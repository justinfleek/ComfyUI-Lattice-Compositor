/**
 * Project Actions
 *
 * Project lifecycle operations: history management, serialization,
 * server persistence, and autosave functionality.
 */

import { toRaw } from 'vue';
import { storeLogger } from '@/utils/logger';
import type { WeylProject } from '@/types/project';
import { saveProject, loadProject, listProjects, deleteProject } from '@/services/projectStorage';
import { migrateProject, needsMigration, CURRENT_SCHEMA_VERSION } from '@/services/projectMigration';

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface ProjectStore {
  project: WeylProject;
  historyStack: WeylProject[];
  historyIndex: number;
  lastSaveProjectId: string | null;
  lastSaveTime: number | null;
  hasUnsavedChanges: boolean;
  autosaveEnabled?: boolean;
  autosaveIntervalMs?: number;
  autosaveTimerId?: number | null;
}

// ============================================================================
// HISTORY MANAGEMENT
// ============================================================================

const MAX_HISTORY_SIZE = 50;

/**
 * Push current project state to history stack
 */
export function pushHistory(store: ProjectStore): void {
  // Remove any future history if we're not at the end
  if (store.historyIndex < store.historyStack.length - 1) {
    store.historyStack = store.historyStack.slice(0, store.historyIndex + 1);
  }

  // Deep clone the project using toRaw to deproxy reactive objects
  const snapshot = structuredClone(toRaw(store.project)) as typeof store.project;
  store.historyStack.push(snapshot);
  store.historyIndex = store.historyStack.length - 1;

  // Limit history size
  if (store.historyStack.length > MAX_HISTORY_SIZE) {
    store.historyStack = store.historyStack.slice(-MAX_HISTORY_SIZE);
    store.historyIndex = store.historyStack.length - 1;
  }
}

/**
 * Undo - go back one step in history
 */
export function undo(store: ProjectStore): boolean {
  if (store.historyIndex <= 0) return false;

  store.historyIndex--;
  // Use toRaw to deproxy Pinia's reactive wrapper before cloning
  const historyEntry = toRaw(store.historyStack[store.historyIndex]);
  store.project = structuredClone(historyEntry) as WeylProject;
  return true;
}

/**
 * Redo - go forward one step in history
 */
export function redo(store: ProjectStore): boolean {
  if (store.historyIndex >= store.historyStack.length - 1) return false;

  store.historyIndex++;
  // Use toRaw to deproxy Pinia's reactive wrapper before cloning
  const historyEntry = toRaw(store.historyStack[store.historyIndex]);
  store.project = structuredClone(historyEntry) as WeylProject;
  return true;
}

/**
 * Check if undo is available
 */
export function canUndo(store: ProjectStore): boolean {
  return store.historyIndex > 0;
}

/**
 * Check if redo is available
 */
export function canRedo(store: ProjectStore): boolean {
  return store.historyIndex < store.historyStack.length - 1;
}

/**
 * Clear history stack
 */
export function clearHistory(store: ProjectStore): void {
  // Use toRaw to deproxy reactive objects before cloning
  const snapshot = structuredClone(toRaw(store.project)) as typeof store.project;
  store.historyStack = [snapshot];
  store.historyIndex = 0;
}

// ============================================================================
// PROJECT SERIALIZATION
// ============================================================================

/**
 * Export project to JSON string
 */
export function exportProject(store: ProjectStore): string {
  return JSON.stringify(store.project, null, 2);
}

/**
 * Import project from JSON string
 * Automatically migrates older project schemas to current version
 */
export function importProject(
  store: ProjectStore,
  json: string,
  pushHistoryFn: () => void
): boolean {
  try {
    let project = JSON.parse(json) as WeylProject;

    // Check if migration is needed and apply it
    if (needsMigration(project)) {
      const oldVersion = (project as any).schemaVersion ?? 1;
      storeLogger.info(`Migrating project from schema v${oldVersion} to v${CURRENT_SCHEMA_VERSION}`);
      project = migrateProject(project);
      storeLogger.info('Project migration completed successfully');
    }

    store.project = project;
    pushHistoryFn();
    return true;
  } catch (err) {
    storeLogger.error('Failed to import project:', err);
    return false;
  }
}

// ============================================================================
// SERVER OPERATIONS
// ============================================================================

/**
 * Save project to server (ComfyUI backend)
 * @returns The project ID if successful, null otherwise
 */
export async function saveProjectToServer(
  store: ProjectStore,
  projectId?: string
): Promise<string | null> {
  try {
    const result = await saveProject(store.project, projectId);

    if (result.status === 'success' && result.project_id) {
      store.lastSaveProjectId = result.project_id;
      store.lastSaveTime = Date.now();
      store.hasUnsavedChanges = false;
      storeLogger.info('Project saved to server:', result.project_id);
      return result.project_id;
    } else {
      storeLogger.error('Failed to save project:', result.message);
      return null;
    }
  } catch (err) {
    storeLogger.error('Error saving project to server:', err);
    return null;
  }
}

/**
 * Load project from server (ComfyUI backend)
 * Automatically migrates older project schemas to current version
 */
export async function loadProjectFromServer(
  store: ProjectStore,
  projectId: string,
  pushHistoryFn: () => void
): Promise<boolean> {
  try {
    const result = await loadProject(projectId);

    if (result.status === 'success' && result.project) {
      let project = result.project;

      // Check if migration is needed and apply it
      if (needsMigration(project)) {
        const oldVersion = (project as any).schemaVersion ?? 1;
        storeLogger.info(`Migrating project from schema v${oldVersion} to v${CURRENT_SCHEMA_VERSION}`);
        project = migrateProject(project);
        storeLogger.info('Project migration completed successfully');
      }

      store.project = project;
      pushHistoryFn();
      store.lastSaveProjectId = projectId;
      store.lastSaveTime = Date.now();
      store.hasUnsavedChanges = false;
      storeLogger.info('Project loaded from server:', projectId);
      return true;
    } else {
      storeLogger.error('Failed to load project:', result.message);
      return false;
    }
  } catch (err) {
    storeLogger.error('Error loading project from server:', err);
    return false;
  }
}

/**
 * List all projects saved on server
 */
export async function listServerProjects(): Promise<Array<{ id: string; name: string; modified?: string }>> {
  try {
    const result = await listProjects();

    if (result.status === 'success' && result.projects) {
      return result.projects;
    }
    return [];
  } catch (err) {
    storeLogger.error('Error listing projects:', err);
    return [];
  }
}

/**
 * Delete a project from server
 */
export async function deleteServerProject(projectId: string): Promise<boolean> {
  try {
    const result = await deleteProject(projectId);
    return result.status === 'success';
  } catch (err) {
    storeLogger.error('Error deleting project:', err);
    return false;
  }
}

// ============================================================================
// AUTOSAVE MANAGEMENT
// ============================================================================

/**
 * Start autosave timer
 */
export function startAutosave(
  store: ProjectStore,
  performAutosaveFn: () => Promise<void>
): void {
  // Don't start if already running or disabled
  if (store.autosaveTimerId !== null || !store.autosaveEnabled) {
    return;
  }

  store.autosaveTimerId = window.setInterval(
    performAutosaveFn,
    store.autosaveIntervalMs
  );
  storeLogger.info('Autosave started with interval:', store.autosaveIntervalMs);
}

/**
 * Stop autosave timer
 */
export function stopAutosave(store: ProjectStore): void {
  if (store.autosaveTimerId !== null && store.autosaveTimerId !== undefined) {
    window.clearInterval(store.autosaveTimerId);
    store.autosaveTimerId = null;
    storeLogger.info('Autosave stopped');
  }
}

/**
 * Configure autosave settings
 */
export function configureAutosave(
  store: ProjectStore,
  options: { enabled?: boolean; intervalMs?: number },
  performAutosaveFn: () => Promise<void>
): void {
  if (options.enabled !== undefined) {
    store.autosaveEnabled = options.enabled;
  }
  if (options.intervalMs !== undefined) {
    store.autosaveIntervalMs = options.intervalMs;
  }

  // Restart autosave with new settings
  stopAutosave(store);
  if (store.autosaveEnabled) {
    startAutosave(store, performAutosaveFn);
  }
}

/**
 * Perform an autosave
 */
export async function performAutosave(store: ProjectStore): Promise<void> {
  if (!store.hasUnsavedChanges) return;

  try {
    const existingProjectId = store.lastSaveProjectId || undefined;
    const result = await saveProject(store.project, existingProjectId);

    if (result.status === 'success' && result.project_id) {
      store.lastSaveProjectId = result.project_id;
      store.lastSaveTime = Date.now();
      store.hasUnsavedChanges = false;
      storeLogger.info('Autosaved project:', result.project_id);
    } else {
      storeLogger.error('Autosave failed:', result.message);
    }
  } catch (error) {
    storeLogger.error('Autosave failed:', error);
  }
}

/**
 * Mark the project as having unsaved changes
 */
export function markUnsavedChanges(store: ProjectStore): void {
  store.hasUnsavedChanges = true;
}

// ============================================================================
// PROJECT INITIALIZATION
// ============================================================================

/**
 * Create a default new project structure
 */
export function createDefaultProject(): WeylProject {
  const mainCompId = 'comp_main';

  return {
    version: '1.0.0',
    schemaVersion: CURRENT_SCHEMA_VERSION,
    meta: {
      name: 'Untitled Project',
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
      author: ''
    },
    // Legacy single-comp alias
    composition: {
      width: 1920,
      height: 1080,
      frameCount: 81,
      fps: 16,
      duration: 5.0625, // 81 frames at 16fps
      backgroundColor: '#1a1a1a',
      autoResizeToContent: false
    },
    // Multi-composition support
    compositions: {
      [mainCompId]: {
        id: mainCompId,
        name: 'Main Comp',
        settings: {
          width: 1920,
          height: 1080,
          frameCount: 81,
          fps: 16,
          duration: 5.0625,
          backgroundColor: '#1a1a1a',
          autoResizeToContent: false
        },
        layers: [],
        currentFrame: 0,
        isNestedComp: false
      }
    },
    mainCompositionId: mainCompId,
    layers: [], // Legacy
    currentFrame: 0,
    assets: {}
  };
}

/**
 * Reset project to default state
 */
export function resetProject(store: ProjectStore): void {
  store.project = createDefaultProject();
  store.lastSaveProjectId = null;
  store.lastSaveTime = 0;
  store.hasUnsavedChanges = false;
  clearHistory(store);
  storeLogger.info('Project reset to default state');
}

// ============================================================================
// ASSET MANAGEMENT
// ============================================================================

/**
 * Find all asset IDs that are actually used by layers in all compositions
 */
export function findUsedAssetIds(store: ProjectStore): Set<string> {
  const usedIds = new Set<string>();

  // Iterate through all compositions
  for (const comp of Object.values(store.project.compositions)) {
    for (const layer of comp.layers) {
      // Check layer data for asset references
      if (layer.data && typeof layer.data === 'object') {
        const data = layer.data as Record<string, any>;

        // Common asset ID field
        if (data.assetId && typeof data.assetId === 'string') {
          usedIds.add(data.assetId);
        }

        // Source asset ID (for derived assets)
        if (data.sourceAssetId && typeof data.sourceAssetId === 'string') {
          usedIds.add(data.sourceAssetId);
        }

        // Model layer with material references
        if (data.materials && Array.isArray(data.materials)) {
          for (const mat of data.materials) {
            if (mat.textureId) usedIds.add(mat.textureId);
            if (mat.normalMapId) usedIds.add(mat.normalMapId);
            if (mat.roughnessMapId) usedIds.add(mat.roughnessMapId);
          }
        }

        // Particle sprite sheet
        if (data.spriteSheetAssetId) {
          usedIds.add(data.spriteSheetAssetId);
        }

        // Environment map
        if (data.environmentMapId) {
          usedIds.add(data.environmentMapId);
        }
      }
    }
  }

  return usedIds;
}

/**
 * Remove unused assets from the project (Reduce Project)
 * Returns the number of assets removed
 */
export function removeUnusedAssets(store: ProjectStore): { removed: number; assetNames: string[] } {
  const usedIds = findUsedAssetIds(store);
  const assets = store.project.assets;
  const removedNames: string[] = [];
  let removedCount = 0;

  // Find and remove unused assets
  for (const assetId of Object.keys(assets)) {
    if (!usedIds.has(assetId)) {
      const asset = assets[assetId];
      removedNames.push(asset.filename || assetId);
      delete assets[assetId];
      removedCount++;
    }
  }

  if (removedCount > 0) {
    store.project.meta.modified = new Date().toISOString();
    pushHistory(store);
    storeLogger.info(`Removed ${removedCount} unused assets:`, removedNames);
  }

  return { removed: removedCount, assetNames: removedNames };
}

/**
 * Get statistics about asset usage
 */
export function getAssetUsageStats(store: ProjectStore): {
  total: number;
  used: number;
  unused: number;
  unusedNames: string[];
} {
  const usedIds = findUsedAssetIds(store);
  const assets = store.project.assets;
  const unusedNames: string[] = [];

  for (const assetId of Object.keys(assets)) {
    if (!usedIds.has(assetId)) {
      unusedNames.push(assets[assetId].filename || assetId);
    }
  }

  return {
    total: Object.keys(assets).length,
    used: usedIds.size,
    unused: unusedNames.length,
    unusedNames
  };
}

/**
 * Collect Files - Package project and all used assets into a ZIP
 */
export async function collectFiles(
  store: ProjectStore,
  options: {
    includeUnused?: boolean;
    projectName?: string;
  } = {}
): Promise<Blob> {
  const { includeUnused = false, projectName } = options;

  // Dynamically import JSZip
  const JSZip = (await import('jszip')).default;
  const zip = new JSZip();

  // Create project folder
  const folderName = projectName || store.project.meta.name || 'weyl-project';
  const folder = zip.folder(folderName);
  if (!folder) throw new Error('Failed to create ZIP folder');

  // Get assets to include
  const usedIds = includeUnused ? null : findUsedAssetIds(store);
  const assets = store.project.assets;
  const assetsFolder = folder.folder('assets');

  // Collect asset files
  const assetManifest: Record<string, string> = {}; // assetId -> relative path

  for (const [assetId, asset] of Object.entries(assets)) {
    // Skip unused assets if not including them
    if (usedIds && !usedIds.has(assetId)) continue;

    const filename = asset.filename || `${assetId}.${getExtensionForAsset(asset)}`;
    assetManifest[assetId] = `assets/${filename}`;

    // Add asset data to ZIP
    if (asset.data) {
      // Asset has inline data (base64 or data URL)
      if (asset.data.startsWith('data:')) {
        // Data URL - extract base64 part
        const base64Data = asset.data.split(',')[1];
        if (base64Data) {
          assetsFolder?.file(filename, base64Data, { base64: true });
        }
      } else if (asset.data.startsWith('blob:') || asset.data.startsWith('http')) {
        // URL - fetch the data
        try {
          const response = await fetch(asset.data);
          const blob = await response.blob();
          assetsFolder?.file(filename, blob);
        } catch (e) {
          storeLogger.warn(`Failed to fetch asset ${assetId}:`, e);
        }
      } else {
        // Assume it's base64
        assetsFolder?.file(filename, asset.data, { base64: true });
      }
    }
  }

  // Create a copy of the project with updated asset paths
  const exportProject = structuredClone(toRaw(store.project));
  (exportProject.meta as any).exportedAt = new Date().toISOString();

  // Add asset manifest to project
  (exportProject as any)._assetManifest = assetManifest;

  // Save project JSON
  folder.file('project.weyl.json', JSON.stringify(exportProject, null, 2));

  // Generate ZIP
  const zipBlob = await zip.generateAsync({
    type: 'blob',
    compression: 'DEFLATE',
    compressionOptions: { level: 6 }
  });

  storeLogger.info(`Collected files: ${Object.keys(assetManifest).length} assets, project JSON`);
  return zipBlob;
}

/**
 * Helper to get file extension for an asset
 */
function getExtensionForAsset(asset: any): string {
  if (asset.filename) {
    const ext = asset.filename.split('.').pop();
    if (ext) return ext;
  }

  switch (asset.type) {
    case 'image': return 'png';
    case 'video': return 'mp4';
    case 'audio': return 'mp3';
    case 'model': return 'glb';
    case 'pointcloud': return 'ply';
    default: return 'bin';
  }
}

/**
 * Trigger Collect Files download
 */
export async function downloadCollectedFiles(
  store: ProjectStore,
  options: { includeUnused?: boolean } = {}
): Promise<void> {
  const projectName = store.project.meta.name || 'weyl-project';
  const zipBlob = await collectFiles(store, { ...options, projectName });

  // Trigger download
  const url = URL.createObjectURL(zipBlob);
  const a = document.createElement('a');
  a.href = url;
  a.download = `${projectName}.zip`;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);

  storeLogger.info(`Downloaded collected files: ${projectName}.zip`);
}
