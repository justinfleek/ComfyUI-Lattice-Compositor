/**
 * Project Actions
 *
 * Project lifecycle operations: history management, serialization,
 * server persistence, and autosave functionality.
 */

import { storeLogger } from '@/utils/logger';
import type { WeylProject } from '@/types/project';
import { saveProject, loadProject, listProjects, deleteProject } from '@/services/projectStorage';

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

  // Deep clone the project (structuredClone is 10-50x faster than JSON.parse/stringify)
  let snapshot: typeof store.project;
  try {
    snapshot = structuredClone(store.project);
  } catch {
    // Fall back to JSON for proxy objects (e.g., in tests)
    snapshot = JSON.parse(JSON.stringify(store.project));
  }
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
  try {
    store.project = structuredClone(store.historyStack[store.historyIndex]);
  } catch {
    store.project = JSON.parse(JSON.stringify(store.historyStack[store.historyIndex]));
  }
  return true;
}

/**
 * Redo - go forward one step in history
 */
export function redo(store: ProjectStore): boolean {
  if (store.historyIndex >= store.historyStack.length - 1) return false;

  store.historyIndex++;
  try {
    store.project = structuredClone(store.historyStack[store.historyIndex]);
  } catch {
    store.project = JSON.parse(JSON.stringify(store.historyStack[store.historyIndex]));
  }
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
  let snapshot: typeof store.project;
  try {
    snapshot = structuredClone(store.project);
  } catch {
    snapshot = JSON.parse(JSON.stringify(store.project));
  }
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
 */
export function importProject(
  store: ProjectStore,
  json: string,
  pushHistoryFn: () => void
): boolean {
  try {
    const project = JSON.parse(json) as WeylProject;
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
 */
export async function loadProjectFromServer(
  store: ProjectStore,
  projectId: string,
  pushHistoryFn: () => void
): Promise<boolean> {
  try {
    const result = await loadProject(projectId);

    if (result.status === 'success' && result.project) {
      store.project = result.project;
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
        isPrecomp: false
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
