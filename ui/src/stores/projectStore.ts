/**
 * Project Store
 *
 * Domain store for project lifecycle operations: history management,
 * serialization, server persistence, autosave, and asset management.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import { toRaw } from "vue";
import { validateProjectExpressions } from "@/services/expressions/expressionValidator";
import {
  CURRENT_SCHEMA_VERSION,
  migrateProject,
  needsMigration,
} from "@/services/projectMigration";
import {
  deleteProject,
  listProjects,
  loadProject,
  saveProject,
} from "@/services/projectStorage";
import { validateURL } from "@/services/security/urlValidator";
import type { AssetReference, Composition, LatticeProject, Layer } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { safeJsonParse } from "@/utils/schemaValidation";
import { validateProjectStructure } from "@/utils/security";
import { useAnimationStore } from "./animationStore";

// ============================================================================
// CONSTANTS
// ============================================================================

const MAX_HISTORY_SIZE = 50;
const MAX_PROJECT_SIZE = 100 * 1024 * 1024;
const MAX_PROJECT_DEPTH = 50;
const MAX_ARRAY_LENGTH = 50000;

// ============================================================================
// STORE INTERFACES
// ============================================================================

export interface ProjectStateAccess {
  project: {
    compositions: Record<string, Composition>;
    composition: {
      width: number;
      height: number;
      frameCount: number;
      duration: number;
      fps: number;
    };
    assets: Record<string, AssetReference>;
    meta: { modified: string };
  };
  activeCompositionId: string;
  openCompositionIds: string[];
  compositionBreadcrumbs: string[];
  selectedAssetId: string | null;
  comfyuiNodeId: string | null;
  sourceImage: string | null;
  depthMap: string | null;
  lastSaveProjectId: string | null;
  lastSaveTime: number;
  hasUnsavedChanges: boolean;
}

export interface ProjectStoreAccess extends ProjectStateAccess {
  getActiveComp(): Composition | null;
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
}

export interface ProjectStore {
  project: LatticeProject;
  historyStack: LatticeProject[];
  historyIndex: number;
  lastSaveProjectId: string | null;
  lastSaveTime: number;
  hasUnsavedChanges: boolean;
  autosaveEnabled?: boolean;
  autosaveIntervalMs?: number;
  autosaveTimerId?: number | null;
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

export function getOpenCompositions(compositorStore: ProjectStoreAccess): Composition[] {
  return compositorStore.openCompositionIds
    .map((id: string) => compositorStore.project.compositions[id])
    .filter(Boolean) as Composition[];
}

export function getBreadcrumbPath(compositorStore: ProjectStoreAccess): Array<{ id: string; name: string }> {
  return compositorStore.compositionBreadcrumbs
    .map((id: string) => {
      const comp = compositorStore.project.compositions[id];
      return comp ? { id, name: comp.name } : null;
    })
    .filter(Boolean) as Array<{ id: string; name: string }>;
}

export function hasProject(compositorStore: ProjectStateAccess): boolean {
  return compositorStore.sourceImage !== null;
}

export function getWidth(compositorStore: ProjectStoreAccess): number {
  return compositorStore.getActiveComp()?.settings.width || 1024;
}

export function getHeight(compositorStore: ProjectStoreAccess): number {
  return compositorStore.getActiveComp()?.settings.height || 1024;
}

export function getFrameCount(compositorStore: ProjectStoreAccess): number {
  return compositorStore.getActiveComp()?.settings.frameCount || 81;
}

export function getFps(compositorStore: ProjectStoreAccess): number {
  return compositorStore.getActiveComp()?.settings.fps || 16;
}

export function getDuration(compositorStore: ProjectStoreAccess): number {
  return compositorStore.getActiveComp()?.settings.duration || 5;
}

export function getBackgroundColor(compositorStore: ProjectStoreAccess): string {
  return compositorStore.getActiveComp()?.settings.backgroundColor || "#050505";
}

export function getCurrentTime(compositorStore: ProjectStoreAccess): number {
  const comp = compositorStore.getActiveComp();
  return comp ? comp.currentFrame / comp.settings.fps : 0;
}

export function selectAsset(compositorStore: ProjectStoreAccess, assetId: string | null): void {
  compositorStore.selectedAssetId = assetId;
}

export function loadInputs(
  compositorStore: ProjectStoreAccess,
  inputs: {
    node_id: string;
    source_image: string;
    depth_map: string;
    width: number;
    height: number;
    frame_count: number;
  },
): void {
  compositorStore.comfyuiNodeId = inputs.node_id;
  compositorStore.sourceImage = inputs.source_image;
  compositorStore.depthMap = inputs.depth_map;

  const comp = compositorStore.getActiveComp();
  if (!comp) return;

  const oldFrameCount = comp.settings.frameCount;

  comp.settings.width = inputs.width;
  comp.settings.height = inputs.height;
  comp.settings.frameCount = inputs.frame_count;
  comp.settings.duration = inputs.frame_count / comp.settings.fps;

  compositorStore.project.composition.width = inputs.width;
  compositorStore.project.composition.height = inputs.height;
  compositorStore.project.composition.frameCount = inputs.frame_count;
  compositorStore.project.composition.duration = inputs.frame_count / compositorStore.project.composition.fps;

  if (inputs.frame_count > oldFrameCount) {
    for (const layer of comp.layers) {
      if (layer.outPoint === oldFrameCount - 1) {
        layer.outPoint = inputs.frame_count - 1;
      }
    }
  }

  if (inputs.source_image) {
    compositorStore.project.assets.source_image = {
      id: "source_image",
      type: "image",
      source: "comfyui_node",
      nodeId: inputs.node_id,
      width: inputs.width,
      height: inputs.height,
      data: inputs.source_image,
    };
  }

  if (inputs.depth_map) {
    compositorStore.project.assets.depth_map = {
      id: "depth_map",
      type: "depth_map",
      source: "comfyui_node",
      nodeId: inputs.node_id,
      width: inputs.width,
      height: inputs.height,
      data: inputs.depth_map,
    };
  }

  if (comp) comp.currentFrame = 0;
  compositorStore.project.meta.modified = new Date().toISOString();
}

// ============================================================================
// PARTICLE CACHE INVALIDATION
// ============================================================================

function invalidateParticleCaches(): void {
  const engine = (window as unknown as {
    __latticeEngine?: { getLayers?: () => Array<{ clearCache?: () => void }> };
  }).__latticeEngine;
  if (!engine) return;

  try {
    const layers = engine.getLayers?.() || [];
    for (const layer of layers) {
      if (layer && typeof layer.clearCache === "function") {
        layer.clearCache();
      }
    }
  } catch {
    // Silently fail if engine not initialized
  }
}

// ============================================================================
// ASSET HELPERS
// ============================================================================

export function findUsedAssetIds(store: ProjectStore): Set<string> {
  const usedIds = new Set<string>();

  for (const comp of Object.values(store.project.compositions)) {
    for (const layer of comp.layers) {
      if (layer.data && typeof layer.data === "object") {
        const data = layer.data as unknown as Record<string, unknown>;

        if (data.assetId && typeof data.assetId === "string") usedIds.add(data.assetId);
        if (data.sourceAssetId && typeof data.sourceAssetId === "string") usedIds.add(data.sourceAssetId);

        if (data.materials && Array.isArray(data.materials)) {
          for (const mat of data.materials as Array<Record<string, unknown>>) {
            if (mat.textureId && typeof mat.textureId === "string") usedIds.add(mat.textureId);
            if (mat.normalMapId && typeof mat.normalMapId === "string") usedIds.add(mat.normalMapId);
            if (mat.roughnessMapId && typeof mat.roughnessMapId === "string") usedIds.add(mat.roughnessMapId);
          }
        }

        if (data.spriteSheetAssetId && typeof data.spriteSheetAssetId === "string") usedIds.add(data.spriteSheetAssetId);
        if (data.environmentMapId && typeof data.environmentMapId === "string") usedIds.add(data.environmentMapId);
      }
    }
  }

  return usedIds;
}

function getExtensionForAsset(asset: { filename?: string; type?: string }): string {
  if (asset.filename) {
    const ext = asset.filename.split(".").pop();
    if (ext) return ext;
  }
  switch (asset.type) {
    case "image": return "png";
    case "video": return "mp4";
    case "audio": return "mp3";
    case "model": return "glb";
    case "pointcloud": return "ply";
    default: return "bin";
  }
}

// ============================================================================
// DEFAULT PROJECT
// ============================================================================

export function createDefaultProject(): LatticeProject {
  const mainCompId = "comp_main";
  return {
    version: "1.0.0",
    schemaVersion: CURRENT_SCHEMA_VERSION,
    meta: {
      name: "Untitled Project",
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
      author: "",
    },
    composition: {
      width: 1920, height: 1080, frameCount: 81, fps: 16,
      duration: 5.0625, backgroundColor: "#1a1a1a",
      autoResizeToContent: false, frameBlendingEnabled: false,
    },
    compositions: {
      [mainCompId]: {
        id: mainCompId, name: "Main Comp",
        settings: {
          width: 1920, height: 1080, frameCount: 81, fps: 16,
          duration: 5.0625, backgroundColor: "#1a1a1a",
          autoResizeToContent: false, frameBlendingEnabled: false,
        },
        layers: [], currentFrame: 0, isNestedComp: false,
      },
    },
    mainCompositionId: mainCompId,
    layers: [],
    currentFrame: 0,
    assets: {},
  };
}

// ============================================================================
// STORE DEFINITION
// ============================================================================

export const useProjectStore = defineStore("project", {
  state: () => ({}),

  actions: {
    // ========================================================================
    // GETTERS (delegated from compositorStore)
    // ========================================================================

    getOpenCompositions(compositorStore: ProjectStoreAccess): Composition[] {
      return getOpenCompositions(compositorStore);
    },

    getBreadcrumbPath(compositorStore: ProjectStoreAccess): Array<{ id: string; name: string }> {
      return getBreadcrumbPath(compositorStore);
    },

    hasProject(compositorStore: ProjectStateAccess): boolean {
      return hasProject(compositorStore);
    },

    getWidth(compositorStore: ProjectStoreAccess): number {
      return getWidth(compositorStore);
    },

    getHeight(compositorStore: ProjectStoreAccess): number {
      return getHeight(compositorStore);
    },

    getFrameCount(compositorStore: ProjectStoreAccess): number {
      return getFrameCount(compositorStore);
    },

    getFps(compositorStore: ProjectStoreAccess): number {
      return getFps(compositorStore);
    },

    getDuration(compositorStore: ProjectStoreAccess): number {
      return getDuration(compositorStore);
    },

    getBackgroundColor(compositorStore: ProjectStoreAccess): string {
      return getBackgroundColor(compositorStore);
    },

    getCurrentTime(compositorStore: ProjectStoreAccess): number {
      return getCurrentTime(compositorStore);
    },

    selectAsset(compositorStore: ProjectStoreAccess, assetId: string | null): void {
      selectAsset(compositorStore, assetId);
    },

    loadInputs(compositorStore: ProjectStoreAccess, inputs: Parameters<typeof loadInputs>[1]): void {
      loadInputs(compositorStore, inputs);
    },

    // ========================================================================
    // HISTORY MANAGEMENT
    // ========================================================================

    pushHistory(store: ProjectStore): void {
      if (store.historyIndex < store.historyStack.length - 1) {
        store.historyStack = store.historyStack.slice(0, store.historyIndex + 1);
      }
      const snapshot = structuredClone(toRaw(store.project)) as typeof store.project;
      store.historyStack.push(snapshot);
      store.historyIndex = store.historyStack.length - 1;
      if (store.historyStack.length > MAX_HISTORY_SIZE) {
        store.historyStack = store.historyStack.slice(-MAX_HISTORY_SIZE);
        store.historyIndex = store.historyStack.length - 1;
      }
    },

    undo(store: ProjectStore): boolean {
      if (store.historyIndex <= 0) return false;
      store.historyIndex--;
      const historyEntry = toRaw(store.historyStack[store.historyIndex]);
      store.project = structuredClone(historyEntry) as LatticeProject;
      invalidateParticleCaches();
      return true;
    },

    redo(store: ProjectStore): boolean {
      if (store.historyIndex >= store.historyStack.length - 1) return false;
      store.historyIndex++;
      const historyEntry = toRaw(store.historyStack[store.historyIndex]);
      store.project = structuredClone(historyEntry) as LatticeProject;
      invalidateParticleCaches();
      return true;
    },

    canUndo(store: ProjectStore): boolean {
      return store.historyIndex > 0;
    },

    canRedo(store: ProjectStore): boolean {
      return store.historyIndex < store.historyStack.length - 1;
    },

    clearHistory(store: ProjectStore): void {
      const snapshot = structuredClone(toRaw(store.project)) as typeof store.project;
      store.historyStack = [snapshot];
      store.historyIndex = 0;
    },

    // ========================================================================
    // PROJECT INITIALIZATION
    // ========================================================================

    newProject(store: ProjectStore): void {
      store.project = createDefaultProject();
      store.lastSaveProjectId = null;
      store.lastSaveTime = 0;
      store.hasUnsavedChanges = false;
      this.clearHistory(store);
      storeLogger.info("Project reset to default state");
    },

    /**
     * Save project (convenience wrapper for performAutosave).
     */
    async saveProject(store: ProjectStore): Promise<void> {
      await this.performAutosave(store);
    },

    /**
     * Save project as (to server with new ID).
     */
    async saveProjectAs(store: ProjectStore): Promise<string | null> {
      return await this.saveProjectToServer(store, undefined);
    },

    // ========================================================================
    // SERIALIZATION
    // ========================================================================

    exportProject(store: ProjectStore): string {
      const project = { ...store.project };
      const animationStore = useAnimationStore();
      if (animationStore.snapConfig) {
        (project as Record<string, unknown>).snapConfig = animationStore.snapConfig;
      }
      return JSON.stringify(project, null, 2);
    },

    importProject(store: ProjectStore, json: string, pushHistoryFn: () => void): boolean {
      try {
        const parseResult = safeJsonParse<LatticeProject>(json, undefined, {
          maxSize: MAX_PROJECT_SIZE,
          maxDepth: MAX_PROJECT_DEPTH,
          maxArrayLength: MAX_ARRAY_LENGTH,
          context: "Project import",
        });

        if (!parseResult.success) {
          storeLogger.error(`[SECURITY] Project parse failed (${parseResult.code}):`, parseResult.error.message);
          return false;
        }

        let project = parseResult.data;

        if (needsMigration(project)) {
          const oldVersion = (project as unknown as { schemaVersion?: number }).schemaVersion ?? 1;
          storeLogger.info(`Migrating project from schema v${oldVersion} to v${CURRENT_SCHEMA_VERSION}`);
          const migrationResult = migrateProject(project);
          if (migrationResult.success && migrationResult.project) {
            project = migrationResult.project as LatticeProject;
          } else {
            storeLogger.error("Project migration failed:", migrationResult.error);
            return false;
          }
        }

        try {
          validateProjectStructure(project, "Imported project");
        } catch (validationError) {
          storeLogger.error("Project structure validation failed:", validationError);
          return false;
        }

        const projectWithSnap = project as unknown as Record<string, unknown>;
        const animationStore = useAnimationStore();
        if (projectWithSnap.snapConfig) {
          try {
            animationStore.setSnapConfig(projectWithSnap.snapConfig as Partial<typeof animationStore.snapConfig>);
          } catch {
            // Continue with default snapConfig
          }
        }

        const { snapConfig: _, ...projectWithoutSnapConfig } = projectWithSnap;
        store.project = projectWithoutSnapConfig as unknown as LatticeProject;
        pushHistoryFn();
        return true;
      } catch (err) {
        storeLogger.error("Failed to import project:", err);
        return false;
      }
    },

    async loadProjectFromFile(store: ProjectStore, file: File, pushHistoryFn: () => void): Promise<boolean> {
      try {
        const json = await file.text();

        try {
          const parseResult = safeJsonParse<LatticeProject>(json, undefined, {
            maxSize: MAX_PROJECT_SIZE,
            maxDepth: MAX_PROJECT_DEPTH,
            maxArrayLength: MAX_ARRAY_LENGTH,
            context: "Project file validation",
          });

          if (!parseResult.success) {
            storeLogger.error(`[SECURITY] Project file parse failed (${parseResult.code}):`, parseResult.error.message);
            return false;
          }

          const project = parseResult.data;
          const validation = await validateProjectExpressions(project);

          if (!validation.valid) {
            const dangerList = validation.dangerous.map((d) => `  - ${d.location}: ${d.reason}`).join("\n");
            storeLogger.error(`[SECURITY] Project contains ${validation.dangerous.length} dangerous expression(s):\n${dangerList}`);
            return false;
          }
        } catch {
          // JSON parse error will be caught by importProject
        }

        const success = this.importProject(store, json, pushHistoryFn);
        if (success) storeLogger.info("Loaded project from file:", file.name);
        return success;
      } catch (err) {
        storeLogger.error("Failed to load project from file:", err);
        return false;
      }
    },

    // ========================================================================
    // SERVER OPERATIONS
    // ========================================================================

    async saveProjectToServer(store: ProjectStore, projectId?: string): Promise<string | null> {
      try {
        const result = await saveProject(store.project, projectId);
        if (result.status === "success" && result.project_id) {
          store.lastSaveProjectId = result.project_id;
          store.lastSaveTime = Date.now();
          store.hasUnsavedChanges = false;
          storeLogger.info("Project saved to server:", result.project_id);
          return result.project_id;
        } else {
          storeLogger.error("Failed to save project:", result.message);
          return null;
        }
      } catch (err) {
        storeLogger.error("Error saving project to server:", err);
        return null;
      }
    },

    async loadProjectFromServer(store: ProjectStore, projectId: string, pushHistoryFn: () => void): Promise<boolean> {
      try {
        const result = await loadProject(projectId);

        if (result.status === "success" && result.project) {
          let project = result.project;

          if (needsMigration(project)) {
            const oldVersion = (project as unknown as { schemaVersion?: number }).schemaVersion ?? 1;
            storeLogger.info(`Migrating project from schema v${oldVersion} to v${CURRENT_SCHEMA_VERSION}`);
            const migrationResult = migrateProject(project);
            if (migrationResult.success && migrationResult.project) {
              project = migrationResult.project as LatticeProject;
            } else {
              storeLogger.error("Project migration failed:", migrationResult.error);
              return false;
            }
          }

          try {
            validateProjectStructure(project, `Server project '${projectId}'`);
          } catch (validationError) {
            storeLogger.error("Project structure validation failed:", validationError);
            return false;
          }

          const validation = await validateProjectExpressions(project);
          if (!validation.valid) {
            const dangerList = validation.dangerous.map((d) => `  - ${d.location}: ${d.reason}`).join("\n");
            storeLogger.error(`[SECURITY] Project contains ${validation.dangerous.length} dangerous expression(s):\n${dangerList}`);
            return false;
          }

          store.project = project;
          pushHistoryFn();
          store.lastSaveProjectId = projectId;
          store.lastSaveTime = Date.now();
          store.hasUnsavedChanges = false;
          storeLogger.info("Project loaded from server:", projectId);
          return true;
        } else {
          storeLogger.error("Failed to load project:", result.message);
          return false;
        }
      } catch (err) {
        storeLogger.error("Error loading project from server:", err);
        return false;
      }
    },

    async listServerProjects(): Promise<Array<{ id: string; name: string; modified?: string }>> {
      try {
        const result = await listProjects();
        return result.status === "success" && result.projects ? result.projects : [];
      } catch (err) {
        storeLogger.error("Error listing projects:", err);
        return [];
      }
    },

    async deleteServerProject(projectId: string): Promise<boolean> {
      try {
        const result = await deleteProject(projectId);
        return result.status === "success";
      } catch (err) {
        storeLogger.error("Error deleting project:", err);
        return false;
      }
    },

    // ========================================================================
    // AUTOSAVE
    // ========================================================================

    startAutosave(store: ProjectStore, performAutosaveFn: () => Promise<void>): void {
      if (store.autosaveTimerId !== null || !store.autosaveEnabled) return;
      store.autosaveTimerId = window.setInterval(performAutosaveFn, store.autosaveIntervalMs);
      storeLogger.info("Autosave started with interval:", store.autosaveIntervalMs);
    },

    stopAutosave(store: ProjectStore): void {
      if (store.autosaveTimerId !== null && store.autosaveTimerId !== undefined) {
        window.clearInterval(store.autosaveTimerId);
        store.autosaveTimerId = null;
        storeLogger.info("Autosave stopped");
      }
    },

    configureAutosave(
      store: ProjectStore,
      options: { enabled?: boolean; intervalMs?: number },
      performAutosaveFn: () => Promise<void>,
    ): void {
      if (options.enabled !== undefined) store.autosaveEnabled = options.enabled;
      if (options.intervalMs !== undefined && Number.isFinite(options.intervalMs) && options.intervalMs > 0) {
        store.autosaveIntervalMs = options.intervalMs;
      }
      this.stopAutosave(store);
      if (store.autosaveEnabled) this.startAutosave(store, performAutosaveFn);
    },

    async performAutosave(store: ProjectStore): Promise<void> {
      if (!store.hasUnsavedChanges) return;

      try {
        const existingProjectId = store.lastSaveProjectId || undefined;
        const result = await saveProject(store.project, existingProjectId);
        if (result.status === "success" && result.project_id) {
          store.lastSaveProjectId = result.project_id;
          store.lastSaveTime = Date.now();
          store.hasUnsavedChanges = false;
          storeLogger.info("Autosaved project:", result.project_id);
        } else {
          storeLogger.error("Autosave failed:", result.message);
        }
      } catch (error) {
        storeLogger.error("Autosave failed:", error);
      }
    },

    markUnsavedChanges(store: ProjectStore): void {
      store.hasUnsavedChanges = true;
    },

    // ========================================================================
    // ASSET MANAGEMENT
    // ========================================================================

    removeUnusedAssets(store: ProjectStore): { removed: number; assetNames: string[] } {
      const usedIds = findUsedAssetIds(store);
      const assets = store.project.assets;
      const removedNames: string[] = [];
      let removedCount = 0;

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
        this.pushHistory(store);
        storeLogger.info(`Removed ${removedCount} unused assets:`, removedNames);
      }

      return { removed: removedCount, assetNames: removedNames };
    },

    getAssetUsageStats(store: ProjectStore): { total: number; used: number; unused: number; unusedNames: string[] } {
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
        unusedNames,
      };
    },

    async collectFiles(store: ProjectStore, options: { includeUnused?: boolean; projectName?: string } = {}): Promise<Blob> {
      const { includeUnused = false, projectName } = options;
      const JSZip = (await import("jszip")).default;
      const zip = new JSZip();

      const folderName = projectName || store.project.meta.name || "lattice-project";
      const folder = zip.folder(folderName);
      if (!folder) throw new Error("Failed to create ZIP folder");

      const usedIds = includeUnused ? undefined : findUsedAssetIds(store);
      const assets = store.project.assets;
      const assetsFolder = folder.folder("assets");
      const assetManifest: Record<string, string> = {};

      for (const [assetId, asset] of Object.entries(assets)) {
        if (usedIds && !usedIds.has(assetId)) continue;

        const filename = asset.filename || `${assetId}.${getExtensionForAsset(asset)}`;
        assetManifest[assetId] = `assets/${filename}`;

        if (asset.data) {
          if (asset.data.startsWith("data:")) {
            const base64Data = asset.data.split(",")[1];
            if (base64Data) assetsFolder?.file(filename, base64Data, { base64: true });
          } else if (asset.data.startsWith("blob:") || asset.data.startsWith("http")) {
            const urlValidation = validateURL(asset.data, "fetch");
            if (!urlValidation.valid) {
              storeLogger.warn(`[SECURITY] Skipped asset ${assetId}: ${urlValidation.error}`);
              continue;
            }
            try {
              const response = await fetch(urlValidation.sanitized || asset.data);
              const blob = await response.blob();
              assetsFolder?.file(filename, blob);
            } catch (e) {
              storeLogger.warn(`Failed to fetch asset ${assetId}:`, e);
            }
          } else {
            assetsFolder?.file(filename, asset.data, { base64: true });
          }
        }
      }

      const exportProject = structuredClone(toRaw(store.project));
      (exportProject.meta as unknown as Record<string, unknown>).exportedAt = new Date().toISOString();
      (exportProject as unknown as Record<string, unknown>)._assetManifest = assetManifest;

      folder.file("project.lattice.json", JSON.stringify(exportProject, null, 2));

      const zipBlob = await zip.generateAsync({
        type: "blob",
        compression: "DEFLATE",
        compressionOptions: { level: 6 },
      });

      storeLogger.info(`Collected files: ${Object.keys(assetManifest).length} assets, project JSON`);
      return zipBlob;
    },

    async downloadCollectedFiles(store: ProjectStore, options: { includeUnused?: boolean } = {}): Promise<void> {
      const projectName = store.project.meta.name || "lattice-project";
      const zipBlob = await this.collectFiles(store, { ...options, projectName });

      const url = URL.createObjectURL(zipBlob);
      const a = document.createElement("a");
      a.href = url;
      a.download = `${projectName}.zip`;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      URL.revokeObjectURL(url);

      storeLogger.info(`Downloaded collected files: ${projectName}.zip`);
    },
  },
});
