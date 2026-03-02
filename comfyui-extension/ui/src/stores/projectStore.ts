/**
 * Project Store
 *
 * Domain store for project lifecycle operations: history management,
 * serialization, server persistence, autosave, and asset management.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import { defineStore } from "pinia";
import { toRaw } from "vue";
import { validateProjectExpressions } from "@/services/expressions/expressionValidator";
import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;
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
import type { AssetReference, Composition, LatticeProject, Layer, ProjectMeta } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { safeJsonParse } from "@/utils/schemaValidation";
import { validateProjectStructure } from "@/utils/security";
import { useAnimationStore } from "./animationStore";
import { createEmptyProject } from "@/types/project";

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

export function getOpenCompositions(projectStore: ReturnType<typeof useProjectStore>): Composition[] {
  return projectStore.openCompositionIds
    .map((id: string) => projectStore.project.compositions[id])
    .filter(Boolean) as Composition[];
}

export function getBreadcrumbPath(projectStore: ReturnType<typeof useProjectStore>): Array<{ id: string; name: string }> {
  return projectStore.compositionBreadcrumbs
    .map((id: string) => {
      const comp = projectStore.project.compositions[id];
      return comp ? { id, name: comp.name } : null;
    })
    .filter(Boolean) as Array<{ id: string; name: string }>;
}

export function hasProject(projectStore: ReturnType<typeof useProjectStore>): boolean {
  return projectStore.sourceImage !== null;
}

export function getWidth(projectStore: ReturnType<typeof useProjectStore>): number {
  const comp = projectStore.project.compositions[projectStore.activeCompositionId];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const settings = (comp != null && typeof comp === "object" && "settings" in comp && comp.settings != null && typeof comp.settings === "object") ? comp.settings : undefined;
  const width = (settings != null && typeof settings === "object" && "width" in settings && typeof settings.width === "number") ? settings.width : undefined;
  return width != null ? width : 1024;
}

export function getHeight(projectStore: ReturnType<typeof useProjectStore>): number {
  const comp = projectStore.project.compositions[projectStore.activeCompositionId];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const settings = (comp != null && typeof comp === "object" && "settings" in comp && comp.settings != null && typeof comp.settings === "object") ? comp.settings : undefined;
  const height = (settings != null && typeof settings === "object" && "height" in settings && typeof settings.height === "number") ? settings.height : undefined;
  return height != null ? height : 1024;
}

export function getFrameCount(projectStore: ReturnType<typeof useProjectStore>): number {
  const comp = projectStore.project.compositions[projectStore.activeCompositionId];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const settings = (comp != null && typeof comp === "object" && "settings" in comp && comp.settings != null && typeof comp.settings === "object") ? comp.settings : undefined;
  const frameCount = (settings != null && typeof settings === "object" && "frameCount" in settings && typeof settings.frameCount === "number") ? settings.frameCount : undefined;
  return frameCount != null ? frameCount : 81;
}

export function getFps(projectStore: ReturnType<typeof useProjectStore>): number {
  const comp = projectStore.project.compositions[projectStore.activeCompositionId];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const settings = (comp != null && typeof comp === "object" && "settings" in comp && comp.settings != null && typeof comp.settings === "object") ? comp.settings : undefined;
  const fps = (settings != null && typeof settings === "object" && "fps" in settings && typeof settings.fps === "number") ? settings.fps : undefined;
  return fps != null ? fps : 16;
}

export function getDuration(projectStore: ReturnType<typeof useProjectStore>): number {
  const comp = projectStore.project.compositions[projectStore.activeCompositionId];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const settings = (comp != null && typeof comp === "object" && "settings" in comp && comp.settings != null && typeof comp.settings === "object") ? comp.settings : undefined;
  const duration = (settings != null && typeof settings === "object" && "duration" in settings && typeof settings.duration === "number") ? settings.duration : undefined;
  return duration != null ? duration : 5;
}

export function getBackgroundColor(projectStore: ReturnType<typeof useProjectStore>): string {
  const comp = projectStore.project.compositions[projectStore.activeCompositionId];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const settings = (comp != null && typeof comp === "object" && "settings" in comp && comp.settings != null && typeof comp.settings === "object") ? comp.settings : undefined;
  const backgroundColor = (settings != null && typeof settings === "object" && "backgroundColor" in settings && typeof settings.backgroundColor === "string") ? settings.backgroundColor : undefined;
  return backgroundColor != null ? backgroundColor : "#050505";
}

export function getCurrentTime(projectStore: ReturnType<typeof useProjectStore>): number {
  const comp = projectStore.project.compositions[projectStore.activeCompositionId];
  return comp ? comp.currentFrame / comp.settings.fps : 0;
}

export function selectAsset(projectStore: ReturnType<typeof useProjectStore>, assetId: string | null): void {
  projectStore.selectedAssetId = assetId;
}

export function loadInputs(
  projectStore: ReturnType<typeof useProjectStore>,
  inputs: {
    node_id: string;
    source_image: string;
    depth_map: string;
    width: number;
    height: number;
    frame_count: number;
  },
): void {
  projectStore.comfyuiNodeId = inputs.node_id;
  projectStore.sourceImage = inputs.source_image;
  projectStore.depthMap = inputs.depth_map;

  const comp = projectStore.project.compositions[projectStore.activeCompositionId];
  if (!comp) return;

  const oldFrameCount = comp.settings.frameCount;

  comp.settings.width = inputs.width;
  comp.settings.height = inputs.height;
  comp.settings.frameCount = inputs.frame_count;
  comp.settings.duration = inputs.frame_count / comp.settings.fps;

  projectStore.project.composition.width = inputs.width;
  projectStore.project.composition.height = inputs.height;
  projectStore.project.composition.frameCount = inputs.frame_count;
  projectStore.project.composition.duration = inputs.frame_count / projectStore.project.composition.fps;

  if (inputs.frame_count > oldFrameCount) {
    for (const layer of comp.layers) {
      if (layer.outPoint === oldFrameCount - 1) {
        layer.outPoint = inputs.frame_count - 1;
      }
    }
  }

  if (inputs.source_image) {
    projectStore.project.assets.source_image = {
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
    projectStore.project.assets.depth_map = {
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
  projectStore.project.meta.modified = new Date().toISOString();
}

// ============================================================================
// PARTICLE CACHE INVALIDATION
// ============================================================================

interface LatticeEngineGlobal {
  __latticeEngine?: {
    getLayers?: () => Array<{ clearCache?: () => void }>;
  };
}

function invalidateParticleCaches(): void {
  const engine = (window as LatticeEngineGlobal).__latticeEngine;
  if (!engine) return;

  try {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
    const getLayers = (engine !== null && engine !== undefined && typeof engine === "object" && "getLayers" in engine) ? engine.getLayers : undefined;
    const layersResult = (getLayers !== null && getLayers !== undefined && typeof getLayers === "function") ? getLayers() : undefined;
    const layers = (layersResult !== null && layersResult !== undefined && Array.isArray(layersResult)) ? layersResult : [];
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

  /**
   * Type guard for layer data with assetId
   */
  function hasAssetId(data: RuntimeValue): data is { assetId?: string | null; sourceAssetId?: string | null; spriteSheetAssetId?: string | null; environmentMapId?: string | null; materials?: Array<{ textureId?: string; normalMapId?: string; roughnessMapId?: string }> } {
    return data !== null && typeof data === "object";
  }

  for (const comp of Object.values(store.project.compositions)) {
    for (const layer of comp.layers) {
      if (layer.data && hasAssetId(layer.data)) {
        const data = layer.data;

        if (data.assetId && typeof data.assetId === "string") usedIds.add(data.assetId);
        if (data.sourceAssetId && typeof data.sourceAssetId === "string") usedIds.add(data.sourceAssetId);

        if (data.materials && Array.isArray(data.materials)) {
          for (const mat of data.materials) {
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
  state: () => {
    // Create initial project and pre-populate history with it
    // This ensures undo works for the very first action
    const initialProject = createEmptyProject(1280, 720); // 720p HD default
    return {
      // Project data
      project: initialProject,
      
      // Active composition (for multi-composition support)
      activeCompositionId: "main",
      openCompositionIds: ["main"] as string[], // Tabs - which comps are open
      compositionBreadcrumbs: ["main"] as string[], // Navigation history for nested compositions
      
      // ComfyUI connection
      comfyuiNodeId: null as string | null,
      
      // Input data from ComfyUI
      sourceImage: null as string | null,
      depthMap: null as string | null,
      
      // History for undo/redo
      historyStack: [structuredClone<LatticeProject>(initialProject)] as LatticeProject[],
      historyIndex: 0,
      
      // Autosave state
      autosaveEnabled: true,
      autosaveIntervalMs: 60000,
      autosaveTimerId: null as number | null,
      lastSaveTime: 0, // 0 = never saved, Date.now() = last save time
      lastSaveProjectId: null as string | null,
      hasUnsavedChanges: false,
      
      // Timeline UI state
      selectedAssetId: null as string | null,
    };
  },

  actions: {
    // ========================================================================
    // GETTERS (delegated from compositorStore)
    // ========================================================================

    getOpenCompositions(): Composition[] {
      return getOpenCompositions(this);
    },

    getBreadcrumbPath(): Array<{ id: string; name: string }> {
      return getBreadcrumbPath(this);
    },

    hasProject(): boolean {
      return hasProject(this);
    },

    getWidth(): number {
      return getWidth(this);
    },

    getHeight(): number {
      return getHeight(this);
    },

    getFrameCount(): number {
      return getFrameCount(this);
    },

    getFps(): number {
      return getFps(this);
    },

    getDuration(): number {
      return getDuration(this);
    },

    getBackgroundColor(): string {
      return getBackgroundColor(this);
    },

    getCurrentTime(): number {
      return getCurrentTime(this);
    },

    /**
     * Get the active composition (mutable reference)
     */
    getActiveComp(): Composition | null {
      return this.project.compositions[this.activeCompositionId] || null;
    },

    /**
     * Get the layers array for the active composition (mutable reference)
     */
    getActiveCompLayers(): Layer[] {
      const comp = this.project.compositions[this.activeCompositionId];
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const layers = (comp !== null && comp !== undefined && typeof comp === "object" && "layers" in comp) ? comp.layers : undefined;
      return (layers !== null && layers !== undefined && Array.isArray(layers)) ? layers : [];
    },

    selectAsset(assetId: string | null): void {
      selectAsset(this, assetId);
    },

    loadInputs(inputs: Parameters<typeof loadInputs>[1]): void {
      loadInputs(this, inputs);
    },

    // ========================================================================
    // HISTORY MANAGEMENT
    // ========================================================================

    pushHistory(): void {
      if (this.historyIndex < this.historyStack.length - 1) {
        this.historyStack = this.historyStack.slice(0, this.historyIndex + 1);
      }
      const snapshot: LatticeProject = structuredClone<LatticeProject>(toRaw(this.project));
      this.historyStack.push(snapshot);
      this.historyIndex = this.historyStack.length - 1;
      if (this.historyStack.length > MAX_HISTORY_SIZE) {
        this.historyStack = this.historyStack.slice(-MAX_HISTORY_SIZE);
        this.historyIndex = this.historyStack.length - 1;
      }
    },

    undo(): boolean {
      if (this.historyIndex <= 0) return false;
      this.historyIndex--;
      const historyEntry = toRaw(this.historyStack[this.historyIndex]);
      this.project = structuredClone<LatticeProject>(historyEntry);
      invalidateParticleCaches();
      return true;
    },

    redo(): boolean {
      if (this.historyIndex >= this.historyStack.length - 1) return false;
      this.historyIndex++;
      const historyEntry = toRaw(this.historyStack[this.historyIndex]);
      this.project = structuredClone<LatticeProject>(historyEntry);
      invalidateParticleCaches();
      return true;
    },

    canUndo(): boolean {
      return this.historyIndex > 0;
    },

    canRedo(): boolean {
      return this.historyIndex < this.historyStack.length - 1;
    },

    clearHistory(): void {
      const snapshot: LatticeProject = structuredClone<LatticeProject>(toRaw(this.project));
      this.historyStack = [snapshot];
      this.historyIndex = 0;
    },

    // ========================================================================
    // PROJECT INITIALIZATION
    // ========================================================================

    newProject(): void {
      this.project = createDefaultProject();
      this.lastSaveProjectId = null;
      this.lastSaveTime = 0;
      this.hasUnsavedChanges = false;
      this.clearHistory();
      storeLogger.info("Project reset to default state");
    },

    /**
     * Save project (convenience wrapper for performAutosave).
     */
    async saveProject(): Promise<void> {
      await this.performAutosave();
    },

    /**
     * Save project as (to server with new ID).
     */
    async saveProjectAs(): Promise<string | null> {
      return await this.saveProjectToServer(undefined);
    },

    // ========================================================================
    // SERIALIZATION
    // ========================================================================

    exportProject(): string {
      const project: LatticeProject = { ...this.project };
      const animationStore = useAnimationStore();
      if (animationStore.snapConfig) {
        project.snapConfig = animationStore.snapConfig;
      }
      return JSON.stringify(project, null, 2);
    },

    importProject(json: string, pushHistoryFn: () => void): boolean {
      try {
        const parseResult = safeJsonParse<LatticeProject>(json, undefined, {
          maxSize: MAX_PROJECT_SIZE,
          maxDepth: MAX_PROJECT_DEPTH,
          maxArrayLength: MAX_ARRAY_LENGTH,
          context: "Project import",
        });

        let project = parseResult.data;

        // Cast to Record for migration functions that accept union type
        const projectForMigration = project as unknown as Record<string, JSONValue>;
        if (needsMigration(projectForMigration)) {
          // Type proof: schemaVersion ∈ ℕ ∪ {undefined} → ℕ
          const schemaVersionValue = project.schemaVersion;
          const oldVersion = isFiniteNumber(schemaVersionValue) && Number.isInteger(schemaVersionValue) && schemaVersionValue >= 1 ? schemaVersionValue : 1;
          storeLogger.info(`Migrating project from schema v${oldVersion} to v${CURRENT_SCHEMA_VERSION}`);
          const migrationResult = migrateProject(projectForMigration);
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

        const animationStore = useAnimationStore();
        if (project.snapConfig) {
          try {
            animationStore.setSnapConfig(project.snapConfig);
          } catch {
            // Continue with default snapConfig
          }
        }

        const { snapConfig: _, ...projectWithoutSnapConfig } = project;
        this.project = projectWithoutSnapConfig;
        pushHistoryFn();
        return true;
      } catch (err) {
        storeLogger.error("Failed to import project:", err);
        return false;
      }
    },

    async loadProjectFromFile(file: File, pushHistoryFn: () => void): Promise<boolean> {
      try {
        const json = await file.text();

        try {
          const parseResult = safeJsonParse<LatticeProject>(json, undefined, {
            maxSize: MAX_PROJECT_SIZE,
            maxDepth: MAX_PROJECT_DEPTH,
            maxArrayLength: MAX_ARRAY_LENGTH,
            context: "Project file validation",
          });

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

        const success = this.importProject(json, pushHistoryFn);
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

    async saveProjectToServer(projectId?: string): Promise<string | null> {
      try {
        const result = await saveProject(this.project, projectId);
        if (result.status === "success" && result.project_id) {
          this.lastSaveProjectId = result.project_id;
          this.lastSaveTime = Date.now();
          this.hasUnsavedChanges = false;
          storeLogger.info("Project saved to server:", result.project_id);
          return result.project_id;
        } else {
          throw new Error(`[ProjectStore] Failed to save project to server: ${result.message || "Unknown error"}`);
        }
      } catch (err) {
        if (err instanceof Error && err.message.startsWith("[ProjectStore]")) {
          throw err;
        }
        throw new Error(`[ProjectStore] Error saving project to server: ${err instanceof Error ? err.message : String(err)}`);
      }
    },

    async loadProjectFromServer(projectId: string, pushHistoryFn: () => void): Promise<boolean> {
      try {
        const result = await loadProject(projectId);

        if (result.status === "success" && result.project) {
          let project = result.project;

          // Cast to Record for migration functions that accept union type
          const projectForMigration = project as unknown as Record<string, JSONValue>;
          if (needsMigration(projectForMigration)) {
            // Type proof: schemaVersion ∈ ℕ ∪ {undefined} → ℕ
          const schemaVersionValue = project.schemaVersion;
          const oldVersion = isFiniteNumber(schemaVersionValue) && Number.isInteger(schemaVersionValue) && schemaVersionValue >= 1 ? schemaVersionValue : 1;
            storeLogger.info(`Migrating project from schema v${oldVersion} to v${CURRENT_SCHEMA_VERSION}`);
            const migrationResult = migrateProject(projectForMigration);
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

          this.project = project;
          pushHistoryFn();
          this.lastSaveProjectId = projectId;
          this.lastSaveTime = Date.now();
          this.hasUnsavedChanges = false;
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

    startAutosave(performAutosaveFn: () => Promise<void>): void {
      if (this.autosaveTimerId !== null || !this.autosaveEnabled) return;
      this.autosaveTimerId = window.setInterval(performAutosaveFn, this.autosaveIntervalMs);
      storeLogger.info("Autosave started with interval:", this.autosaveIntervalMs);
    },

    stopAutosave(): void {
      if (this.autosaveTimerId !== null && this.autosaveTimerId !== undefined) {
        window.clearInterval(this.autosaveTimerId);
        this.autosaveTimerId = null;
        storeLogger.info("Autosave stopped");
      }
    },

    configureAutosave(
      options: { enabled?: boolean; intervalMs?: number },
      performAutosaveFn: () => Promise<void>,
    ): void {
      if (options.enabled !== undefined) this.autosaveEnabled = options.enabled;
      if (options.intervalMs !== undefined && Number.isFinite(options.intervalMs) && options.intervalMs > 0) {
        this.autosaveIntervalMs = options.intervalMs;
      }
      this.stopAutosave();
      if (this.autosaveEnabled) this.startAutosave(performAutosaveFn);
    },

    async performAutosave(): Promise<void> {
      if (!this.hasUnsavedChanges) return;

      try {
        const existingProjectId = this.lastSaveProjectId || undefined;
        const result = await saveProject(this.project, existingProjectId);
        if (result.status === "success" && result.project_id) {
          this.lastSaveProjectId = result.project_id;
          this.lastSaveTime = Date.now();
          this.hasUnsavedChanges = false;
          storeLogger.info("Autosaved project:", result.project_id);
        } else {
          storeLogger.error("Autosave failed:", result.message);
        }
      } catch (error) {
        storeLogger.error("Autosave failed:", error);
      }
    },

    markUnsavedChanges(): void {
      this.hasUnsavedChanges = true;
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
        this.pushHistory();
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

      const usedIds = includeUnused ? null : findUsedAssetIds(store);
      const assets = store.project.assets;
      const assetsFolder = folder.folder("assets");
      if (assetsFolder === null) throw new Error("Failed to create assets ZIP folder");
      const assetManifest: Record<string, string> = {};

      for (const [assetId, asset] of Object.entries(assets)) {
        if (usedIds !== null && !usedIds.has(assetId)) continue;

        const filename = asset.filename ? asset.filename : `${assetId}.${getExtensionForAsset(asset)}`;
        assetManifest[assetId] = `assets/${filename}`;

        if (asset.data) {
          if (asset.data.startsWith("data:")) {
            const base64Data = asset.data.split(",")[1];
            if (base64Data) {
              assetsFolder.file(filename, base64Data, { base64: true });
            }
          } else if (asset.data.startsWith("blob:") || asset.data.startsWith("http")) {
            const urlValidation = validateURL(asset.data, "fetch");
            if (!urlValidation.valid) {
              storeLogger.warn(`[SECURITY] Skipped asset ${assetId}: ${urlValidation.error}`);
              continue;
            }
            try {
              const sanitizedUrl = urlValidation.sanitized ? urlValidation.sanitized : asset.data;
              const response = await fetch(sanitizedUrl);
              const blob = await response.blob();
              assetsFolder.file(filename, blob);
            } catch (e) {
              storeLogger.warn(`Failed to fetch asset ${assetId}:`, e);
            }
          } else {
            assetsFolder.file(filename, asset.data, { base64: true });
          }
        }
      }

      const exportProject = structuredClone(toRaw(store.project)) as LatticeProject & {
        meta: ProjectMeta & { exportedAt?: string };
        _assetManifest?: typeof assetManifest;
      };
      exportProject.meta.exportedAt = new Date().toISOString();
      exportProject._assetManifest = assetManifest;

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
