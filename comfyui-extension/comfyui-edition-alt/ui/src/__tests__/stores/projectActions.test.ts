/**
 * Project Actions Tests
 *
 * Tests for history management, project serialization, autosave,
 * and asset management.
 *
 * CRITICAL: These functions handle user data. Bugs here = data loss.
 *
 * @audit P0 CRITICAL - Data integrity
 */

import { describe, it, expect, beforeEach, vi, afterEach } from "vitest";
import { setActivePinia, createPinia } from "pinia";
import { useProjectStore, createDefaultProject, findUsedAssetIds } from "@/stores/projectStore";
import type { ProjectStore } from "@/stores/projectStore";
import type { LatticeProject, Layer, Composition, LayerType, AssetReference, ProjectMeta } from "@/types/project";
import type { ParticleLayerData } from "@/types/particles";
import { isObject } from "@/utils/typeGuards";

// Initialize Pinia before tests
beforeEach(() => {
  setActivePinia(createPinia());
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Shim functions - wrap store actions for backward compatibility with tests
// ════════════════════════════════════════════════════════════════════════════

const projectStore = () => useProjectStore();

function pushHistory(store: ProjectStore): void {
  projectStore().pushHistory(store);
}

function undo(store: ProjectStore): boolean {
  return projectStore().undo(store);
}

function redo(store: ProjectStore): boolean {
  return projectStore().redo(store);
}

function canUndo(store: ProjectStore): boolean {
  return projectStore().canUndo(store);
}

function canRedo(store: ProjectStore): boolean {
  return projectStore().canRedo(store);
}

function clearHistory(store: ProjectStore): void {
  projectStore().clearHistory(store);
}

function exportProject(store: ProjectStore): string {
  return projectStore().exportProject(store);
}

function importProject(store: ProjectStore, json: string, pushHistoryFn: () => void): boolean {
  return projectStore().importProject(store, json, pushHistoryFn);
}

function resetProject(store: ProjectStore): void {
  // Reset to default project state
  const defaultProject = createDefaultProject();
  store.project = defaultProject;
  store.historyStack = [structuredClone(defaultProject)];
  store.historyIndex = 0;
  store.hasUnsavedChanges = false;
  store.lastSaveProjectId = null;
  store.lastSaveTime = 0;
}

function markUnsavedChanges(store: ProjectStore): void {
  projectStore().markUnsavedChanges(store);
}

function configureAutosave(store: ProjectStore, enabled: boolean, intervalMs: number, performAutosaveFn: () => Promise<void>): void {
  projectStore().configureAutosave(store, enabled, intervalMs, performAutosaveFn);
}

function startAutosave(store: ProjectStore, performAutosaveFn: () => Promise<void>): void {
  projectStore().startAutosave(store, performAutosaveFn);
}

function stopAutosave(store: ProjectStore): void {
  projectStore().stopAutosave(store);
}

async function performAutosave(store: ProjectStore): Promise<void> {
  return projectStore().performAutosave(store);
}

function removeUnusedAssets(store: ProjectStore): { removed: number; assetNames: string[] } {
  return projectStore().removeUnusedAssets(store);
}

function getAssetUsageStats(store: ProjectStore): { total: number; used: number; unused: number; usedNames: string[]; unusedNames: string[] } {
  return projectStore().getAssetUsageStats(store);
}

// ════════════════════════════════════════════════════════════════════════════
// Test Helpers
// ════════════════════════════════════════════════════════════════════════════

function createMockProject(overrides: Partial<LatticeProject> = {}): LatticeProject {
  return {
    version: "1.0.0",
    schemaVersion: 2,
    meta: {
      name: "Test Project",
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
    },
    composition: {
      width: 1920,
      height: 1080,
      frameCount: 81,
      fps: 16,
      duration: 5,
      backgroundColor: "#000000",
      autoResizeToContent: false,
      frameBlendingEnabled: false,
    },
    compositions: {
      main: {
        id: "main",
        name: "Main Comp",
        settings: {
          width: 1920,
          height: 1080,
          frameCount: 81,
          fps: 16,
          duration: 5,
          backgroundColor: "#000000",
          autoResizeToContent: false,
          frameBlendingEnabled: false,
        },
        layers: [],
        currentFrame: 0,
        isNestedComp: false,
      },
    },
    mainCompositionId: "main",
    layers: [],
    currentFrame: 0,
    assets: {},
    ...overrides,
  };
}

function createMockStore(overrides: Partial<ProjectStore> = {}): ProjectStore {
  return {
    project: createMockProject(),
    historyStack: [createMockProject()],
    historyIndex: 0,
    lastSaveProjectId: null,
    lastSaveTime: 0, // 0 = never saved
    hasUnsavedChanges: false,
    autosaveEnabled: false,
    autosaveIntervalMs: 60000,
    autosaveTimerId: null,
    ...overrides,
  };
}

function createMockLayer(id: string, type: LayerType = "solid", data: Record<string, unknown> = {}): Layer {
  return {
    id,
    name: `Layer ${id}`,
    type,
    visible: true,
    locked: false,
    isolate: false,
    motionBlur: false,
    startFrame: 0,
    endFrame: 100,
    inPoint: 0,
    outPoint: 100,
    blendMode: "normal",
    threeD: false,
    opacity: { id: "op", name: "opacity", type: "number", value: 100, animated: false, keyframes: [] },
    transform: {
      position: { id: "pos", name: "position", type: "vector3", value: { x: 0, y: 0, z: 0 }, animated: false, keyframes: [] },
      scale: { id: "sc", name: "scale", type: "vector3", value: { x: 100, y: 100, z: 100 }, animated: false, keyframes: [] },
      rotation: { id: "rot", name: "rotation", type: "number", value: 0, animated: false, keyframes: [] },
      origin: { id: "org", name: "origin", type: "vector3", value: { x: 0, y: 0, z: 0 }, animated: false, keyframes: [] },
    },
    effects: [],
    properties: [],
    parentId: null,
    data: { type, ...data },
  };
}

// ════════════════════════════════════════════════════════════════════════════
// History Management Tests
// ════════════════════════════════════════════════════════════════════════════

describe("History Management", () => {
  describe("pushHistory", () => {
    it("adds current project state to history stack", () => {
      const store = createMockStore();
      const initialLength = store.historyStack.length;

      store.project.meta.name = "Modified";
      pushHistory(store);

      expect(store.historyStack.length).toBe(initialLength + 1);
      expect(store.historyIndex).toBe(store.historyStack.length - 1);
    });

    it("creates deep clone (modifications don't affect history)", () => {
      const store = createMockStore();
      pushHistory(store);

      const historySnapshot = store.historyStack[store.historyIndex];
      store.project.meta.name = "Changed After Push";

      expect(historySnapshot.meta.name).not.toBe("Changed After Push");
    });

    it("truncates future history when pushing from middle of stack", () => {
      const store = createMockStore();

      // Push 3 states
      store.project.meta.name = "State 1";
      pushHistory(store);
      store.project.meta.name = "State 2";
      pushHistory(store);
      store.project.meta.name = "State 3";
      pushHistory(store);

      // Go back 2 steps
      undo(store);
      undo(store);

      // Push new state - should truncate future
      store.project.meta.name = "New Branch";
      pushHistory(store);

      // History should be: initial, State 1, New Branch
      expect(store.historyStack.length).toBe(3);
      expect(store.historyStack[store.historyStack.length - 1].meta.name).toBe("New Branch");
    });

    it("limits history size to MAX_HISTORY_SIZE (50)", () => {
      const store = createMockStore();

      // Push 60 states
      for (let i = 0; i < 60; i++) {
        store.project.meta.name = `State ${i}`;
        pushHistory(store);
      }

      expect(store.historyStack.length).toBeLessThanOrEqual(50);
      expect(store.historyIndex).toBe(store.historyStack.length - 1);
    });

    it("preserves layer data in history snapshot", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1", "solid", { color: "#ff0000" });
      store.project.compositions.main.layers.push(layer);

      pushHistory(store);

      // Modify layer after push
      (store.project.compositions.main.layers[0].data as { color: string }).color = "#00ff00";

      // History should have original color
      const snapshot = store.historyStack[store.historyIndex];
      expect((snapshot.compositions.main.layers[0].data as { color: string }).color).toBe("#ff0000");
    });
  });

  describe("undo", () => {
    it("returns false when at beginning of history", () => {
      const store = createMockStore();
      expect(undo(store)).toBe(false);
      expect(store.historyIndex).toBe(0);
    });

    it("decrements history index and restores previous state", () => {
      const store = createMockStore();

      store.project.meta.name = "Modified";
      pushHistory(store);

      expect(store.historyIndex).toBe(1);
      expect(undo(store)).toBe(true);
      expect(store.historyIndex).toBe(0);
      expect(store.project.meta.name).toBe("Test Project");
    });

    it("restores complete project state", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1");
      store.project.compositions.main.layers.push(layer);
      pushHistory(store);

      // Remove layer
      store.project.compositions.main.layers = [];
      pushHistory(store);

      // Undo should restore layer
      undo(store);
      expect(store.project.compositions.main.layers.length).toBe(1);
      expect(store.project.compositions.main.layers[0].id).toBe("layer-1");
    });

    it("multiple undos walk back through history correctly", () => {
      const store = createMockStore();

      for (let i = 1; i <= 5; i++) {
        store.project.meta.name = `State ${i}`;
        pushHistory(store);
      }

      expect(store.project.meta.name).toBe("State 5");

      undo(store);
      expect(store.project.meta.name).toBe("State 4");

      undo(store);
      expect(store.project.meta.name).toBe("State 3");

      undo(store);
      expect(store.project.meta.name).toBe("State 2");
    });
  });

  describe("redo", () => {
    it("returns false when at end of history", () => {
      const store = createMockStore();
      expect(redo(store)).toBe(false);
    });

    it("increments history index and restores next state", () => {
      const store = createMockStore();

      store.project.meta.name = "State 1";
      pushHistory(store);

      undo(store);
      expect(store.project.meta.name).toBe("Test Project");

      expect(redo(store)).toBe(true);
      expect(store.project.meta.name).toBe("State 1");
    });

    it("multiple redos walk forward through history correctly", () => {
      const store = createMockStore();

      for (let i = 1; i <= 3; i++) {
        store.project.meta.name = `State ${i}`;
        pushHistory(store);
      }

      // Undo all
      undo(store);
      undo(store);
      undo(store);

      expect(store.project.meta.name).toBe("Test Project");

      redo(store);
      expect(store.project.meta.name).toBe("State 1");

      redo(store);
      expect(store.project.meta.name).toBe("State 2");

      redo(store);
      expect(store.project.meta.name).toBe("State 3");
    });
  });

  describe("canUndo / canRedo", () => {
    it("canUndo returns false at start of history", () => {
      const store = createMockStore();
      expect(canUndo(store)).toBe(false);
    });

    it("canUndo returns true when history exists", () => {
      const store = createMockStore();
      pushHistory(store);
      expect(canUndo(store)).toBe(true);
    });

    it("canRedo returns false at end of history", () => {
      const store = createMockStore();
      pushHistory(store);
      expect(canRedo(store)).toBe(false);
    });

    it("canRedo returns true after undo", () => {
      const store = createMockStore();
      pushHistory(store);
      undo(store);
      expect(canRedo(store)).toBe(true);
    });
  });

  describe("clearHistory", () => {
    it("resets history to single entry with current project", () => {
      const store = createMockStore();

      for (let i = 0; i < 10; i++) {
        pushHistory(store);
      }

      store.project.meta.name = "Current State";
      clearHistory(store);

      expect(store.historyStack.length).toBe(1);
      expect(store.historyIndex).toBe(0);
      expect(store.historyStack[0].meta.name).toBe("Current State");
    });

    it("cleared history snapshot is independent of current project", () => {
      const store = createMockStore();
      clearHistory(store);

      store.project.meta.name = "Changed After Clear";

      expect(store.historyStack[0].meta.name).not.toBe("Changed After Clear");
    });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Project Serialization Tests
// ════════════════════════════════════════════════════════════════════════════

describe("Project Serialization", () => {
  describe("exportProject", () => {
    it("returns valid JSON string", () => {
      const store = createMockStore();
      const json = exportProject(store);

      expect(() => JSON.parse(json)).not.toThrow();
    });

    it("exported JSON matches project structure", () => {
      const store = createMockStore();
      store.project.meta.name = "Export Test";

      const json = exportProject(store);
      const parsed = JSON.parse(json);

      expect(parsed.meta.name).toBe("Export Test");
      expect(parsed.version).toBe("1.0.0");
      expect(parsed.compositions).toBeDefined();
    });

    it("preserves all project data in export", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1", "text", { text: "Hello" });
      store.project.compositions.main.layers.push(layer);
      // Create minimal valid AssetReference for testing
      const asset: AssetReference = {
        id: "asset-1",
        type: "image",
        source: "file",
        width: 1920,
        height: 1080,
        data: "data:image/png;base64,test",
        filename: "test.png",
      };
      store.project.assets = {
        "asset-1": asset,
      };

      const json = exportProject(store);
      const parsed = JSON.parse(json);

      expect(parsed.compositions.main.layers.length).toBe(1);
      expect(parsed.compositions.main.layers[0].data.text).toBe("Hello");
      expect(parsed.assets["asset-1"].filename).toBe("test.png");
    });
  });

  describe("importProject", () => {
    it("successfully imports valid project JSON", () => {
      const store = createMockStore();
      // Create minimal valid ProjectMeta for testing
      const meta: ProjectMeta = {
        name: "Imported",
        created: new Date().toISOString(),
        modified: new Date().toISOString(),
      };
      const projectJson = JSON.stringify(createMockProject({ meta }));
      const pushHistoryFn = vi.fn();

      const result = importProject(store, projectJson, pushHistoryFn);

      expect(result).toBe(true);
      expect(store.project.meta.name).toBe("Imported");
      expect(pushHistoryFn).toHaveBeenCalled();
    });

    it("returns false for invalid JSON", () => {
      const store = createMockStore();
      const pushHistoryFn = vi.fn();

      const result = importProject(store, "not valid json {{{", pushHistoryFn);

      expect(result).toBe(false);
      expect(pushHistoryFn).not.toHaveBeenCalled();
    });

    it("preserves existing project on failed import", () => {
      const store = createMockStore();
      store.project.meta.name = "Original";
      const pushHistoryFn = vi.fn();

      importProject(store, "invalid", pushHistoryFn);

      expect(store.project.meta.name).toBe("Original");
    });
  });

  describe("createDefaultProject", () => {
    it("creates project with all required fields", () => {
      const project = createDefaultProject();

      expect(project.version).toBeDefined();
      expect(project.schemaVersion).toBeDefined();
      expect(project.meta).toBeDefined();
      expect(project.meta.name).toBeDefined();
      expect(project.meta.created).toBeDefined();
      expect(project.compositions).toBeDefined();
      expect(project.mainCompositionId).toBeDefined();
      expect(project.assets).toBeDefined();
    });

    it("creates main composition with correct defaults", () => {
      const project = createDefaultProject();
      const mainComp = project.compositions[project.mainCompositionId];

      expect(mainComp).toBeDefined();
      expect(mainComp.settings.width).toBe(1920);
      expect(mainComp.settings.height).toBe(1080);
      expect(mainComp.settings.fps).toBe(16);
      expect(mainComp.settings.frameCount).toBe(81);
      expect(mainComp.layers).toEqual([]);
    });

    it("creates unique projects (not shared references)", () => {
      const project1 = createDefaultProject();
      const project2 = createDefaultProject();

      project1.meta.name = "Project 1";

      expect(project2.meta.name).not.toBe("Project 1");
    });
  });

  describe("resetProject", () => {
    it("replaces project with default state", () => {
      const store = createMockStore();
      store.project.meta.name = "Modified Project";
      const layer = createMockLayer("layer-1");
      store.project.compositions.main.layers.push(layer);

      resetProject(store);

      expect(store.project.meta.name).toBe("Untitled Project");
      expect(store.project.compositions[store.project.mainCompositionId].layers).toEqual([]);
    });

    it("clears save state", () => {
      const store = createMockStore();
      store.lastSaveProjectId = "saved-123";
      store.lastSaveTime = Date.now();
      store.hasUnsavedChanges = true;

      resetProject(store);

      expect(store.lastSaveProjectId).toBeNull();
      expect(store.lastSaveTime).toBe(0);
      expect(store.hasUnsavedChanges).toBe(false);
    });

    it("clears history", () => {
      const store = createMockStore();
      for (let i = 0; i < 5; i++) {
        pushHistory(store);
      }

      resetProject(store);

      expect(store.historyStack.length).toBe(1);
      expect(store.historyIndex).toBe(0);
    });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Autosave Tests
// ════════════════════════════════════════════════════════════════════════════

describe("Autosave Management", () => {
  beforeEach(() => {
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe("markUnsavedChanges", () => {
    it("sets hasUnsavedChanges to true", () => {
      const store = createMockStore();
      store.hasUnsavedChanges = false;

      markUnsavedChanges(store);

      expect(store.hasUnsavedChanges).toBe(true);
    });
  });

  describe("configureAutosave", () => {
    it("updates autosave enabled state", () => {
      const store = createMockStore();
      const performFn = vi.fn();

      configureAutosave(store, { enabled: true }, performFn);

      expect(store.autosaveEnabled).toBe(true);
    });

    it("updates interval when valid", () => {
      const store = createMockStore();
      const performFn = vi.fn();

      configureAutosave(store, { intervalMs: 30000 }, performFn);

      expect(store.autosaveIntervalMs).toBe(30000);
    });

    it("ignores invalid intervalMs (NaN)", () => {
      const store = createMockStore();
      store.autosaveIntervalMs = 60000;
      const performFn = vi.fn();

      configureAutosave(store, { intervalMs: NaN }, performFn);

      expect(store.autosaveIntervalMs).toBe(60000);
    });

    it("ignores invalid intervalMs (negative)", () => {
      const store = createMockStore();
      store.autosaveIntervalMs = 60000;
      const performFn = vi.fn();

      configureAutosave(store, { intervalMs: -1000 }, performFn);

      expect(store.autosaveIntervalMs).toBe(60000);
    });

    it("ignores invalid intervalMs (zero)", () => {
      const store = createMockStore();
      store.autosaveIntervalMs = 60000;
      const performFn = vi.fn();

      configureAutosave(store, { intervalMs: 0 }, performFn);

      expect(store.autosaveIntervalMs).toBe(60000);
    });

    it("ignores invalid intervalMs (Infinity)", () => {
      const store = createMockStore();
      store.autosaveIntervalMs = 60000;
      const performFn = vi.fn();

      configureAutosave(store, { intervalMs: Infinity }, performFn);

      expect(store.autosaveIntervalMs).toBe(60000);
    });
  });

  describe("startAutosave", () => {
    it("does not start if disabled", () => {
      const store = createMockStore();
      store.autosaveEnabled = false;
      const performFn = vi.fn();

      startAutosave(store, performFn);

      expect(store.autosaveTimerId).toBeNull();
    });

    it("does not start if already running", () => {
      const store = createMockStore();
      store.autosaveEnabled = true;
      store.autosaveTimerId = 123;
      const performFn = vi.fn();

      startAutosave(store, performFn);

      expect(store.autosaveTimerId).toBe(123); // Unchanged
    });

    it("starts timer when enabled and not running", () => {
      const store = createMockStore();
      store.autosaveEnabled = true;
      store.autosaveTimerId = null;
      const performFn = vi.fn();

      startAutosave(store, performFn);

      expect(store.autosaveTimerId).not.toBeNull();
    });
  });

  describe("stopAutosave", () => {
    it("clears timer and sets timerId to null", () => {
      const store = createMockStore();
      store.autosaveTimerId = 123;

      stopAutosave(store);

      expect(store.autosaveTimerId).toBeNull();
    });

    it("handles already-stopped autosave gracefully", () => {
      const store = createMockStore();
      store.autosaveTimerId = null;

      expect(() => stopAutosave(store)).not.toThrow();
      expect(store.autosaveTimerId).toBeNull();
    });
  });

  describe("performAutosave", () => {
    it("does nothing if no unsaved changes", async () => {
      const store = createMockStore();
      store.hasUnsavedChanges = false;

      // Should complete without error
      await performAutosave(store);

      // State unchanged
      expect(store.hasUnsavedChanges).toBe(false);
    });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Asset Management Tests
// ════════════════════════════════════════════════════════════════════════════

describe("Asset Management", () => {
  describe("findUsedAssetIds", () => {
    it("returns empty set for project with no layers", () => {
      const store = createMockStore();
      const usedIds = findUsedAssetIds(store);

      expect(usedIds.size).toBe(0);
    });

    it("finds assetId in layer data", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1", "image", { assetId: "img-001" });
      store.project.compositions.main.layers.push(layer);

      const usedIds = findUsedAssetIds(store);

      expect(usedIds.has("img-001")).toBe(true);
    });

    it("finds sourceAssetId in layer data", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1", "depth", { sourceAssetId: "depth-001" });
      store.project.compositions.main.layers.push(layer);

      const usedIds = findUsedAssetIds(store);

      expect(usedIds.has("depth-001")).toBe(true);
    });

    it("finds material texture IDs", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1", "model", {
        materials: [
          { textureId: "tex-001", normalMapId: "norm-001", roughnessMapId: "rough-001" },
        ],
      });
      store.project.compositions.main.layers.push(layer);

      const usedIds = findUsedAssetIds(store);

      expect(usedIds.has("tex-001")).toBe(true);
      expect(usedIds.has("norm-001")).toBe(true);
      expect(usedIds.has("rough-001")).toBe(true);
    });

    it("finds spriteSheetAssetId", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1", "particle", { spriteSheetAssetId: "sprite-001" });
      store.project.compositions.main.layers.push(layer);

      const usedIds = findUsedAssetIds(store);

      expect(usedIds.has("sprite-001")).toBe(true);
    });

    it("finds environmentMapId", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1", "model", { environmentMapId: "env-001" });
      store.project.compositions.main.layers.push(layer);

      const usedIds = findUsedAssetIds(store);

      expect(usedIds.has("env-001")).toBe(true);
    });

    it("finds assets across multiple compositions", () => {
      const store = createMockStore();

      // Add second composition
      store.project.compositions["comp2"] = {
        id: "comp2",
        name: "Comp 2",
        settings: store.project.composition,
        layers: [createMockLayer("layer-2", "image", { assetId: "img-002" })],
        currentFrame: 0,
        isNestedComp: false,
      };

      // Add layer to main comp
      store.project.compositions.main.layers.push(
        createMockLayer("layer-1", "image", { assetId: "img-001" })
      );

      const usedIds = findUsedAssetIds(store);

      expect(usedIds.has("img-001")).toBe(true);
      expect(usedIds.has("img-002")).toBe(true);
    });
  });

  describe("removeUnusedAssets", () => {
    it("removes assets not referenced by any layer", () => {
      const store = createMockStore();
      // Create minimal valid AssetReference objects for testing
      const usedAsset: AssetReference = {
        id: "used-001",
        type: "image",
        source: "file",
        width: 1920,
        height: 1080,
        data: "data:image/png;base64,used",
        filename: "used.png",
      };
      const unusedAsset: AssetReference = {
        id: "unused-001",
        type: "image",
        source: "file",
        width: 1920,
        height: 1080,
        data: "data:image/png;base64,unused",
        filename: "unused.png",
      };
      store.project.assets = {
        "used-001": usedAsset,
        "unused-001": unusedAsset,
      };

      const layer = createMockLayer("layer-1", "image", { assetId: "used-001" });
      store.project.compositions.main.layers.push(layer);

      const result = removeUnusedAssets(store);

      expect(result.removed).toBe(1);
      expect(result.assetNames).toContain("unused.png");
      expect(store.project.assets["used-001"]).toBeDefined();
      expect(store.project.assets["unused-001"]).toBeUndefined();
    });

    it("returns 0 when all assets are used", () => {
      const store = createMockStore();
      store.project.assets = {
        "used-001": {
          id: "used-001",
          type: "image",
          source: "file",
          width: 1920,
          height: 1080,
          data: "data:image/png;base64,used",
          filename: "used.png",
        },
      };

      const layer = createMockLayer("layer-1", "image", { assetId: "used-001" });
      store.project.compositions.main.layers.push(layer);

      const result = removeUnusedAssets(store);

      expect(result.removed).toBe(0);
      expect(result.assetNames).toHaveLength(0);
    });

    it("pushes history after removing assets", () => {
      const store = createMockStore();
      store.project.assets = {
        "unused-001": {
          id: "unused-001",
          type: "image",
          source: "file",
          width: 1920,
          height: 1080,
          data: "data:image/png;base64,unused",
          filename: "unused.png",
        },
      };
      const initialHistoryLength = store.historyStack.length;

      removeUnusedAssets(store);

      expect(store.historyStack.length).toBe(initialHistoryLength + 1);
    });

    it("does not push history when no assets removed", () => {
      const store = createMockStore();
      const initialHistoryLength = store.historyStack.length;

      removeUnusedAssets(store);

      expect(store.historyStack.length).toBe(initialHistoryLength);
    });
  });

  describe("getAssetUsageStats", () => {
    it("returns correct counts", () => {
      const store = createMockStore();
      store.project.assets = {
        "used-001": {
          id: "used-001",
          type: "image",
          source: "file",
          width: 1920,
          height: 1080,
          data: "data:image/png;base64,used",
          filename: "used.png",
        },
        "unused-001": {
          id: "unused-001",
          type: "image",
          source: "file",
          width: 1920,
          height: 1080,
          data: "data:image/png;base64,unused1",
          filename: "unused1.png",
        },
        "unused-002": {
          id: "unused-002",
          type: "image",
          source: "file",
          width: 1920,
          height: 1080,
          data: "data:image/png;base64,unused2",
          filename: "unused2.png",
        },
      };

      const layer = createMockLayer("layer-1", "image", { assetId: "used-001" });
      store.project.compositions.main.layers.push(layer);

      const stats = getAssetUsageStats(store);

      expect(stats.total).toBe(3);
      expect(stats.used).toBe(1);
      expect(stats.unused).toBe(2);
      expect(stats.unusedNames).toContain("unused1.png");
      expect(stats.unusedNames).toContain("unused2.png");
    });

    it("handles empty project", () => {
      const store = createMockStore();

      const stats = getAssetUsageStats(store);

      expect(stats.total).toBe(0);
      expect(stats.used).toBe(0);
      expect(stats.unused).toBe(0);
    });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Edge Cases & Determinism Tests
// ════════════════════════════════════════════════════════════════════════════

describe("Edge Cases", () => {
  describe("History with rapid operations", () => {
    it("handles rapid push/undo/redo sequence correctly", () => {
      const store = createMockStore();

      // Rapid operations
      for (let i = 0; i < 10; i++) {
        store.project.meta.name = `State ${i}`;
        pushHistory(store);
      }

      undo(store);
      undo(store);
      redo(store);
      pushHistory(store);
      undo(store);
      undo(store);
      undo(store);
      redo(store);
      redo(store);

      // Should not throw
      expect(store.historyIndex).toBeGreaterThanOrEqual(0);
      expect(store.historyIndex).toBeLessThan(store.historyStack.length);
    });
  });

  describe("Project with deep nesting", () => {
    it("preserves deeply nested layer data through history", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1", "particle", {
        emitter: {
          config: {
            nested: {
              deeply: {
                value: 42,
              },
            },
          },
        },
      });
      store.project.compositions.main.layers.push(layer);

      // Push state WITH the layer (value = 42)
      pushHistory(store);

      // Modify nested value to 100
      // Type guard ensures safe property access for deeply nested test data
      const layerData = store.project.compositions.main.layers[0].data;
      if (!isObject(layerData)) {
        throw new Error("Expected layer.data to be an object");
      }
      const layerDataObj = layerData as Record<string, unknown>;
      const emitter = layerDataObj.emitter as Record<string, unknown>;
      const config = emitter.config as Record<string, unknown>;
      const nested = config.nested as Record<string, unknown>;
      const deeply = nested.deeply as Record<string, unknown>;
      deeply.value = 100;

      // Push modified state
      pushHistory(store);

      // Now undo should restore value to 42
      undo(store);

      // Type guard ensures safe property access for assertion
      const restoredLayerData = store.project.compositions.main.layers[0].data;
      if (!isObject(restoredLayerData)) {
        throw new Error("Expected layer.data to be an object");
      }
      const restoredLayerDataObj = restoredLayerData as Record<string, unknown>;
      const restoredEmitter = restoredLayerDataObj.emitter as Record<string, unknown>;
      const restoredConfig = restoredEmitter.config as Record<string, unknown>;
      const restoredNested = restoredConfig.nested as Record<string, unknown>;
      const restoredDeeply = restoredNested.deeply as Record<string, unknown>;
      expect(restoredDeeply.value).toBe(42);
    });
  });

  describe("Serialization with special values", () => {
    it("handles project with unicode characters", () => {
      const store = createMockStore();
      store.project.meta.name = "プロジェクト 🎬 مشروع";

      const json = exportProject(store);
      const parsed = JSON.parse(json);

      expect(parsed.meta.name).toBe("プロジェクト 🎬 مشروع");
    });

    it("handles project with empty strings", () => {
      const store = createMockStore();
      store.project.meta.name = "";

      const json = exportProject(store);
      const parsed = JSON.parse(json);

      expect(parsed.meta.name).toBe("");
    });

    it("handles project with very long names", () => {
      const store = createMockStore();
      store.project.meta.name = "a".repeat(10000);

      const json = exportProject(store);
      const parsed = JSON.parse(json);

      expect(parsed.meta.name.length).toBe(10000);
    });
  });

  describe("Asset management with edge cases", () => {
    it("handles layer with null data", () => {
      const store = createMockStore();
      const layer = createMockLayer("layer-1");
      // Type guard ensures safe property assignment for null data test
      const layerPartial: Partial<Layer> = { ...layer };
      layerPartial.data = null;
      store.project.compositions.main.layers.push(layerPartial as Layer);
      store.project.compositions.main.layers.push(layer);

      // Should not throw
      const usedIds = findUsedAssetIds(store);
      expect(usedIds.size).toBe(0);
    });

    it("handles asset with missing filename", () => {
      const store = createMockStore();
      store.project.assets = {
        "no-name": {
          id: "no-name",
          type: "image",
          source: "file",
          width: 1920,
          height: 1080,
          data: "data:image/png;base64,noname",
        },
      };

      const stats = getAssetUsageStats(store);

      // Should fall back to assetId
      expect(stats.unusedNames).toContain("no-name");
    });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// Determinism Tests
// ════════════════════════════════════════════════════════════════════════════

describe("Determinism", () => {
  it("same operations produce identical results", () => {
    const store1 = createMockStore();
    const store2 = createMockStore();

    // Perform identical operations on both
    for (let i = 0; i < 5; i++) {
      store1.project.meta.name = `State ${i}`;
      store2.project.meta.name = `State ${i}`;
      pushHistory(store1);
      pushHistory(store2);
    }

    undo(store1);
    undo(store2);
    redo(store1);
    redo(store2);

    expect(store1.project.meta.name).toBe(store2.project.meta.name);
    expect(store1.historyIndex).toBe(store2.historyIndex);
    expect(store1.historyStack.length).toBe(store2.historyStack.length);
  });

  it("export/import roundtrip is lossless", () => {
    const store = createMockStore();
    store.project.meta.name = "Roundtrip Test";
    const layer = createMockLayer("layer-1", "text", { text: "Hello World" });
    store.project.compositions.main.layers.push(layer);

    const exported = exportProject(store);

    const store2 = createMockStore();
    const pushFn = vi.fn();
    importProject(store2, exported, pushFn);

    expect(store2.project.meta.name).toBe(store.project.meta.name);
    expect(store2.project.compositions.main.layers.length).toBe(1);
    expect((store2.project.compositions.main.layers[0].data as { text: string }).text).toBe("Hello World");
  });
});
