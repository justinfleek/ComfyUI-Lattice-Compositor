/**
 * Composition Store
 *
 * Domain store for composition management including creation, deletion,
 * navigation, breadcrumb trail, and nested composition handling.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import type {
  Composition,
  CompositionSettings,
  Layer,
  NestedCompData,
} from "@/types/project";
import {
  createAnimatableProperty,
  createDefaultTransform,
} from "@/types/project";
import { DEFAULT_FPS, validateFps } from "@/utils/fpsUtils";
import { storeLogger } from "@/utils/logger";
import { useSelectionStore } from "./selectionStore";
import { useProjectStore } from "./projectStore";

// ============================================================================
// STORE ACCESS INTERFACE
// ============================================================================

export interface CompositionStoreAccess {
  project: {
    compositions: Record<string, Composition>;
    mainCompositionId: string;
    composition: CompositionSettings;
    meta: { modified: string };
  };
  activeCompositionId: string;
  openCompositionIds: string[];
  compositionBreadcrumbs: string[];
  selectedLayerIds: string[];
  getActiveComp(): Composition | null;
  switchComposition(compId: string): void;
  pushHistory(): void;
}

// ============================================================================
// PINIA STORE
// ============================================================================

export const useCompositionStore = defineStore("composition", {
  state: () => ({}),

  getters: {},

  actions: {
    // ========================================================================
    // CRUD OPERATIONS
    // ========================================================================

    /**
     * Create a new composition.
     */
    createComposition(
      name: string,
      settings?: Partial<CompositionSettings>,
      isNestedComp: boolean = false,
    ): Composition {
      const projectStore = useProjectStore();
      const id = `comp_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
      const activeComp = projectStore.project.compositions[projectStore.activeCompositionId];

      const rawFps = settings?.fps ?? activeComp?.settings.fps ?? DEFAULT_FPS;
      const validFps = validateFps(rawFps);

      const defaultSettings: CompositionSettings = {
        width: settings?.width ?? activeComp?.settings.width ?? 1024,
        height: settings?.height ?? activeComp?.settings.height ?? 1024,
        frameCount: settings?.frameCount ?? activeComp?.settings.frameCount ?? 81,
        fps: validFps,
        duration: 0,
        backgroundColor: settings?.backgroundColor ?? "#050505",
        autoResizeToContent: settings?.autoResizeToContent ?? true,
        frameBlendingEnabled: settings?.frameBlendingEnabled ?? false,
      };
      defaultSettings.duration = defaultSettings.frameCount / defaultSettings.fps;

      const composition: Composition = {
        id,
        name,
        settings: defaultSettings,
        layers: [],
        currentFrame: 0,
        isNestedComp,
      };

      projectStore.project.compositions[id] = composition;

      if (!projectStore.openCompositionIds.includes(id)) {
        projectStore.openCompositionIds.push(id);
      }
      projectStore.activeCompositionId = id;

      projectStore.pushHistory();
      storeLogger.debug("Created composition:", name, id);
      return composition;
    },

    /**
     * Delete a composition.
     */
    deleteComposition(store: CompositionStoreAccess, compId: string): boolean {
      if (compId === store.project.mainCompositionId) {
        storeLogger.warn("Cannot delete main composition");
        return false;
      }

      const comp = store.project.compositions[compId];
      if (!comp) return false;

      delete store.project.compositions[compId];

      const openIdx = store.openCompositionIds.indexOf(compId);
      if (openIdx >= 0) {
        store.openCompositionIds.splice(openIdx, 1);
      }

      if (store.activeCompositionId === compId) {
        store.activeCompositionId =
          store.openCompositionIds[0] || store.project.mainCompositionId;
      }

      storeLogger.debug("Deleted composition:", compId);
      return true;
    },

    /**
     * Rename a composition.
     */
    renameComposition(store: CompositionStoreAccess, compId: string, newName: string): void {
      const comp = store.project.compositions[compId];
      if (comp) comp.name = newName;
    },

    /**
     * Update composition settings.
     */
    updateCompositionSettings(
      store: CompositionStoreAccess,
      compId: string,
      settings: Partial<CompositionSettings>,
    ): void {
      const comp = store.project.compositions[compId];
      if (!comp) return;

      const oldFrameCount = comp.settings.frameCount;

      if (settings.fps !== undefined) {
        settings.fps = validateFps(settings.fps);
      }

      Object.assign(comp.settings, settings);
      comp.settings.duration = comp.settings.frameCount / comp.settings.fps;

      if (settings.frameCount && settings.frameCount > oldFrameCount) {
        for (const layer of comp.layers) {
          if (layer.outPoint === oldFrameCount - 1) {
            layer.outPoint = settings.frameCount - 1;
          }
        }
      }

      if (compId === store.project.mainCompositionId) {
        Object.assign(store.project.composition, comp.settings);
      }

      store.pushHistory();
    },

    /**
     * Enable frame blending for a composition.
     */
    enableFrameBlending(store: CompositionStoreAccess, compId: string): void {
      this.updateCompositionSettings(store, compId, { frameBlendingEnabled: true });
    },

    /**
     * Disable frame blending for a composition.
     */
    disableFrameBlending(store: CompositionStoreAccess, compId: string): void {
      this.updateCompositionSettings(store, compId, { frameBlendingEnabled: false });
    },

    /**
     * Toggle frame blending for a composition.
     */
    toggleFrameBlending(store: CompositionStoreAccess, compId: string): void {
      const comp = store.project.compositions[compId];
      if (!comp) return;
      this.updateCompositionSettings(store, compId, {
        frameBlendingEnabled: !comp.settings.frameBlendingEnabled,
      });
    },

    /**
     * Get a composition by ID.
     */
    getComposition(store: CompositionStoreAccess, compId: string): Composition | null {
      return store.project.compositions[compId] || null;
    },

    // ========================================================================
    // NAVIGATION
    // ========================================================================

    /**
     * Switch to a different composition (tab).
     */
    switchComposition(store: CompositionStoreAccess, compId: string): void {
      if (!store.project.compositions[compId]) {
        storeLogger.warn("Composition not found:", compId);
        return;
      }

      if (!store.openCompositionIds.includes(compId)) {
        store.openCompositionIds.push(compId);
      }

      const selection = useSelectionStore();
      selection.clearLayerSelection();
      selection.clearKeyframeSelection();

      store.activeCompositionId = compId;
      storeLogger.debug("Switched to composition:", compId);
    },

    /**
     * Close a composition tab.
     */
    closeCompositionTab(store: CompositionStoreAccess, compId: string): void {
      if (store.openCompositionIds.length <= 1) {
        storeLogger.warn("Cannot close the last tab");
        return;
      }

      const idx = store.openCompositionIds.indexOf(compId);
      if (idx >= 0) {
        store.openCompositionIds.splice(idx, 1);
      }

      if (store.activeCompositionId === compId) {
        store.activeCompositionId = store.openCompositionIds[Math.max(0, idx - 1)];
      }
    },

    /**
     * Enter a nested comp (double-click on nested comp layer).
     */
    enterNestedComp(store: CompositionStoreAccess, compId: string): void {
      if (!store.project.compositions[compId]) {
        storeLogger.warn("Nested comp not found:", compId);
        return;
      }

      store.compositionBreadcrumbs.push(compId);
      this.switchComposition(store, compId);

      storeLogger.debug("Entered nested comp:", compId, "breadcrumbs:", store.compositionBreadcrumbs);
    },

    /**
     * Navigate back one level in the breadcrumb trail.
     */
    navigateBack(store: CompositionStoreAccess): void {
      if (store.compositionBreadcrumbs.length <= 1) {
        storeLogger.warn("Already at root composition");
        return;
      }

      store.compositionBreadcrumbs.pop();
      const prevId = store.compositionBreadcrumbs[store.compositionBreadcrumbs.length - 1];

      if (prevId) this.switchComposition(store, prevId);
      storeLogger.debug("Navigated back, breadcrumbs:", store.compositionBreadcrumbs);
    },

    /**
     * Navigate to a specific breadcrumb index.
     */
    navigateToBreadcrumb(store: CompositionStoreAccess, index: number): void {
      if (!Number.isInteger(index) || index < 0 || index >= store.compositionBreadcrumbs.length) {
        return;
      }

      if (index === store.compositionBreadcrumbs.length - 1) return;

      store.compositionBreadcrumbs = store.compositionBreadcrumbs.slice(0, index + 1);
      const targetId = store.compositionBreadcrumbs[index];

      if (targetId) this.switchComposition(store, targetId);
      storeLogger.debug("Navigated to breadcrumb", index, "breadcrumbs:", store.compositionBreadcrumbs);
    },

    /**
     * Reset breadcrumbs to main composition.
     */
    resetBreadcrumbs(store: CompositionStoreAccess): void {
      store.compositionBreadcrumbs = [store.project.mainCompositionId];
      this.switchComposition(store, store.project.mainCompositionId);
    },

    // ========================================================================
    // NESTING
    // ========================================================================

    /**
     * Nest selected layers into a new composition.
     */
    nestSelectedLayers(name?: string): Composition | null {
      const projectStore = useProjectStore();
      const selectionStore = useSelectionStore();

      if (selectionStore.selectedLayerIds.length === 0) {
        storeLogger.warn("No layers selected for nesting");
        return null;
      }

      const activeComp = projectStore.project.compositions[projectStore.activeCompositionId];
      if (!activeComp) return null;

      const nestedComp = this.createComposition(
        name || "Nested Comp",
        activeComp.settings,
        true,
      );

      const selectedLayers = activeComp.layers.filter((l) =>
        selectionStore.selectedLayerIds.includes(l.id),
      );

      if (selectedLayers.length === 0) {
        storeLogger.warn("Selected layers not found in active composition");
        return null;
      }

      const earliestIn = Math.min(
        ...selectedLayers.map((l) => l.startFrame ?? l.inPoint ?? 0),
      );

      for (const layer of selectedLayers) {
        const layerStart = layer.startFrame ?? layer.inPoint ?? 0;
        const layerEnd = layer.endFrame ?? layer.outPoint ?? 80;
        layer.startFrame = layerStart - earliestIn;
        layer.endFrame = layerEnd - earliestIn;
        layer.inPoint = layer.startFrame;
        layer.outPoint = layer.endFrame;

        const idx = activeComp.layers.indexOf(layer);
        if (idx >= 0) activeComp.layers.splice(idx, 1);

        nestedComp.layers.push(layer);
      }

      const maxOut = Math.max(
        ...nestedComp.layers.map((l) => l.endFrame ?? l.outPoint ?? 80),
      );
      nestedComp.settings.frameCount = maxOut + 1;
      nestedComp.settings.duration = nestedComp.settings.frameCount / nestedComp.settings.fps;

      const nestedEndFrame = earliestIn + nestedComp.settings.frameCount - 1;
      const nestedCompLayer: Layer = {
        id: `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
        name: nestedComp.name,
        type: "nestedComp",
        visible: true,
        locked: false,
        isolate: false,
        threeD: false,
        startFrame: earliestIn,
        endFrame: nestedEndFrame,
        inPoint: earliestIn,
        outPoint: nestedEndFrame,
        parentId: null,
        transform: createDefaultTransform(),
        opacity: createAnimatableProperty("opacity", 100, "number"),
        properties: [],
        effects: [],
        blendMode: "normal",
        motionBlur: false,
        data: {
          compositionId: nestedComp.id,
          speedMapEnabled: false,
          timeRemapEnabled: false,
          flattenTransform: false,
        } as NestedCompData,
      };

      activeComp.layers.push(nestedCompLayer);

      selectionStore.clearLayerSelection();
      projectStore.activeCompositionId = activeComp.id;

      storeLogger.debug("Nested layers into:", nestedComp.name);
      return nestedComp;
    },
  },
});
