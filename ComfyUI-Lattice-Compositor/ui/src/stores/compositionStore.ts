/**
 * Composition Store
 *
 * Domain store for composition management including creation, deletion,
 * navigation, breadcrumb trail, and nested composition handling.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { isFiniteNumber } from "@/utils/typeGuards";
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

      // Type proof: fps ∈ ℝ ∪ {undefined} → ℝ
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const settingsFpsValue = (settings != null && typeof settings === "object" && "fps" in settings && typeof settings.fps === "number") ? settings.fps : undefined;
      const activeCompSettings = (activeComp != null && typeof activeComp === "object" && "settings" in activeComp && activeComp.settings != null && typeof activeComp.settings === "object") ? activeComp.settings : undefined;
      const activeCompFpsValue = (activeCompSettings != null && typeof activeCompSettings === "object" && "fps" in activeCompSettings && typeof activeCompSettings.fps === "number") ? activeCompSettings.fps : undefined;
      const rawFps = isFiniteNumber(settingsFpsValue) && settingsFpsValue > 0
        ? settingsFpsValue
        : (isFiniteNumber(activeCompFpsValue) && activeCompFpsValue > 0 ? activeCompFpsValue : DEFAULT_FPS);
      const validFps = validateFps(rawFps);

      // Type proof: width ∈ ℕ ∪ {undefined} → ℕ
      const settingsWidthValue = (settings != null && typeof settings === "object" && "width" in settings && typeof settings.width === "number") ? settings.width : undefined;
      const activeCompWidthValue = (activeCompSettings != null && typeof activeCompSettings === "object" && "width" in activeCompSettings && typeof activeCompSettings.width === "number") ? activeCompSettings.width : undefined;
      const width = isFiniteNumber(settingsWidthValue) && Number.isInteger(settingsWidthValue) && settingsWidthValue > 0
        ? settingsWidthValue
        : (isFiniteNumber(activeCompWidthValue) && Number.isInteger(activeCompWidthValue) && activeCompWidthValue > 0 ? activeCompWidthValue : 1024);
      // Type proof: height ∈ ℕ ∪ {undefined} → ℕ
      const settingsHeightValue = (settings != null && typeof settings === "object" && "height" in settings && typeof settings.height === "number") ? settings.height : undefined;
      const activeCompHeightValue = (activeCompSettings != null && typeof activeCompSettings === "object" && "height" in activeCompSettings && typeof activeCompSettings.height === "number") ? activeCompSettings.height : undefined;
      const height = isFiniteNumber(settingsHeightValue) && Number.isInteger(settingsHeightValue) && settingsHeightValue > 0
        ? settingsHeightValue
        : (isFiniteNumber(activeCompHeightValue) && Number.isInteger(activeCompHeightValue) && activeCompHeightValue > 0 ? activeCompHeightValue : 1024);
      // Type proof: frameCount ∈ ℕ ∪ {undefined} → ℕ
      const settingsFrameCountValue = (settings != null && typeof settings === "object" && "frameCount" in settings && typeof settings.frameCount === "number") ? settings.frameCount : undefined;
      const activeCompFrameCountValue = (activeCompSettings != null && typeof activeCompSettings === "object" && "frameCount" in activeCompSettings && typeof activeCompSettings.frameCount === "number") ? activeCompSettings.frameCount : undefined;
      const frameCount = isFiniteNumber(settingsFrameCountValue) && Number.isInteger(settingsFrameCountValue) && settingsFrameCountValue > 0
        ? settingsFrameCountValue
        : (isFiniteNumber(activeCompFrameCountValue) && Number.isInteger(activeCompFrameCountValue) && activeCompFrameCountValue > 0 ? activeCompFrameCountValue : 81);
      // Type proof: backgroundColor ∈ string | undefined → string
      const backgroundColorValue = (settings != null && typeof settings === "object" && "backgroundColor" in settings && typeof settings.backgroundColor === "string") ? settings.backgroundColor : undefined;
      const backgroundColor = typeof backgroundColorValue === "string" && backgroundColorValue.length > 0 ? backgroundColorValue : "#050505";
      // Type proof: autoResizeToContent ∈ boolean | undefined → boolean
      const autoResizeToContentValue = (settings != null && typeof settings === "object" && "autoResizeToContent" in settings && typeof settings.autoResizeToContent === "boolean") ? settings.autoResizeToContent : undefined;
      const autoResizeToContent = autoResizeToContentValue === true;
      // Type proof: frameBlendingEnabled ∈ boolean | undefined → boolean
      const frameBlendingEnabledValue = (settings != null && typeof settings === "object" && "frameBlendingEnabled" in settings && typeof settings.frameBlendingEnabled === "boolean") ? settings.frameBlendingEnabled : undefined;
      const frameBlendingEnabled = frameBlendingEnabledValue === true;

      const defaultSettings: CompositionSettings = {
        width: width,
        height: height,
        frameCount: frameCount,
        fps: validFps,
        duration: 0,
        backgroundColor: backgroundColor,
        autoResizeToContent: autoResizeToContent,
        frameBlendingEnabled: frameBlendingEnabled,
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
        throw new Error("[CompositionStore] Cannot nest layers: No layers selected");
      }

      const activeComp = projectStore.project.compositions[projectStore.activeCompositionId];
      if (!activeComp) {
        throw new Error("[CompositionStore] Cannot nest layers: No active composition found");
      }

      const nestedComp = this.createComposition(
        name || "Nested Comp",
        activeComp.settings,
        true,
      );

      const selectedLayers = activeComp.layers.filter((l) =>
        selectionStore.selectedLayerIds.includes(l.id),
      );

      if (selectedLayers.length === 0) {
        throw new Error("[CompositionStore] Cannot nest layers: Selected layers not found in active composition");
      }

      // Type proof: earliestIn ∈ ℕ (computed from layer timing)
      const earliestIn = Math.min(
        ...selectedLayers.map((l) => {
          const startFrameValue = l.startFrame;
          const inPointValue = l.inPoint;
          return isFiniteNumber(startFrameValue) && Number.isInteger(startFrameValue) && startFrameValue >= 0
            ? startFrameValue
            : (isFiniteNumber(inPointValue) && Number.isInteger(inPointValue) && inPointValue >= 0 ? inPointValue : 0);
        }),
      );

      for (const layer of selectedLayers) {
        // Type proof: layerStart ∈ ℕ ∪ {undefined} → ℕ
        const startFrameValue = layer.startFrame;
        const inPointValue = layer.inPoint;
        const layerStart = isFiniteNumber(startFrameValue) && Number.isInteger(startFrameValue) && startFrameValue >= 0
          ? startFrameValue
          : (isFiniteNumber(inPointValue) && Number.isInteger(inPointValue) && inPointValue >= 0 ? inPointValue : 0);
        // Type proof: layerEnd ∈ ℕ ∪ {undefined} → ℕ
        const endFrameValue = layer.endFrame;
        const outPointValue = layer.outPoint;
        const layerEnd = isFiniteNumber(endFrameValue) && Number.isInteger(endFrameValue) && endFrameValue >= 0
          ? endFrameValue
          : (isFiniteNumber(outPointValue) && Number.isInteger(outPointValue) && outPointValue >= 0 ? outPointValue : 80);
        layer.startFrame = layerStart - earliestIn;
        layer.endFrame = layerEnd - earliestIn;
        layer.inPoint = layer.startFrame;
        layer.outPoint = layer.endFrame;

        const idx = activeComp.layers.indexOf(layer);
        if (idx >= 0) activeComp.layers.splice(idx, 1);

        nestedComp.layers.push(layer);
      }

      // Type proof: maxOut ∈ ℕ (computed from layer timing)
      const maxOut = Math.max(
        ...nestedComp.layers.map((l) => {
          const endFrameValue = l.endFrame;
          const outPointValue = l.outPoint;
          return isFiniteNumber(endFrameValue) && Number.isInteger(endFrameValue) && endFrameValue >= 0
            ? endFrameValue
            : (isFiniteNumber(outPointValue) && Number.isInteger(outPointValue) && outPointValue >= 0 ? outPointValue : 80);
        }),
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
