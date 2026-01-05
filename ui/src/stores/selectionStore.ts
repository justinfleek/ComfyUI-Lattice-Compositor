/**
 * Selection Store
 *
 * Manages selection state for layers, keyframes, and properties.
 * This is a focused store extracted from compositorStore for better maintainability.
 */
import { defineStore } from "pinia";
import { storeLogger } from "@/utils/logger";

/** Modifier keys for selection operations */
export interface SelectionModifiers {
  ctrl: boolean;
  shift: boolean;
  alt?: boolean;
}

/** Control point selection info */
export interface ControlPointSelection {
  layerId: string;
  pointIndex: number;
  groupId?: string;
}

interface SelectionState {
  // Layer selection
  selectedLayerIds: string[];

  // Last selected layer (for shift+click range selection)
  lastSelectedLayerId: string | null;

  // Keyframe selection
  selectedKeyframeIds: string[];

  // Control point selection (for spline editing)
  selectedControlPoints: ControlPointSelection[];

  // Property focus (for graph editor)
  selectedPropertyPath: string | null;

  // Tool state
  currentTool: "select" | "pen" | "text" | "hand" | "zoom";
}

export const useSelectionStore = defineStore("selection", {
  state: (): SelectionState => ({
    selectedLayerIds: [],
    lastSelectedLayerId: null,
    selectedKeyframeIds: [],
    selectedControlPoints: [],
    selectedPropertyPath: null,
    currentTool: "select",
  }),

  getters: {
    hasSelection: (state) => state.selectedLayerIds.length > 0,
    hasMultipleSelected: (state) => state.selectedLayerIds.length > 1,
    hasKeyframeSelection: (state) => state.selectedKeyframeIds.length > 0,
    hasControlPointSelection: (state) => state.selectedControlPoints.length > 0,
    singleSelectedLayerId: (state) =>
      state.selectedLayerIds.length === 1 ? state.selectedLayerIds[0] : null,
    selectedControlPointCount: (state) => state.selectedControlPoints.length,
  },

  actions: {
    // ============================================================
    // LAYER SELECTION
    // ============================================================

    /**
     * Select a single layer (replaces current selection)
     */
    selectLayer(layerId: string): void {
      this.selectedLayerIds = [layerId];
      this.lastSelectedLayerId = layerId;
      storeLogger.debug("Selected layer:", layerId);
    },

    /**
     * Select multiple layers (replaces current selection)
     */
    selectLayers(layerIds: string[]): void {
      this.selectedLayerIds = [...layerIds];
      if (layerIds.length > 0) {
        this.lastSelectedLayerId = layerIds[layerIds.length - 1];
      }
      storeLogger.debug("Selected layers:", layerIds.length);
    },

    /**
     * Add layer to selection (multi-select)
     */
    addToSelection(layerId: string): void {
      if (!this.selectedLayerIds.includes(layerId)) {
        this.selectedLayerIds.push(layerId);
        this.lastSelectedLayerId = layerId;
      }
    },

    /**
     * Remove layer from selection
     */
    removeFromSelection(layerId: string): void {
      const index = this.selectedLayerIds.indexOf(layerId);
      if (index >= 0) {
        this.selectedLayerIds.splice(index, 1);
      }
    },

    /**
     * Toggle layer selection
     */
    toggleLayerSelection(layerId: string): void {
      if (this.selectedLayerIds.includes(layerId)) {
        this.removeFromSelection(layerId);
      } else {
        this.addToSelection(layerId);
      }
    },

    /**
     * Select layer with keyboard modifiers (Ctrl/Shift+Click behavior)
     *
     * @param layerId The layer to select
     * @param modifiers Modifier keys state
     * @param orderedLayerIds All layer IDs in order (for shift+click range selection)
     */
    selectLayerWithModifiers(
      layerId: string,
      modifiers: SelectionModifiers,
      orderedLayerIds?: string[],
    ): void {
      if (modifiers.shift && this.lastSelectedLayerId && orderedLayerIds) {
        // Shift+click: Range select
        this.selectRange(this.lastSelectedLayerId, layerId, orderedLayerIds);
      } else if (modifiers.ctrl) {
        // Ctrl+click: Toggle selection
        this.toggleLayerSelection(layerId);
        this.lastSelectedLayerId = layerId;
      } else {
        // Normal click: Replace selection
        this.selectLayer(layerId);
      }
    },

    /**
     * Select a range of layers between two layer IDs
     *
     * @param startLayerId First layer in range
     * @param endLayerId Last layer in range
     * @param orderedLayerIds All layer IDs in display order
     */
    selectRange(
      startLayerId: string,
      endLayerId: string,
      orderedLayerIds: string[],
    ): void {
      const startIndex = orderedLayerIds.indexOf(startLayerId);
      const endIndex = orderedLayerIds.indexOf(endLayerId);

      if (startIndex === -1 || endIndex === -1) {
        // Fallback to single selection if IDs not found
        this.selectLayer(endLayerId);
        return;
      }

      const minIndex = Math.min(startIndex, endIndex);
      const maxIndex = Math.max(startIndex, endIndex);

      this.selectedLayerIds = orderedLayerIds.slice(minIndex, maxIndex + 1);
      this.lastSelectedLayerId = endLayerId;

      storeLogger.debug("Range selected layers:", this.selectedLayerIds.length);
    },

    /**
     * Clear layer selection
     */
    clearLayerSelection(): void {
      this.selectedLayerIds = [];
      this.lastSelectedLayerId = null;
    },

    /**
     * Check if layer is selected
     */
    isLayerSelected(layerId: string): boolean {
      return this.selectedLayerIds.includes(layerId);
    },

    /**
     * Select layer above current selection (Ctrl+Up Arrow behavior)
     * @param orderedLayerIds All layer IDs in display order (top to bottom)
     */
    selectLayerAbove(orderedLayerIds: string[]): void {
      if (orderedLayerIds.length === 0) return;

      // If no selection, select the first (topmost) layer
      if (this.selectedLayerIds.length === 0) {
        this.selectLayer(orderedLayerIds[0]);
        return;
      }

      // Find the topmost selected layer's index
      let minIndex = orderedLayerIds.length;
      for (const selectedId of this.selectedLayerIds) {
        const idx = orderedLayerIds.indexOf(selectedId);
        if (idx !== -1 && idx < minIndex) {
          minIndex = idx;
        }
      }

      // Select the layer above (lower index = higher in stack)
      const aboveIndex = minIndex - 1;
      if (aboveIndex >= 0) {
        this.selectLayer(orderedLayerIds[aboveIndex]);
        storeLogger.debug("Selected layer above:", orderedLayerIds[aboveIndex]);
      }
    },

    /**
     * Select layer below current selection (Ctrl+Down Arrow behavior)
     * @param orderedLayerIds All layer IDs in display order (top to bottom)
     */
    selectLayerBelow(orderedLayerIds: string[]): void {
      if (orderedLayerIds.length === 0) return;

      // If no selection, select the last (bottommost) layer
      if (this.selectedLayerIds.length === 0) {
        this.selectLayer(orderedLayerIds[orderedLayerIds.length - 1]);
        return;
      }

      // Find the bottommost selected layer's index
      let maxIndex = -1;
      for (const selectedId of this.selectedLayerIds) {
        const idx = orderedLayerIds.indexOf(selectedId);
        if (idx !== -1 && idx > maxIndex) {
          maxIndex = idx;
        }
      }

      // Select the layer below (higher index = lower in stack)
      const belowIndex = maxIndex + 1;
      if (belowIndex < orderedLayerIds.length) {
        this.selectLayer(orderedLayerIds[belowIndex]);
        storeLogger.debug("Selected layer below:", orderedLayerIds[belowIndex]);
      }
    },

    // ============================================================
    // KEYFRAME SELECTION
    // ============================================================

    /**
     * Select a single keyframe
     */
    selectKeyframe(keyframeId: string): void {
      this.selectedKeyframeIds = [keyframeId];
    },

    /**
     * Select multiple keyframes
     */
    selectKeyframes(keyframeIds: string[]): void {
      this.selectedKeyframeIds = [...keyframeIds];
    },

    /**
     * Add keyframe to selection
     */
    addKeyframeToSelection(keyframeId: string): void {
      if (!this.selectedKeyframeIds.includes(keyframeId)) {
        this.selectedKeyframeIds.push(keyframeId);
      }
    },

    /**
     * Remove keyframe from selection
     */
    removeKeyframeFromSelection(keyframeId: string): void {
      const index = this.selectedKeyframeIds.indexOf(keyframeId);
      if (index >= 0) {
        this.selectedKeyframeIds.splice(index, 1);
      }
    },

    /**
     * Toggle keyframe selection
     */
    toggleKeyframeSelection(keyframeId: string): void {
      if (this.selectedKeyframeIds.includes(keyframeId)) {
        this.removeKeyframeFromSelection(keyframeId);
      } else {
        this.addKeyframeToSelection(keyframeId);
      }
    },

    /**
     * Clear keyframe selection
     */
    clearKeyframeSelection(): void {
      this.selectedKeyframeIds = [];
    },

    /**
     * Check if keyframe is selected
     */
    isKeyframeSelected(keyframeId: string): boolean {
      return this.selectedKeyframeIds.includes(keyframeId);
    },

    // ============================================================
    // CONTROL POINT SELECTION
    // ============================================================

    /**
     * Select a single control point
     */
    selectControlPoint(
      layerId: string,
      pointIndex: number,
      groupId?: string,
    ): void {
      this.selectedControlPoints = [{ layerId, pointIndex, groupId }];
    },

    /**
     * Select multiple control points
     */
    selectControlPoints(points: ControlPointSelection[]): void {
      this.selectedControlPoints = [...points];
    },

    /**
     * Add control point to selection
     */
    addControlPointToSelection(
      layerId: string,
      pointIndex: number,
      groupId?: string,
    ): void {
      const exists = this.selectedControlPoints.some(
        (p) => p.layerId === layerId && p.pointIndex === pointIndex,
      );
      if (!exists) {
        this.selectedControlPoints.push({ layerId, pointIndex, groupId });
      }
    },

    /**
     * Remove control point from selection
     */
    removeControlPointFromSelection(layerId: string, pointIndex: number): void {
      this.selectedControlPoints = this.selectedControlPoints.filter(
        (p) => !(p.layerId === layerId && p.pointIndex === pointIndex),
      );
    },

    /**
     * Toggle control point selection
     */
    toggleControlPointSelection(
      layerId: string,
      pointIndex: number,
      groupId?: string,
    ): void {
      const index = this.selectedControlPoints.findIndex(
        (p) => p.layerId === layerId && p.pointIndex === pointIndex,
      );
      if (index >= 0) {
        this.selectedControlPoints.splice(index, 1);
      } else {
        this.selectedControlPoints.push({ layerId, pointIndex, groupId });
      }
    },

    /**
     * Select control point with keyboard modifiers
     */
    selectControlPointWithModifiers(
      layerId: string,
      pointIndex: number,
      modifiers: SelectionModifiers,
      groupId?: string,
    ): void {
      if (modifiers.ctrl) {
        this.toggleControlPointSelection(layerId, pointIndex, groupId);
      } else {
        this.selectControlPoint(layerId, pointIndex, groupId);
      }
    },

    /**
     * Select all control points in a group
     * @param groupId The group ID to select
     * @param layerId The layer containing the group
     * @param pointIndicesInGroup All point indices that belong to this group
     */
    selectControlPointGroup(
      groupId: string,
      layerId: string,
      pointIndicesInGroup: number[],
    ): void {
      this.selectedControlPoints = pointIndicesInGroup.map((pointIndex) => ({
        layerId,
        pointIndex,
        groupId,
      }));
      storeLogger.debug(
        "Selected control point group:",
        groupId,
        "points:",
        pointIndicesInGroup.length,
      );
    },

    /**
     * Add all control points in a group to selection
     */
    addControlPointGroupToSelection(
      groupId: string,
      layerId: string,
      pointIndicesInGroup: number[],
    ): void {
      for (const pointIndex of pointIndicesInGroup) {
        const exists = this.selectedControlPoints.some(
          (p) => p.layerId === layerId && p.pointIndex === pointIndex,
        );
        if (!exists) {
          this.selectedControlPoints.push({ layerId, pointIndex, groupId });
        }
      }
    },

    /**
     * Clear control point selection
     */
    clearControlPointSelection(): void {
      this.selectedControlPoints = [];
    },

    /**
     * Check if control point is selected
     */
    isControlPointSelected(layerId: string, pointIndex: number): boolean {
      return this.selectedControlPoints.some(
        (p) => p.layerId === layerId && p.pointIndex === pointIndex,
      );
    },

    /**
     * Get selected control points for a specific layer
     */
    getSelectedControlPointsForLayer(layerId: string): ControlPointSelection[] {
      return this.selectedControlPoints.filter((p) => p.layerId === layerId);
    },

    // ============================================================
    // PROPERTY SELECTION
    // ============================================================

    /**
     * Set selected property path (for graph editor focus)
     */
    setSelectedPropertyPath(path: string | null): void {
      this.selectedPropertyPath = path;
    },

    // ============================================================
    // TOOL STATE
    // ============================================================

    /**
     * Set current tool
     */
    setTool(tool: SelectionState["currentTool"]): void {
      this.currentTool = tool;
    },

    // ============================================================
    // CLEAR ALL
    // ============================================================

    /**
     * Clear all selections
     */
    clearAll(): void {
      this.selectedLayerIds = [];
      this.lastSelectedLayerId = null;
      this.selectedKeyframeIds = [];
      this.selectedControlPoints = [];
      this.selectedPropertyPath = null;
    },
  },
});

export type SelectionStore = ReturnType<typeof useSelectionStore>;
