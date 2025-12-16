/**
 * Selection Store
 *
 * Manages selection state for layers, keyframes, and properties.
 * This is a focused store extracted from compositorStore for better maintainability.
 */
import { defineStore } from 'pinia';
import { storeLogger } from '@/utils/logger';

interface SelectionState {
  // Layer selection
  selectedLayerIds: string[];

  // Keyframe selection
  selectedKeyframeIds: string[];

  // Property focus (for graph editor)
  selectedPropertyPath: string | null;

  // Tool state
  currentTool: 'select' | 'pen' | 'text' | 'hand' | 'zoom';
}

export const useSelectionStore = defineStore('selection', {
  state: (): SelectionState => ({
    selectedLayerIds: [],
    selectedKeyframeIds: [],
    selectedPropertyPath: null,
    currentTool: 'select',
  }),

  getters: {
    hasSelection: (state) => state.selectedLayerIds.length > 0,
    hasMultipleSelected: (state) => state.selectedLayerIds.length > 1,
    hasKeyframeSelection: (state) => state.selectedKeyframeIds.length > 0,
    singleSelectedLayerId: (state) =>
      state.selectedLayerIds.length === 1 ? state.selectedLayerIds[0] : null,
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
      storeLogger.debug('Selected layer:', layerId);
    },

    /**
     * Select multiple layers (replaces current selection)
     */
    selectLayers(layerIds: string[]): void {
      this.selectedLayerIds = [...layerIds];
      storeLogger.debug('Selected layers:', layerIds.length);
    },

    /**
     * Add layer to selection (multi-select)
     */
    addToSelection(layerId: string): void {
      if (!this.selectedLayerIds.includes(layerId)) {
        this.selectedLayerIds.push(layerId);
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
     * Clear layer selection
     */
    clearLayerSelection(): void {
      this.selectedLayerIds = [];
    },

    /**
     * Check if layer is selected
     */
    isLayerSelected(layerId: string): boolean {
      return this.selectedLayerIds.includes(layerId);
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
    setTool(tool: SelectionState['currentTool']): void {
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
      this.selectedKeyframeIds = [];
      this.selectedPropertyPath = null;
    },
  },
});

export type SelectionStore = ReturnType<typeof useSelectionStore>;
