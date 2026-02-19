/**
 * UI Store
 *
 * Manages UI state including panel visibility, tool options, and UI preferences.
 * This is a focused store extracted from compositorStore for better maintainability.
 */

import { defineStore } from "pinia";
import type { ClipboardKeyframe, Layer } from "@/types/project";

interface UIState {
  // Panel visibility
  curveEditorVisible: boolean;
  
  // Layer display options
  hideMinimizedLayers: boolean;
  
  // Shape tool options
  shapeToolOptions: {
    fromCenter: boolean;
    constrain: boolean;
    polygonSides: number;
    starPoints: number;
    starInnerRadius: number;
  };

  // Clipboard for copy/paste
  clipboard: {
    layers: Layer[];
    keyframes: ClipboardKeyframe[];
  };
}

export const useUIStore = defineStore("ui", {
  state: (): UIState => ({
    curveEditorVisible: false,
    hideMinimizedLayers: false,
    shapeToolOptions: {
      fromCenter: false,
      constrain: false,
      polygonSides: 6,
      starPoints: 5,
      starInnerRadius: 0.5,
    },
    clipboard: {
      layers: [],
      keyframes: [],
    },
  }),

  getters: {
    /**
     * Get curve editor visibility
     */
    isCurveEditorVisible: (state) => state.curveEditorVisible,

    /**
     * Get hide minimized layers state
     */
    shouldHideMinimizedLayers: (state) => state.hideMinimizedLayers,
  },

  actions: {
    /**
     * Set curve editor visibility
     */
    setCurveEditorVisible(visible: boolean): void {
      this.curveEditorVisible = visible;
    },

    /**
     * Toggle curve editor visibility
     */
    toggleCurveEditorVisible(): void {
      this.curveEditorVisible = !this.curveEditorVisible;
    },

    /**
     * Set hide minimized layers state
     */
    setHideMinimizedLayers(hide: boolean): void {
      this.hideMinimizedLayers = hide;
    },

    /**
     * Toggle hide minimized layers
     */
    toggleHideMinimizedLayers(): void {
      this.hideMinimizedLayers = !this.hideMinimizedLayers;
    },

    /**
     * Update shape tool options
     */
    setShapeToolOptions(options: Partial<UIState["shapeToolOptions"]>): void {
      this.shapeToolOptions = { ...this.shapeToolOptions, ...options };
    },
  },
});
