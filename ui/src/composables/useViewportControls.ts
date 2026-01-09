/**
 * Viewport Controls Composable
 *
 * Extracted from ThreeCanvas.vue - handles zoom, pan, and fit operations
 * for the Three.js viewport.
 */

import { computed, type Ref, ref, type ShallowRef } from "vue";
import type { LatticeEngine } from "@/engine/LatticeEngine";

export interface ViewportControlsOptions {
  engine: ShallowRef<LatticeEngine | null>;
  compositionWidth: Ref<number>;
  compositionHeight: Ref<number>;
  canvasWidth: Ref<number>;
  canvasHeight: Ref<number>;
}

export interface ViewportControlsReturn {
  // State
  zoom: Ref<number>;
  viewportTransform: Ref<number[]>;
  zoomLevel: Ref<string>;
  resolution: Ref<"full" | "half" | "third" | "quarter" | "custom">;
  zoomDisplayPercent: Ref<number>;

  // Actions
  zoomIn: () => void;
  zoomOut: () => void;
  setZoom: (newZoom: number) => void;
  fitToView: () => void;
  centerOnComposition: () => void;
  resetCamera: () => void;
  onZoomSelect: () => void;
  onResolutionChange: () => void;

  // Coordinate conversion
  screenToScene: (screenX: number, screenY: number) => { x: number; y: number };
}

export function useViewportControls(
  options: ViewportControlsOptions,
): ViewportControlsReturn {
  const {
    engine,
    compositionWidth,
    compositionHeight,
    canvasWidth,
    canvasHeight,
  } = options;

  // State
  const zoom = ref(1);
  const viewportTransform = ref<number[]>([1, 0, 0, 1, 0, 0]);
  const zoomLevel = ref<string>("fit");
  const resolution = ref<"full" | "half" | "third" | "quarter" | "custom">(
    "full",
  );

  // Computed
  const zoomDisplayPercent = computed(() => Math.round(zoom.value * 100));

  /**
   * Zoom in by 20%
   */
  function zoomIn() {
    const newZoom = Math.min(zoom.value * 1.2, 10);
    zoom.value = newZoom;
    viewportTransform.value[0] = newZoom;
    viewportTransform.value[3] = newZoom;
    if (engine.value) {
      engine.value.setViewportTransform(viewportTransform.value);
    }
  }

  /**
   * Zoom out by 20%
   */
  function zoomOut() {
    const newZoom = Math.max(zoom.value * 0.8, 0.1);
    zoom.value = newZoom;
    viewportTransform.value[0] = newZoom;
    viewportTransform.value[3] = newZoom;
    if (engine.value) {
      engine.value.setViewportTransform(viewportTransform.value);
    }
  }

  /**
   * Set zoom to a specific level (0.1 to 10)
   */
  function setZoom(newZoom: number) {
    newZoom = Math.max(0.1, Math.min(10, newZoom));
    zoom.value = newZoom;
    viewportTransform.value[0] = newZoom;
    viewportTransform.value[3] = newZoom;
    if (engine.value) {
      engine.value.setViewportTransform(viewportTransform.value);
    }
  }

  /**
   * Center the viewport on the composition
   */
  function centerOnComposition() {
    if (!engine.value) return;

    const compW = compositionWidth.value;
    const compH = compositionHeight.value;
    const viewW = canvasWidth.value;
    const viewH = canvasHeight.value;

    if (!compW || !compH || !viewW || !viewH) return;

    // Calculate fit zoom with padding
    const padding = 0.85;
    const fitZoom = Math.min(
      (viewW * padding) / compW,
      (viewH * padding) / compH,
    );

    zoom.value = fitZoom;
    viewportTransform.value[0] = fitZoom;
    viewportTransform.value[3] = fitZoom;

    // Center the composition
    const scaledW = compW * fitZoom;
    const scaledH = compH * fitZoom;
    viewportTransform.value[4] = (viewW - scaledW) / 2;
    viewportTransform.value[5] = (viewH - scaledH) / 2;

    // Update engine camera
    engine.value.getCameraController().setZoom(fitZoom);
    engine.value.getCameraController().setPan(0, 0); // Center
  }

  /**
   * Fit to view (alias for centerOnComposition)
   */
  function fitToView() {
    centerOnComposition();
  }

  /**
   * Reset camera to default 3D viewing position
   */
  function resetCamera() {
    if (engine.value) {
      engine.value.resetCameraToDefault();
      centerOnComposition();
    }
  }

  /**
   * Handle zoom dropdown selection
   */
  function onZoomSelect() {
    if (zoomLevel.value === "fit") {
      fitToView();
    } else {
      const newZoom = parseFloat(zoomLevel.value);
      if (!Number.isNaN(newZoom)) {
        setZoom(newZoom);
        if (engine.value) {
          engine.value.getCameraController().setZoom(newZoom);
        }
      }
    }
  }

  /**
   * Handle resolution dropdown change
   * Note: Resolution changes affect render quality (not implemented in engine yet)
   */
  function onResolutionChange() {
    // Resolution dropdown is currently UI-only
    // Engine setResolution would need to be implemented to affect rendering
    console.log(`[ViewportControls] Resolution changed to ${resolution.value}`);
  }

  /**
   * Convert screen coordinates to scene coordinates
   */
  function screenToScene(
    screenX: number,
    screenY: number,
  ): { x: number; y: number } {
    const vpt = viewportTransform.value;
    return {
      x: (screenX - vpt[4]) / vpt[0],
      y: (screenY - vpt[5]) / vpt[3],
    };
  }

  return {
    // State
    zoom,
    viewportTransform,
    zoomLevel,
    resolution,
    zoomDisplayPercent,

    // Actions
    zoomIn,
    zoomOut,
    setZoom,
    fitToView,
    centerOnComposition,
    resetCamera,
    onZoomSelect,
    onResolutionChange,

    // Coordinate conversion
    screenToScene,
  };
}
