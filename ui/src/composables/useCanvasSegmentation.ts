/**
 * Canvas Segmentation Composable
 *
 * Handles point and box-based segmentation interactions on the canvas.
 */

import { ref } from "vue";
import { segmentByBox, segmentByPoint } from "@/services/segmentation";
import { useCompositorStore } from "@/stores/compositorStore";

export interface SegmentBoxState {
  isDrawing: boolean;
  end: { x: number; y: number } | null;
}

export function useCanvasSegmentation() {
  const store = useCompositorStore();

  // State
  const isDrawingSegmentBox = ref(false);
  const segmentBoxEnd = ref<{ x: number; y: number } | null>(null);

  /**
   * Start segment box drawing
   */
  function startSegmentBox(scenePos: { x: number; y: number }) {
    store.setSegmentBoxStart({ x: scenePos.x, y: scenePos.y });
    segmentBoxEnd.value = { x: scenePos.x, y: scenePos.y };
    isDrawingSegmentBox.value = true;
  }

  /**
   * Update segment box end position
   */
  function updateSegmentBox(scenePos: { x: number; y: number }) {
    if (isDrawingSegmentBox.value && store.segmentBoxStart) {
      segmentBoxEnd.value = { x: scenePos.x, y: scenePos.y };
    }
  }

  /**
   * Cancel segment box drawing
   */
  function cancelSegmentBox() {
    isDrawingSegmentBox.value = false;
    store.setSegmentBoxStart(null);
    segmentBoxEnd.value = null;
  }

  /**
   * Finish segment box drawing and trigger segmentation
   */
  async function finishSegmentBox(): Promise<boolean> {
    if (
      !isDrawingSegmentBox.value ||
      !store.segmentBoxStart ||
      !segmentBoxEnd.value
    ) {
      cancelSegmentBox();
      return false;
    }

    const start = store.segmentBoxStart;
    const end = segmentBoxEnd.value;

    // Reset state first
    isDrawingSegmentBox.value = false;
    store.setSegmentBoxStart(null);
    segmentBoxEnd.value = null;

    // Trigger segmentation
    await handleSegmentBox(start.x, start.y, end.x, end.y);
    return true;
  }

  /**
   * Handle point-based segmentation
   */
  async function handleSegmentPoint(x: number, y: number) {
    if (!store.sourceImage) {
      console.warn("[useCanvasSegmentation] No source image for segmentation");
      return;
    }

    store.setSegmentLoading(true);

    try {
      const result = await segmentByPoint(store.sourceImage, { x, y });

      if (
        result.status === "success" &&
        result.masks &&
        result.masks.length > 0
      ) {
        // Set the first (best) mask as pending
        const mask = result.masks[0];
        store.setSegmentPendingMask({
          mask: mask.mask,
          bounds: mask.bounds,
          area: mask.area,
          score: mask.score,
        });
        console.log(
          "[useCanvasSegmentation] Segmentation successful, mask area:",
          mask.area,
        );
      } else {
        console.warn(
          "[useCanvasSegmentation] Segmentation returned no masks:",
          result.message,
        );
      }
    } catch (err) {
      console.error("[useCanvasSegmentation] Segmentation failed:", err);
    } finally {
      store.setSegmentLoading(false);
    }
  }

  /**
   * Handle box-based segmentation
   */
  async function handleSegmentBox(
    x1: number,
    y1: number,
    x2: number,
    y2: number,
  ) {
    if (!store.sourceImage) {
      console.warn("[useCanvasSegmentation] No source image for segmentation");
      return;
    }

    // Normalize box coordinates (ensure x1 < x2, y1 < y2)
    const box: [number, number, number, number] = [
      Math.min(x1, x2),
      Math.min(y1, y2),
      Math.max(x1, x2),
      Math.max(y1, y2),
    ];

    store.setSegmentLoading(true);

    try {
      const result = await segmentByBox(store.sourceImage, box);

      if (
        result.status === "success" &&
        result.masks &&
        result.masks.length > 0
      ) {
        const mask = result.masks[0];
        store.setSegmentPendingMask({
          mask: mask.mask,
          bounds: mask.bounds,
          area: mask.area,
          score: mask.score,
        });
        console.log(
          "[useCanvasSegmentation] Box segmentation successful, mask area:",
          mask.area,
        );
      } else {
        console.warn(
          "[useCanvasSegmentation] Box segmentation returned no masks:",
          result.message,
        );
      }
    } catch (err) {
      console.error("[useCanvasSegmentation] Box segmentation failed:", err);
    } finally {
      store.setSegmentLoading(false);
    }
  }

  /**
   * Compute segment box preview style for overlay
   */
  function getSegmentBoxStyle(viewportTransform: number[]) {
    const start = store.segmentBoxStart;
    const end = segmentBoxEnd.value;
    if (!start || !end) return {};

    const vpt = viewportTransform;

    // Convert to screen coordinates
    const x1 = start.x * vpt[0] + vpt[4];
    const y1 = start.y * vpt[3] + vpt[5];
    const x2 = end.x * vpt[0] + vpt[4];
    const y2 = end.y * vpt[3] + vpt[5];

    return {
      left: `${Math.min(x1, x2)}px`,
      top: `${Math.min(y1, y2)}px`,
      width: `${Math.abs(x2 - x1)}px`,
      height: `${Math.abs(y2 - y1)}px`,
    };
  }

  /**
   * Compute mask overlay style
   */
  function getMaskOverlayStyle(viewportTransform: number[]) {
    const mask = store.segmentPendingMask;
    if (!mask) return {};

    const vpt = viewportTransform;

    // Convert scene coordinates to screen coordinates
    const screenX = mask.bounds.x * vpt[0] + vpt[4];
    const screenY = mask.bounds.y * vpt[3] + vpt[5];
    const screenWidth = mask.bounds.width * vpt[0];
    const screenHeight = mask.bounds.height * vpt[3];

    return {
      left: `${screenX}px`,
      top: `${screenY}px`,
      width: `${screenWidth}px`,
      height: `${screenHeight}px`,
    };
  }

  return {
    // State
    isDrawingSegmentBox,
    segmentBoxEnd,

    // Methods
    startSegmentBox,
    updateSegmentBox,
    cancelSegmentBox,
    finishSegmentBox,
    handleSegmentPoint,
    handleSegmentBox,
    getSegmentBoxStyle,
    getMaskOverlayStyle,
  };
}
