/**
 * Navigation Actions
 *
 * Frame navigation: goToStart, goToEnd, keyframe jumping.
 */

import { clearMaskPathCacheOnSeek } from "@/services/effects/maskRenderer";
import { clearTimeEffectStateOnSeek } from "@/services/effects/timeRenderer";
import { useKeyframeStore } from "../keyframeStore";
import { useSelectionStore } from "../selectionStore";
import type { AnimationStoreAccess } from "./types";
import { setFrame } from "./playback";

/**
 * Jump to first frame
 */
export function goToStart(store: AnimationStoreAccess): void {
  const comp = store.getActiveComp();
  if (!comp) return;
  if (comp.currentFrame !== 0) {
    clearTimeEffectStateOnSeek();
    clearMaskPathCacheOnSeek();
  }
  comp.currentFrame = 0;
}

/**
 * Jump to last frame
 */
export function goToEnd(store: AnimationStoreAccess): void {
  const comp = store.getActiveComp();
  if (!comp) return;
  const lastFrame = comp.settings.frameCount - 1;
  if (comp.currentFrame !== lastFrame) {
    clearTimeEffectStateOnSeek();
    clearMaskPathCacheOnSeek();
  }
  comp.currentFrame = lastFrame;
}

/**
 * Jump to the next keyframe (K key behavior)
 * @param store Compositor store access
 * @param layerId Optional layer ID. If not provided, uses selected layers or all layers.
 */
export function jumpToNextKeyframe(
  store: AnimationStoreAccess,
  layerId?: string,
): void {
  const layerIds = layerId
    ? [layerId]
    : useSelectionStore().selectedLayerIds.length > 0
      ? useSelectionStore().selectedLayerIds
      : [];

  const nextFrame = useKeyframeStore().findNextKeyframeFrame(
    store,
    store.currentFrame,
    layerIds,
  );

  if (nextFrame !== null) {
    setFrame(store, nextFrame);
  }
}

/**
 * Jump to the previous keyframe (J key behavior)
 * @param store Compositor store access
 * @param layerId Optional layer ID. If not provided, uses selected layers or all layers.
 */
export function jumpToPrevKeyframe(
  store: AnimationStoreAccess,
  layerId?: string,
): void {
  const layerIds = layerId
    ? [layerId]
    : useSelectionStore().selectedLayerIds.length > 0
      ? useSelectionStore().selectedLayerIds
      : [];

  const prevFrame = useKeyframeStore().findPrevKeyframeFrame(
    store,
    store.currentFrame,
    layerIds,
  );

  if (prevFrame !== null) {
    setFrame(store, prevFrame);
  }
}
