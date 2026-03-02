/**
 * Playback Actions
 *
 * Core playback operations: play, pause, toggle, frame stepping.
 */

import { clearMaskPathCacheOnSeek } from "@/services/effects/maskRenderer";
import { clearTimeEffectStateOnSeek } from "@/services/effects/timeRenderer";
import { usePlaybackStore } from "../playbackStore";
import type { AnimationStoreAccess } from "./types";

/**
 * Start playback
 */
export function play(store: AnimationStoreAccess): void {
  const playback = usePlaybackStore();
  if (playback.isPlaying) return;

  const comp = store.getActiveComp();
  if (!comp) return;

  playback.play(
    comp.settings.fps,
    comp.settings.frameCount,
    comp.currentFrame,
    (frame: number) => {
      comp.currentFrame = frame;
    },
  );

  // Note: playbackStore.isPlaying is already set to true by playback.play()
}

/**
 * Pause playback
 */
export function pause(store: AnimationStoreAccess): void {
  const playback = usePlaybackStore();
  playback.stop();
  // Note: playbackStore.isPlaying is already set to false by playback.stop()
}

/**
 * Toggle playback state
 */
export function togglePlayback(store: AnimationStoreAccess): void {
  const playback = usePlaybackStore();
  if (playback.isPlaying) {
    pause(store);
  } else {
    play(store);
  }
}

/**
 * Set current frame
 * Clears temporal effect state when frame changes non-sequentially.
 */
export function setFrame(store: AnimationStoreAccess, frame: number): void {
  const comp = store.getActiveComp();
  if (!comp) return;

  // Validate frame (NaN bypasses Math.max/min)
  if (!Number.isFinite(frame)) return;

  const newFrame = Math.max(0, Math.min(frame, comp.settings.frameCount - 1));

  // Clear temporal state if frame changes by more than 1 (non-sequential)
  const frameDelta = Math.abs(newFrame - comp.currentFrame);
  if (frameDelta > 1) {
    clearTimeEffectStateOnSeek();
    clearMaskPathCacheOnSeek();
  }

  comp.currentFrame = newFrame;
}

/**
 * Advance to next frame
 */
export function nextFrame(store: AnimationStoreAccess): void {
  const comp = store.getActiveComp();
  if (!comp) return;
  if (comp.currentFrame < comp.settings.frameCount - 1) {
    comp.currentFrame++;
  }
}

/**
 * Go to previous frame
 */
export function prevFrame(store: AnimationStoreAccess): void {
  const comp = store.getActiveComp();
  if (!comp) return;
  if (comp.currentFrame > 0) {
    comp.currentFrame--;
  }
}

/**
 * Jump forward or backward by N frames
 */
export function jumpFrames(store: AnimationStoreAccess, n: number): void {
  const comp = store.getActiveComp();
  if (!comp) return;

  // Validate n (NaN bypasses Math.max/min)
  if (!Number.isFinite(n)) return;

  const newFrame = Math.max(
    0,
    Math.min(comp.currentFrame + n, comp.settings.frameCount - 1),
  );
  if (Math.abs(n) > 1) {
    clearTimeEffectStateOnSeek();
    clearMaskPathCacheOnSeek();
  }
  comp.currentFrame = newFrame;
}
