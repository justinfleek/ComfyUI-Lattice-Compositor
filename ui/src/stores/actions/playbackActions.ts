/**
 * Playback Actions
 *
 * Handles play/pause, frame navigation, and timeline scrubbing.
 * Extracted from compositorStore.ts for modularity.
 */

import { clearMaskPathCacheOnSeek } from "@/services/effects/maskRenderer";
import { clearTimeEffectStateOnSeek } from "@/services/effects/timeRenderer";
import type { Composition } from "@/types/project";
import { usePlaybackStore } from "../playbackStore";

export interface PlaybackStore {
  isPlaying: boolean;
  getActiveComp(): Composition | null;
}

/**
 * Start playback
 */
export function play(store: PlaybackStore): void {
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

  store.isPlaying = true;
}

/**
 * Pause playback
 */
export function pause(store: PlaybackStore): void {
  const playback = usePlaybackStore();
  playback.stop();
  store.isPlaying = false;
}

/**
 * Toggle playback state
 */
export function togglePlayback(store: PlaybackStore): void {
  const playback = usePlaybackStore();
  if (playback.isPlaying) {
    pause(store);
  } else {
    play(store);
  }
}

/**
 * Set current frame (UI state only)
 * Clears temporal effect state when frame changes non-sequentially.
 */
export function setFrame(store: PlaybackStore, frame: number): void {
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
export function nextFrame(store: PlaybackStore): void {
  const comp = store.getActiveComp();
  if (!comp) return;
  if (comp.currentFrame < comp.settings.frameCount - 1) {
    comp.currentFrame++;
  }
}

/**
 * Go to previous frame
 */
export function prevFrame(store: PlaybackStore): void {
  const comp = store.getActiveComp();
  if (!comp) return;
  if (comp.currentFrame > 0) {
    comp.currentFrame--;
  }
}

/**
 * Jump to first frame
 */
export function goToStart(store: PlaybackStore): void {
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
export function goToEnd(store: PlaybackStore): void {
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
 * Jump forward or backward by N frames
 */
export function jumpFrames(store: PlaybackStore, n: number): void {
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
