/**
 * Animation Store
 *
 * Domain store for playback, frame navigation, and timeline control.
 *
 * MODULE STRUCTURE:
 * - types.ts: Type definitions and interfaces
 * - playback.ts: play, pause, toggle, setFrame, nextFrame, prevFrame
 * - navigation.ts: goToStart, goToEnd, jumpToNextKeyframe, jumpToPrevKeyframe
 */

import { defineStore } from "pinia";

// ============================================================================
// MODULE IMPORTS
// ============================================================================

// Types (re-export for consumers)
export type { AnimationStoreAccess, AnimationState } from "./types";

// Playback operations
import {
  play as playImpl,
  pause as pauseImpl,
  togglePlayback as togglePlaybackImpl,
  setFrame as setFrameImpl,
  nextFrame as nextFrameImpl,
  prevFrame as prevFrameImpl,
  jumpFrames as jumpFramesImpl,
} from "./playback";

// Navigation operations
import {
  goToStart as goToStartImpl,
  goToEnd as goToEndImpl,
  jumpToNextKeyframe as jumpToNextKeyframeImpl,
  jumpToPrevKeyframe as jumpToPrevKeyframeImpl,
} from "./navigation";

// Types for internal use
import type { AnimationStoreAccess, AnimationState } from "./types";

// ============================================================================
// STORE DEFINITION
// ============================================================================

export const useAnimationStore = defineStore("animation", {
  state: (): AnimationState => ({
    loopPlayback: true,
    workAreaStart: null,
    workAreaEnd: null,
  }),

  getters: {
    /** Check if work area is defined */
    hasWorkArea: (state) =>
      state.workAreaStart !== null && state.workAreaEnd !== null,

    /** Get effective start frame (work area or 0) */
    effectiveStartFrame: (state) => state.workAreaStart ?? 0,
  },

  actions: {
    // ========================================================================
    // WORK AREA
    // ========================================================================

    /**
     * Set work area bounds
     */
    setWorkArea(start: number | null, end: number | null): void {
      this.workAreaStart = start;
      this.workAreaEnd = end;
    },

    /**
     * Clear work area
     */
    clearWorkArea(): void {
      this.workAreaStart = null;
      this.workAreaEnd = null;
    },

    /**
     * Set loop playback mode
     */
    setLoopPlayback(loop: boolean): void {
      this.loopPlayback = loop;
    },

    // ========================================================================
    // PLAYBACK CONTROLS
    // ========================================================================

    /**
     * Start playback
     */
    play(store: AnimationStoreAccess): void {
      playImpl(store);
    },

    /**
     * Pause playback
     */
    pause(store: AnimationStoreAccess): void {
      pauseImpl(store);
    },

    /**
     * Toggle playback state
     */
    togglePlayback(store: AnimationStoreAccess): void {
      togglePlaybackImpl(store);
    },

    /**
     * Set current frame
     */
    setFrame(store: AnimationStoreAccess, frame: number): void {
      setFrameImpl(store, frame);
    },

    /**
     * Advance to next frame
     */
    nextFrame(store: AnimationStoreAccess): void {
      nextFrameImpl(store);
    },

    /**
     * Go to previous frame
     */
    prevFrame(store: AnimationStoreAccess): void {
      prevFrameImpl(store);
    },

    /**
     * Jump forward or backward by N frames
     */
    jumpFrames(store: AnimationStoreAccess, n: number): void {
      jumpFramesImpl(store, n);
    },

    // ========================================================================
    // NAVIGATION
    // ========================================================================

    /**
     * Jump to first frame
     */
    goToStart(store: AnimationStoreAccess): void {
      goToStartImpl(store);
    },

    /**
     * Jump to last frame
     */
    goToEnd(store: AnimationStoreAccess): void {
      goToEndImpl(store);
    },

    /**
     * Jump to the next keyframe (K key behavior)
     */
    jumpToNextKeyframe(store: AnimationStoreAccess, layerId?: string): void {
      jumpToNextKeyframeImpl(store, layerId);
    },

    /**
     * Jump to the previous keyframe (J key behavior)
     */
    jumpToPrevKeyframe(store: AnimationStoreAccess, layerId?: string): void {
      jumpToPrevKeyframeImpl(store, layerId);
    },

    // ========================================================================
    // GETTERS (delegated to store for convenience)
    // ========================================================================

    /**
     * Get current frame from active composition
     */
    getCurrentFrame(store: AnimationStoreAccess): number {
      return store.currentFrame;
    },

    /**
     * Get frame count from active composition
     */
    getFrameCount(store: AnimationStoreAccess): number {
      return store.frameCount;
    },

    /**
     * Get FPS from active composition
     */
    getFps(store: AnimationStoreAccess): number {
      return store.fps;
    },

    /**
     * Get effective end frame (work area or frameCount - 1)
     */
    getEffectiveEndFrame(store: AnimationStoreAccess): number {
      return this.workAreaEnd ?? store.frameCount - 1;
    },
  },
});

// ============================================================================
// TYPE EXPORTS
// ============================================================================

export type AnimationStoreType = ReturnType<typeof useAnimationStore>;
