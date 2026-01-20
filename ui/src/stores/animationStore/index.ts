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
import {
  DEFAULT_SNAP_CONFIG,
  findNearestSnap,
  type SnapConfig,
  type SnapResult,
} from "@/services/timelineSnap";
import { usePlaybackStore } from "../playbackStore";
import { useProjectStore } from "../projectStore";
import { motionEngine } from "@/engine/MotionEngine";
import { useAudioStore } from "../audioStore";
import type { FrameState } from "@/engine/MotionEngine";

// ============================================================================
// MODULE IMPORTS
// ============================================================================

// Types (re-export for consumers)
export type {
  AnimationStoreAccess,
  AnimationState,
  FrameEvaluationAccess,
  SnapPointAccess,
} from "./types";

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
import type {
  AnimationStoreAccess,
  AnimationState,
  FrameEvaluationAccess,
  SnapPointAccess,
} from "./types";

// ============================================================================
// STORE DEFINITION
// ============================================================================

export const useAnimationStore = defineStore("animation", {
  state: (): AnimationState => ({
    loopPlayback: true,
    workAreaStart: null,
    workAreaEnd: null,
    timelineZoom: 1,
    snapConfig: { ...DEFAULT_SNAP_CONFIG },
  }),

  getters: {
    /** Check if work area is defined */
    hasWorkArea: (state) =>
      state.workAreaStart !== null && state.workAreaEnd !== null,

    /** Get effective start frame (work area or 0) */
    effectiveStartFrame: (state) => state.workAreaStart ?? 0,

    /** Whether playback is currently active (delegated to playbackStore) */
    isPlaying(): boolean {
      return usePlaybackStore().isPlaying;
    },

    /** Get current frame from active composition (playback position) */
    currentFrame(): number {
      const projectStore = useProjectStore();
      const comp = projectStore.getActiveComp();
      return comp?.currentFrame ?? 0;
    },
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

    // ========================================================================
    // SNAP CONFIGURATION
    // ========================================================================

    /**
     * Set snap configuration
     */
    setSnapConfig(config: Partial<SnapConfig>): void {
      this.snapConfig = { ...this.snapConfig, ...config };
    },

    /**
     * Toggle snapping on/off
     */
    toggleSnapping(): void {
      this.snapConfig.enabled = !this.snapConfig.enabled;
    },

    /**
     * Toggle specific snap type
     */
    toggleSnapType(
      type:
        | "grid"
        | "keyframes"
        | "beats"
        | "peaks"
        | "layerBounds"
        | "playhead",
    ): void {
      // Type-safe snap toggle mapping
      type BooleanSnapKey =
        | "snapToGrid"
        | "snapToKeyframes"
        | "snapToBeats"
        | "snapToPeaks"
        | "snapToLayerBounds"
        | "snapToPlayhead";
      const typeMap: Record<typeof type, BooleanSnapKey> = {
        grid: "snapToGrid",
        keyframes: "snapToKeyframes",
        beats: "snapToBeats",
        peaks: "snapToPeaks",
        layerBounds: "snapToLayerBounds",
        playhead: "snapToPlayhead",
      };
      const key = typeMap[type];
      this.snapConfig[key] = !this.snapConfig[key];
    },

    // ========================================================================
    // TIMELINE ZOOM
    // ========================================================================

    /**
     * Set timeline zoom level
     * @param zoom Zoom level (0.1 to 10, where 1.0 = 100%)
     */
    setTimelineZoom(zoom: number): void {
      this.timelineZoom = Math.max(0.1, Math.min(10, zoom));
    },

    // ========================================================================
    // FRAME EVALUATION
    // ========================================================================

    /**
     * Get evaluated FrameState for a specific frame
     *
     * This is the CANONICAL way to get evaluated state for rendering.
     * Uses MotionEngine.evaluate() which is PURE and deterministic.
     *
     * @param store - Store with full project and camera access
     * @param frame - Optional frame override (defaults to currentFrame)
     * @returns Immutable FrameState snapshot
     */
    getFrameState(store: FrameEvaluationAccess, frame?: number): FrameState {
      const comp = store.getActiveComp();
      const targetFrame = frame ?? comp?.currentFrame ?? 0;

      // Get audio reactive data from audioStore
      const audioStore = useAudioStore();
      const audioReactive =
        audioStore.audioAnalysis && audioStore.reactiveMappings.length > 0
          ? {
              analysis: audioStore.audioAnalysis,
              mappings: audioStore.reactiveMappings,
            }
          : null;

      return motionEngine.evaluate(
        targetFrame,
        store.project,
        audioStore.audioAnalysis,
        store.activeCameraId,
        true, // useCache
        audioReactive,
      );
    },

    // ========================================================================
    // TIMELINE SNAPPING
    // ========================================================================

    /**
     * Get current time in seconds
     * @param store - Store with composition access
     * @returns Current time in seconds
     */
    getCurrentTime(store: { getActiveComp(): { currentFrame: number; settings: { fps: number } } | null }): number {
      const comp = store.getActiveComp();
      if (!comp) return 0;
      return comp.currentFrame / comp.settings.fps;
    },

    /**
     * Find nearest snap point for a given frame
     * @param store - Store with layer and audio access
     * @param frame - Frame to find snap point for
     * @param pixelsPerFrame - Pixels per frame for snap tolerance calculation
     * @param selectedLayerId - Optional selected layer ID for layer-bound snapping
     * @returns Snap result or null if no snap point found
     */
    findSnapPoint(
      store: SnapPointAccess,
      frame: number,
      pixelsPerFrame: number,
      selectedLayerId?: string | null,
    ): SnapResult | null {
      const audioStore = useAudioStore();
      return findNearestSnap(
        frame,
        this.snapConfig,
        pixelsPerFrame,
        {
          layers: store.layers,
          selectedLayerId,
          currentFrame: store.currentFrame,
          audioAnalysis: audioStore.audioAnalysis,
          peakData: audioStore.peakData,
        },
      );
    },
  },
});

// ============================================================================
// TYPE EXPORTS
// ============================================================================

export type AnimationStoreType = ReturnType<typeof useAnimationStore>;
