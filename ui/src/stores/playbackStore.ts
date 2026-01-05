/**
 * Playback Store
 *
 * Manages playback state including play/pause, frame navigation, and scrubbing.
 * This is a focused store extracted from compositorStore for better maintainability.
 */
import { defineStore } from "pinia";
import { validateFps } from "@/utils/fpsUtils";
import { storeLogger } from "@/utils/logger";

interface PlaybackState {
  isPlaying: boolean;
  playbackRequestId: number | null;
  playbackStartTime: number | null;
  playbackStartFrame: number;
  loopPlayback: boolean;
  // Work area bounds (null = use full composition)
  workAreaStart: number | null;
  workAreaEnd: number | null;
}

export const usePlaybackStore = defineStore("playback", {
  state: (): PlaybackState => ({
    isPlaying: false,
    playbackRequestId: null,
    playbackStartTime: null,
    playbackStartFrame: 0,
    loopPlayback: true,
    workAreaStart: null,
    workAreaEnd: null,
  }),

  getters: {
    playing: (state) => state.isPlaying,
    hasWorkArea: (state) =>
      state.workAreaStart !== null && state.workAreaEnd !== null,
    effectiveStartFrame: (state) => state.workAreaStart ?? 0,
    effectiveEndFrame: (state) => (frameCount: number) =>
      state.workAreaEnd ?? frameCount - 1,
  },

  actions: {
    /**
     * Set work area bounds
     */
    setWorkArea(start: number | null, end: number | null): void {
      this.workAreaStart = start;
      this.workAreaEnd = end;
      storeLogger.debug("Work area set:", { start, end });
    },

    /**
     * Clear work area
     */
    clearWorkArea(): void {
      this.workAreaStart = null;
      this.workAreaEnd = null;
      storeLogger.debug("Work area cleared");
    },

    /**
     * Start playback
     * @param fps - Frames per second (must be > 0, validated internally)
     * @param frameCount - Total frame count
     * @param currentFrame - Starting frame
     * @param onFrame - Callback for each frame
     */
    play(
      fps: number,
      frameCount: number,
      currentFrame: number,
      onFrame: (frame: number) => void,
    ): void {
      if (this.isPlaying) return;

      // Validate fps to prevent division by zero
      const validFps = validateFps(fps);

      this.isPlaying = true;
      this.playbackStartTime = performance.now();
      this.playbackStartFrame = currentFrame;

      // Determine effective playback range (work area or full comp)
      const rangeStart = this.workAreaStart ?? 0;
      const rangeEnd = this.workAreaEnd ?? frameCount - 1;
      const rangeLength = rangeEnd - rangeStart + 1;

      // If current frame is outside work area, jump to work area start
      if (this.workAreaStart !== null && this.workAreaEnd !== null) {
        if (currentFrame < rangeStart || currentFrame > rangeEnd) {
          currentFrame = rangeStart;
          onFrame(currentFrame);
        }
      }

      const frameDuration = 1000 / validFps;
      let lastFrameTime = this.playbackStartTime;

      const tick = (now: number) => {
        if (!this.isPlaying) return;

        const elapsed = now - lastFrameTime;
        if (elapsed >= frameDuration) {
          const framesToAdvance = Math.floor(elapsed / frameDuration);
          let newFrame = currentFrame + framesToAdvance;

          // Handle looping or stopping at end of work area / composition
          if (newFrame > rangeEnd) {
            if (this.loopPlayback) {
              // Loop within work area
              newFrame = rangeStart + ((newFrame - rangeStart) % rangeLength);
            } else {
              newFrame = rangeEnd;
              this.stop();
              onFrame(newFrame);
              return;
            }
          }

          currentFrame = newFrame;
          lastFrameTime = now - (elapsed % frameDuration);
          onFrame(currentFrame);
        }

        this.playbackRequestId = requestAnimationFrame(tick);
      };

      this.playbackRequestId = requestAnimationFrame(tick);
      storeLogger.debug(
        "Playback started at frame",
        currentFrame,
        "range:",
        rangeStart,
        "-",
        rangeEnd,
      );
    },

    /**
     * Stop playback
     */
    stop(): void {
      if (this.playbackRequestId !== null) {
        cancelAnimationFrame(this.playbackRequestId);
        this.playbackRequestId = null;
      }
      this.isPlaying = false;
      this.playbackStartTime = null;
      storeLogger.debug("Playback stopped");
    },

    /**
     * Toggle playback
     */
    toggle(
      fps: number,
      frameCount: number,
      currentFrame: number,
      onFrame: (frame: number) => void,
    ): void {
      if (this.isPlaying) {
        this.stop();
      } else {
        this.play(fps, frameCount, currentFrame, onFrame);
      }
    },

    /**
     * Set loop playback mode
     */
    setLoopPlayback(loop: boolean): void {
      this.loopPlayback = loop;
    },

    /**
     * Go to first frame
     */
    goToStart(onFrame: (frame: number) => void): void {
      this.stop();
      onFrame(0);
    },

    /**
     * Go to last frame
     */
    goToEnd(frameCount: number, onFrame: (frame: number) => void): void {
      this.stop();
      onFrame(frameCount - 1);
    },

    /**
     * Step forward one frame
     */
    stepForward(
      currentFrame: number,
      frameCount: number,
      onFrame: (frame: number) => void,
    ): void {
      this.stop();
      const newFrame = Math.min(currentFrame + 1, frameCount - 1);
      onFrame(newFrame);
    },

    /**
     * Step backward one frame
     */
    stepBackward(currentFrame: number, onFrame: (frame: number) => void): void {
      this.stop();
      const newFrame = Math.max(currentFrame - 1, 0);
      onFrame(newFrame);
    },

    /**
     * Jump to specific frame
     */
    goToFrame(
      frame: number,
      frameCount: number,
      onFrame: (frame: number) => void,
    ): void {
      const clampedFrame = Math.max(0, Math.min(frame, frameCount - 1));
      onFrame(clampedFrame);
    },
  },
});

export type PlaybackStore = ReturnType<typeof usePlaybackStore>;
