/**
 * Layer Time Utilities
 *
 * PURE MODULE - DO NOT MUTATE
 * ==========================
 * All functions in this module are PURE: same inputs = same outputs.
 * No side effects, no global state, no randomness.
 *
 * Provides deterministic calculation of source time from composition time,
 * accounting for:
 * - Time stretch (percentage-based speed)
 * - Reversed playback (negative timeStretch)
 * - Layer startFrame offset
 * - SpeedMap (time remapping via keyframes)
 *
 * DETERMINISM REQUIREMENT:
 * Given the same (compFrame, layer, fps), output MUST be identical
 * regardless of playback history or scrubbing order.
 */

import type { AnimatableProperty, Layer } from "@/types/project";
import { interpolateProperty } from "./interpolation";
import { isFiniteNumber } from "@/utils/typeGuards";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

/**
 * Options for source time calculation
 */
export interface SourceTimeOptions {
  /** Composition frame rate (fps) */
  fps: number;

  /** Optional SpeedMap property for time remapping */
  speedMap?: AnimatableProperty<number>;

  /** Whether SpeedMap is enabled */
  speedMapEnabled?: boolean;

  /** Source duration in frames (for clamping/looping) */
  sourceDuration?: number;

  /** Loop playback when source time exceeds duration */
  loop?: boolean;

  /** Ping-pong loop (reverse at end instead of restart) */
  pingPong?: boolean;
}

/**
 * Result of source time calculation
 */
export interface SourceTimeResult {
  /** Source time in seconds */
  sourceTime: number;

  /** Source frame number */
  sourceFrame: number;

  /** Effective playback speed (1 = normal, 0.5 = half, -1 = reversed) */
  effectiveSpeed: number;

  /** Whether playback is reversed */
  isReversed: boolean;

  /** Whether source time was clamped/looped */
  wasAdjusted: boolean;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                         // core // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Calculate source time from composition frame
 *
 * This is the core function for time remapping. It converts a composition
 * frame number to the corresponding source time/frame, accounting for
 * all time manipulation properties.
 *
 * PURE FUNCTION: Same inputs always produce same outputs.
 *
 * @param compFrame - Current composition frame (0-based)
 * @param layer - Layer containing time properties
 * @param options - Additional options (fps, speedMap, etc.)
 * @returns Source time result with time, frame, and metadata
 */
export function getSourceTime(
  compFrame: number,
  layer: Layer,
  options: SourceTimeOptions,
): SourceTimeResult {
  const {
    fps,
    speedMap,
    speedMapEnabled = false,
    sourceDuration,
    loop = false,
    pingPong = false,
  } = options;

  // Get time stretch (default 100 = normal speed)
  // Type proof: timeStretch ∈ number | undefined → number
  const timeStretch = isFiniteNumber(layer.timeStretch)
    ? layer.timeStretch
    : 100;

  // Calculate effective speed: 100% stretch = 1x speed, 200% = 0.5x, 50% = 2x
  // Formula: effectiveSpeed = 100 / timeStretch
  const effectiveSpeed = timeStretch !== 0 ? 100 / timeStretch : 0;
  const isReversed = timeStretch < 0;
  const absSpeed = Math.abs(effectiveSpeed);

  // If SpeedMap (time remapping) is enabled, use keyframe-driven time
  if (speedMapEnabled && speedMap) {
    const remappedTime = interpolateProperty(speedMap, compFrame, fps);
    return {
      sourceTime: remappedTime,
      sourceFrame: Math.round(remappedTime * fps),
      effectiveSpeed: effectiveSpeed,
      isReversed,
      wasAdjusted: false,
    };
  }

  // Calculate time relative to layer start
  // Type proof: layerStartFrame ∈ number | undefined → number
  const layerStartFrame = isFiniteNumber(layer.startFrame)
    ? Math.floor(layer.startFrame)
    : 0;
  const layerFrame = compFrame - layerStartFrame;

  // Apply time stretch to get source frame
  // layerFrame * absSpeed gives us the source frame offset
  let sourceFrame = layerFrame * absSpeed;

  // Handle reversed playback
  if (isReversed && sourceDuration !== undefined) {
    // Reversed: start from end of source
    sourceFrame = sourceDuration - 1 - sourceFrame;
  }

  // Handle looping/clamping
  let wasAdjusted = false;
  if (sourceDuration !== undefined && sourceDuration > 0) {
    if (loop) {
      if (pingPong) {
        // Ping-pong: 0 -> duration -> 0 -> duration...
        const cycles = Math.floor(sourceFrame / sourceDuration);
        const phase = sourceFrame % sourceDuration;
        if (phase < 0) {
          // Handle negative frames
          sourceFrame = sourceDuration + phase;
        } else if (cycles % 2 === 1) {
          // Odd cycle: reverse
          sourceFrame = sourceDuration - 1 - phase;
        } else {
          sourceFrame = phase;
        }
        wasAdjusted = cycles !== 0;
      } else {
        // Simple loop
        const originalFrame = sourceFrame;
        sourceFrame =
          ((sourceFrame % sourceDuration) + sourceDuration) % sourceDuration;
        wasAdjusted = sourceFrame !== originalFrame;
      }
    } else {
      // Clamp to valid range
      const originalFrame = sourceFrame;
      sourceFrame = Math.max(0, Math.min(sourceFrame, sourceDuration - 1));
      wasAdjusted = sourceFrame !== originalFrame;
    }
  }

  // Ensure non-negative
  sourceFrame = Math.max(0, sourceFrame);

  return {
    sourceTime: sourceFrame / fps,
    sourceFrame: Math.round(sourceFrame),
    effectiveSpeed,
    isReversed,
    wasAdjusted,
  };
}

/**
 * Calculate layer duration after time stretch is applied
 *
 * @param sourceDuration - Original source duration in frames
 * @param timeStretch - Time stretch percentage (100 = normal)
 * @returns Stretched duration in frames
 */
export function getStretchedDuration(
  sourceDuration: number,
  timeStretch: number,
): number {
  if (timeStretch === 0) return sourceDuration;
  // 100% stretch = same duration, 200% = 2x duration, 50% = 0.5x duration
  return Math.round((sourceDuration * Math.abs(timeStretch)) / 100);
}

/**
 * Calculate new layer endpoints after applying time stretch
 *
 * @param layer - Layer to stretch
 * @param newTimeStretch - New time stretch percentage
 * @param anchorFrame - Frame to anchor (optional, defaults to stretchAnchor)
 * @returns New startFrame and endFrame values
 */
export function calculateStretchedEndpoints(
  layer: Layer,
  newTimeStretch: number,
  anchorFrame?: number,
): { startFrame: number; endFrame: number } {
  // Type proof: currentStretch ∈ number | undefined → number
  const currentStretch = isFiniteNumber(layer.timeStretch)
    ? layer.timeStretch
    : 100;
  // Type proof: anchor ∈ string | undefined → string
  const validAnchors: ("startFrame" | "endFrame" | "currentFrame")[] = [
    "startFrame",
    "endFrame",
    "currentFrame",
  ];
  const anchor =
    typeof layer.stretchAnchor === "string" &&
    validAnchors.includes(layer.stretchAnchor as "startFrame" | "endFrame" | "currentFrame")
      ? (layer.stretchAnchor as "startFrame" | "endFrame" | "currentFrame")
      : "startFrame";

  const currentDuration = layer.endFrame - layer.startFrame;
  // Calculate original source duration
  const sourceDuration = (currentDuration * 100) / Math.abs(currentStretch);
  // Calculate new stretched duration
  const newDuration = getStretchedDuration(sourceDuration, newTimeStretch);

  let startFrame = layer.startFrame;
  let endFrame = layer.endFrame;

  if (anchorFrame !== undefined) {
    // Stretch around specific frame
    const ratio = (anchorFrame - layer.startFrame) / currentDuration;
    startFrame = Math.round(anchorFrame - ratio * newDuration);
    endFrame = startFrame + newDuration;
  } else {
    switch (anchor) {
      case "startFrame":
        // Keep start fixed, adjust end
        endFrame = startFrame + newDuration;
        break;
      case "endFrame":
        // Keep end fixed, adjust start
        startFrame = endFrame - newDuration;
        break;
      case "currentFrame": {
        // Stretch around center (default if no specific frame given)
        const center = (layer.startFrame + layer.endFrame) / 2;
        startFrame = Math.round(center - newDuration / 2);
        endFrame = startFrame + newDuration;
        break;
      }
    }
  }

  return { startFrame, endFrame };
}

/**
 * Check if a layer is visible at a given composition frame
 *
 * @param layer - Layer to check
 * @param compFrame - Composition frame
 * @returns True if layer is visible at this frame
 */
export function isLayerVisibleAtFrame(
  layer: Layer,
  compFrame: number,
): boolean {
  // Type proof: start ∈ number | undefined → number
  const start = isFiniteNumber(layer.startFrame)
    ? Math.floor(layer.startFrame)
    : 0;
  // Type proof: end ∈ number | undefined → number
  const end = isFiniteNumber(layer.endFrame)
    ? Math.floor(layer.endFrame)
    : 80;
  return compFrame >= start && compFrame <= end;
}

/**
 * Get the source frame for a video/nested comp layer at a composition frame
 * Convenience wrapper around getSourceTime for common use cases.
 *
 * @param compFrame - Composition frame
 * @param layer - Layer
 * @param fps - Composition FPS
 * @param speedMap - Optional SpeedMap property
 * @param speedMapEnabled - Whether SpeedMap is enabled
 * @param sourceDuration - Source duration in frames (for clamping)
 * @returns Source frame number
 */
export function getSourceFrame(
  compFrame: number,
  layer: Layer,
  fps: number,
  speedMap?: AnimatableProperty<number>,
  speedMapEnabled?: boolean,
  sourceDuration?: number,
): number {
  const result = getSourceTime(compFrame, layer, {
    fps,
    speedMap,
    speedMapEnabled,
    sourceDuration,
  });
  return result.sourceFrame;
}

/**
 * Reverse the time stretch of a layer
 * Toggles between positive and negative timeStretch.
 *
 * @param layer - Layer to reverse
 * @returns New timeStretch value
 */
export function reverseTimeStretch(layer: Layer): number {
  // Type proof: current ∈ number | undefined → number
  const current = isFiniteNumber(layer.timeStretch)
    ? layer.timeStretch
    : 100;
  return -current;
}

/**
 * Check if a layer has reversed playback
 *
 * @param layer - Layer to check
 * @returns True if playback is reversed
 */
export function isReversed(layer: Layer): boolean {
  // Type proof: timeStretch ∈ number | undefined → number
  const timeStretch = isFiniteNumber(layer.timeStretch)
    ? layer.timeStretch
    : 100;
  return timeStretch < 0;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // exports
// ════════════════════════════════════════════════════════════════════════════

export default {
  getSourceTime,
  getStretchedDuration,
  calculateStretchedEndpoints,
  isLayerVisibleAtFrame,
  getSourceFrame,
  reverseTimeStretch,
  isReversed,
};
