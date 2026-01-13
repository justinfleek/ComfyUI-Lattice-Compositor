/**
 * Timewarp Evaluation Service
 *
 * Evaluates Timewarp by integrating the animatable speed curve.
 * Unlike SpeedMap (which keyframes source time directly), Timewarp
 * keyframes the SPEED percentage and integrates to find source frame.
 *
 * This allows smooth speed ramps with proper easing curves.
 *
 * Key concepts:
 * - Speed 100% = normal playback (1:1 source to comp frame)
 * - Speed 200% = 2x speed (source advances 2 frames per comp frame)
 * - Speed 50% = 0.5x speed (source advances 0.5 frames per comp frame)
 * - Speed ramp = animate speed with keyframes and easing
 *
 * To find source frame at comp frame T:
 *   sourceFrame = ∫₀ᵀ (speed(t) / 100) dt
 *
 * We approximate this integral using numerical integration.
 */

import type { AnimatableProperty } from "@/types/project";
import { interpolateProperty } from "./interpolation";

/**
 * Result of Timewarp evaluation
 */
export interface TimewarpResult {
  sourceFrame: number; // The source frame to display (may be fractional)
  sourceFrameFloor: number; // Floor of source frame (for frame blending)
  sourceFrameCeil: number; // Ceiling of source frame (for frame blending)
  blendFactor: number; // 0-1 blend between floor and ceil
  instantSpeed: number; // Speed at this exact frame (for UI display)
  effectiveDuration: number; // How many source frames are covered by comp duration
}

/**
 * Evaluate Timewarp at a specific comp frame
 *
 * Integrates the speed curve from layer start to find the source frame.
 * Uses Simpson's rule for accurate numerical integration.
 *
 * @param compFrame - Current composition frame
 * @param layerStartFrame - Layer's start frame in comp
 * @param timewarpSpeed - Animatable speed property (100 = normal)
 * @param compDuration - Total composition duration in frames
 * @returns TimewarpResult with source frame and blend info
 */
export function evaluateTimewarp(
  compFrame: number,
  layerStartFrame: number,
  timewarpSpeed: AnimatableProperty<number>,
  compDuration: number,
): TimewarpResult {
  // Frame relative to layer start
  const relativeFrame = compFrame - layerStartFrame;

  if (relativeFrame <= 0) {
    const speed = interpolateProperty(timewarpSpeed, layerStartFrame) as number;
    return {
      sourceFrame: 0,
      sourceFrameFloor: 0,
      sourceFrameCeil: 0,
      blendFactor: 0,
      instantSpeed: speed,
      effectiveDuration: calculateEffectiveDuration(
        layerStartFrame,
        compDuration,
        timewarpSpeed,
      ),
    };
  }

  // Integrate speed curve from layer start to current frame
  const sourceFrame = integrateSpeedCurve(
    layerStartFrame,
    compFrame,
    timewarpSpeed,
  );

  // Get current speed for UI display
  const instantSpeed = interpolateProperty(timewarpSpeed, compFrame) as number;

  // Calculate blend factors for frame interpolation
  const sourceFrameFloor = Math.floor(sourceFrame);
  const sourceFrameCeil = Math.ceil(sourceFrame);
  const blendFactor = sourceFrame - sourceFrameFloor;

  // Calculate effective source duration
  const effectiveDuration = calculateEffectiveDuration(
    layerStartFrame,
    compDuration,
    timewarpSpeed,
  );

  return {
    sourceFrame,
    sourceFrameFloor,
    sourceFrameCeil,
    blendFactor,
    instantSpeed,
    effectiveDuration,
  };
}

/**
 * Integrate speed curve using Simpson's rule
 *
 * ∫ₐᵇ (speed(t) / 100) dt
 *
 * Simpson's rule: (h/3) * [f(a) + 4*f(a+h) + 2*f(a+2h) + 4*f(a+3h) + ... + f(b)]
 *
 * @param startFrame - Integration start
 * @param endFrame - Integration end
 * @param timewarpSpeed - Speed property to integrate
 * @returns Integrated source frames
 */
function integrateSpeedCurve(
  startFrame: number,
  endFrame: number,
  timewarpSpeed: AnimatableProperty<number>,
): number {
  const frameSpan = endFrame - startFrame;

  // For very short spans, use simple trapezoid
  if (frameSpan < 1) {
    const avgSpeed =
      ((interpolateProperty(timewarpSpeed, startFrame) as number) +
        (interpolateProperty(timewarpSpeed, endFrame) as number)) /
      2 /
      100;
    return frameSpan * avgSpeed;
  }

  // Use adaptive Simpson's rule with at least 1 sample per frame
  const numSamples = Math.max(10, Math.ceil(frameSpan) * 2);
  // Ensure even number for Simpson's rule
  const n = numSamples % 2 === 0 ? numSamples : numSamples + 1;
  const h = frameSpan / n;

  let sum = 0;

  // First point
  sum += (interpolateProperty(timewarpSpeed, startFrame) as number) / 100;

  // Middle points with alternating coefficients (4, 2, 4, 2, ...)
  for (let i = 1; i < n; i++) {
    const t = startFrame + i * h;
    const speed = (interpolateProperty(timewarpSpeed, t) as number) / 100;
    const coeff = i % 2 === 1 ? 4 : 2;
    sum += coeff * speed;
  }

  // Last point
  sum += (interpolateProperty(timewarpSpeed, endFrame) as number) / 100;

  return (h / 3) * sum;
}

/**
 * Calculate how many source frames are covered by the comp duration
 * (Integrates speed from start to end of layer)
 */
function calculateEffectiveDuration(
  layerStartFrame: number,
  compDuration: number,
  timewarpSpeed: AnimatableProperty<number>,
): number {
  return integrateSpeedCurve(layerStartFrame, compDuration, timewarpSpeed);
}

/**
 * Calculate the comp frame where a specific source frame would be displayed
 * (Inverse of evaluateTimewarp - useful for finding keyframe positions)
 *
 * This is more expensive as it requires iterative solving.
 *
 * @param targetSourceFrame - The source frame to find
 * @param layerStartFrame - Layer's start frame in comp
 * @param timewarpSpeed - Speed property
 * @param maxCompFrame - Maximum comp frame to search
 * @returns Comp frame where source frame is displayed, or -1 if not found
 */
export function findCompFrameForSourceFrame(
  targetSourceFrame: number,
  layerStartFrame: number,
  timewarpSpeed: AnimatableProperty<number>,
  maxCompFrame: number,
): number {
  // Binary search for the comp frame
  let low = layerStartFrame;
  let high = maxCompFrame;
  const tolerance = 0.01;

  while (high - low > tolerance) {
    const mid = (low + high) / 2;
    const sourceAtMid = integrateSpeedCurve(
      layerStartFrame,
      mid,
      timewarpSpeed,
    );

    if (sourceAtMid < targetSourceFrame) {
      low = mid;
    } else {
      high = mid;
    }
  }

  return (low + high) / 2;
}

/**
 * Get the speed graph data points for visualization
 * Returns both value (source frame) and velocity (instantaneous speed)
 *
 * @param layerStartFrame - Layer start
 * @param layerEndFrame - Layer end
 * @param timewarpSpeed - Speed property
 * @param sampleRate - Samples per frame (default 1)
 * @returns Arrays of frame numbers, source frames, and speeds
 */
export function getTimewarpGraphData(
  layerStartFrame: number,
  layerEndFrame: number,
  timewarpSpeed: AnimatableProperty<number>,
  sampleRate: number = 1,
): {
  frames: number[];
  sourceFrames: number[];
  speeds: number[];
} {
  const frames: number[] = [];
  const sourceFrames: number[] = [];
  const speeds: number[] = [];

  const step = 1 / sampleRate;
  let cumulativeSource = 0;

  for (let f = layerStartFrame; f <= layerEndFrame; f += step) {
    const speed = interpolateProperty(timewarpSpeed, f) as number;

    frames.push(f);
    speeds.push(speed);

    // Accumulate source frames
    if (f > layerStartFrame) {
      cumulativeSource += (speed / 100) * step;
    }
    sourceFrames.push(cumulativeSource);
  }

  return { frames, sourceFrames, speeds };
}

/**
 * Apply Timewarp to modify layer keyframes
 *
 * When Timewarp is applied, this function can be used to scale
 * the layer's property keyframes to match the new timing.
 *
 * @param keyframes - Original keyframes
 * @param layerStartFrame - Layer start
 * @param timewarpSpeed - Speed property
 * @param maxCompFrame - Max frame to map to
 * @returns New keyframe frames (positions scaled by timewarp)
 */
export function mapKeyframesToTimewarp(
  keyframeFrames: number[],
  layerStartFrame: number,
  timewarpSpeed: AnimatableProperty<number>,
  maxCompFrame: number,
): number[] {
  return keyframeFrames.map((kfFrame) => {
    // Find where this keyframe's SOURCE frame appears in comp time
    const sourceFrame = kfFrame - layerStartFrame;
    return findCompFrameForSourceFrame(
      sourceFrame,
      layerStartFrame,
      timewarpSpeed,
      maxCompFrame,
    );
  });
}

/**
 * Create a speed ramp preset
 * Returns keyframes for common speed ramp patterns
 */
export function createSpeedRampPreset(
  preset: "slow-fast" | "fast-slow" | "slow-fast-slow" | "impact" | "rewind",
  layerStartFrame: number,
  layerDuration: number,
  fps: number = 16,
): AnimatableProperty<number> {
  const midFrame = layerStartFrame + layerDuration / 2;
  const endFrame = layerStartFrame + layerDuration;
  const impactFrame = layerStartFrame + layerDuration * 0.3;

  const baseProperty: AnimatableProperty<number> = {
    id: `prop_timewarp_speed_${Date.now()}`,
    name: "Timewarp Speed",
    value: 100,
    type: "number",
    animated: true,
    keyframes: [],
  };

  switch (preset) {
    case "slow-fast":
      // Start slow, end fast
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 25,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: 20, enabled: true },
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: endFrame,
          value: 200,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: -20, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true },
        },
      ];
      break;

    case "fast-slow":
      // Start fast, end slow
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 200,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: -20, enabled: true },
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: endFrame,
          value: 25,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 20, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true },
        },
      ];
      break;

    case "slow-fast-slow":
      // Slow at edges, fast in middle
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 25,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true },
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: midFrame,
          value: 200,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true },
        },
        {
          id: `kf_${Date.now()}_3`,
          frame: endFrame,
          value: 25,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -10, value: 0, enabled: true },
          outHandle: { frame: 10, value: 0, enabled: true },
        },
      ];
      break;

    case "impact":
      // Normal -> super slow at impact -> normal
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: impactFrame - fps * 0.1,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: 0, enabled: true },
          outHandle: { frame: 3, value: -30, enabled: true },
        },
        {
          id: `kf_${Date.now()}_3`,
          frame: impactFrame,
          value: 10,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: 30, enabled: true },
          outHandle: { frame: 3, value: 30, enabled: true },
        },
        {
          id: `kf_${Date.now()}_4`,
          frame: impactFrame + fps * 0.3,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: -30, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
        },
      ];
      break;

    case "rewind":
      // Normal -> reverse -> normal
      baseProperty.keyframes = [
        {
          id: `kf_${Date.now()}_1`,
          frame: layerStartFrame,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
        },
        {
          id: `kf_${Date.now()}_2`,
          frame: layerStartFrame + layerDuration * 0.3,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 3, value: -50, enabled: true },
        },
        {
          id: `kf_${Date.now()}_3`,
          frame: midFrame,
          value: -150, // Reverse at 1.5x speed
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: 50, enabled: true },
          outHandle: { frame: 3, value: 50, enabled: true },
        },
        {
          id: `kf_${Date.now()}_4`,
          frame: layerStartFrame + layerDuration * 0.7,
          value: 100,
          interpolation: "bezier",
          controlMode: "smooth",
          inHandle: { frame: -3, value: -50, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
        },
      ];
      break;
  }

  return baseProperty;
}

export default {
  evaluateTimewarp,
  findCompFrameForSourceFrame,
  getTimewarpGraphData,
  mapKeyframesToTimewarp,
  createSpeedRampPreset,
};
