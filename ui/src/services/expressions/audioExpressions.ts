/**
 * Audio Expression Functions
 *
 * Functions for audio-reactive animations including valueAtTime,
 * posterizeTime, and interpolation helpers.
 */

import type { Keyframe } from '@/types/project';
import type { ExpressionContext } from './types';

// ============================================================
// VALUE AT TIME
// ============================================================

/**
 * valueAtTime - Get the value of a property at a specific time
 *
 * This is a core expression function used for audio reactivity.
 * Example: thisComp.layer("Audio Amplitude").effect("Both Channels")("Slider").valueAtTime(time - 0.1)
 *
 * @param ctx - Expression context
 * @param targetTime - The time in seconds to sample
 * @returns The interpolated value at that time
 */
export function valueAtTime(
  ctx: ExpressionContext,
  targetTime: number
): number | number[] {
  const { keyframes, fps, value } = ctx;

  // If no keyframes, return current value
  if (!keyframes || keyframes.length === 0) {
    return value;
  }

  // Convert time to frame
  const targetFrame = targetTime * fps;

  // Find surrounding keyframes
  const sortedKfs = [...keyframes].sort((a, b) => a.frame - b.frame);

  // Before first keyframe
  if (targetFrame <= sortedKfs[0].frame) {
    return sortedKfs[0].value;
  }

  // After last keyframe
  if (targetFrame >= sortedKfs[sortedKfs.length - 1].frame) {
    return sortedKfs[sortedKfs.length - 1].value;
  }

  // Find surrounding keyframes
  let prevKf = sortedKfs[0];
  let nextKf = sortedKfs[1];

  for (let i = 0; i < sortedKfs.length - 1; i++) {
    if (targetFrame >= sortedKfs[i].frame && targetFrame < sortedKfs[i + 1].frame) {
      prevKf = sortedKfs[i];
      nextKf = sortedKfs[i + 1];
      break;
    }
  }

  // Linear interpolation between keyframes
  const t = (targetFrame - prevKf.frame) / (nextKf.frame - prevKf.frame);

  if (typeof prevKf.value === 'number' && typeof nextKf.value === 'number') {
    return prevKf.value + t * (nextKf.value - prevKf.value);
  }

  // Array interpolation
  if (Array.isArray(prevKf.value) && Array.isArray(nextKf.value)) {
    return prevKf.value.map((v, i) =>
      v + t * ((nextKf.value as number[])[i] - v)
    );
  }

  return value;
}

// ============================================================
// POSTERIZE TIME
// ============================================================

/**
 * posterizeTime - Reduce the frame rate of the expression evaluation
 *
 * This is useful for creating a more rhythmic, less smooth animation response.
 * Instead of updating every frame, it only updates at the specified rate.
 *
 * Example:
 *   posterizeTime(12);
 *   amp = thisComp.layer("Audio Amplitude").effect("Both Channels")("Slider");
 *   amp * 5 + 50
 *
 * @param ctx - Expression context
 * @param framesPerSecond - The reduced frame rate to sample at
 * @returns The time quantized to the specified frame rate
 */
export function posterizeTime(
  ctx: ExpressionContext,
  framesPerSecond: number
): number {
  const { time } = ctx;

  // Calculate the interval between samples
  const interval = 1 / framesPerSecond;

  // Quantize time to the nearest interval
  const quantizedTime = Math.floor(time / interval) * interval;

  return quantizedTime;
}

/**
 * Get the posterized frame number
 */
export function posterizedFrame(
  ctx: ExpressionContext,
  framesPerSecond: number
): number {
  const quantizedTime = posterizeTime(ctx, framesPerSecond);
  return Math.floor(quantizedTime * ctx.fps);
}

// ============================================================
// INTERPOLATION FUNCTIONS
// ============================================================

/**
 * linearInterp - Linear interpolation with range mapping
 *
 * Maps a value from one range to another using linear interpolation.
 * Unlike simple lerp, this takes input range and output range.
 *
 * Example:
 *   amp = thisComp.layer("Audio Amplitude").effect("Both Channels")("Slider");
 *   linear(amp, 0, 25, 50, 150)  // Maps amplitude 0-25 to scale 50-150
 *
 * @param t - Input value
 * @param tMin - Input range minimum
 * @param tMax - Input range maximum
 * @param vMin - Output range minimum
 * @param vMax - Output range maximum
 * @returns The mapped value, clamped to output range
 */
export function linearInterp(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number,
  vMax: number
): number {
  // Normalize t to 0-1 range within input range
  const normalized = Math.max(0, Math.min(1, (t - tMin) / (tMax - tMin)));

  // Map to output range
  return vMin + normalized * (vMax - vMin);
}

/**
 * easeInterp - Eased interpolation with range mapping
 *
 * Like linear() but with smooth ease-in-out interpolation.
 * Creates more organic, natural-looking transitions.
 *
 * Example:
 *   amp = thisComp.layer("Audio Amplitude").effect("Both Channels")("Slider");
 *   ease(amp, 0, 25, 50, 150)  // Maps with smooth easing
 *
 * @param t - Input value
 * @param tMin - Input range minimum
 * @param tMax - Input range maximum
 * @param vMin - Output range minimum
 * @param vMax - Output range maximum
 * @returns The eased mapped value, clamped to output range
 */
export function easeInterp(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number,
  vMax: number
): number {
  // Normalize t to 0-1 range within input range
  const normalized = Math.max(0, Math.min(1, (t - tMin) / (tMax - tMin)));

  // Apply smooth ease (cubic ease-in-out)
  const eased = normalized < 0.5
    ? 4 * normalized * normalized * normalized
    : 1 - Math.pow(-2 * normalized + 2, 3) / 2;

  // Map to output range
  return vMin + eased * (vMax - vMin);
}

/**
 * easeIn - Ease-in interpolation with range mapping
 */
export function easeInInterp(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number,
  vMax: number
): number {
  const normalized = Math.max(0, Math.min(1, (t - tMin) / (tMax - tMin)));
  const eased = normalized * normalized * normalized;
  return vMin + eased * (vMax - vMin);
}

/**
 * easeOut - Ease-out interpolation with range mapping
 */
export function easeOutInterp(
  t: number,
  tMin: number,
  tMax: number,
  vMin: number,
  vMax: number
): number {
  const normalized = Math.max(0, Math.min(1, (t - tMin) / (tMax - tMin)));
  const eased = 1 - Math.pow(1 - normalized, 3);
  return vMin + eased * (vMax - vMin);
}

// ============================================================
// AUDIO AMPLITUDE HELPER
// ============================================================

/**
 * Audio amplitude reference helper
 *
 * Creates an expression-friendly reference to the Audio Amplitude layer's slider.
 * This simplifies the common pattern of referencing audio data in expressions.
 *
 * @param keyframes - The slider's keyframes array
 * @param frame - Frame number to sample
 * @param fps - Frames per second
 * @param timeOffset - Optional time offset in seconds
 * @returns The amplitude value at the specified frame
 */
export function audioAmplitude(
  keyframes: Keyframe<number>[],
  frame: number,
  fps: number,
  timeOffset: number = 0
): number {
  if (!keyframes || keyframes.length === 0) return 0;

  // Apply time offset
  const targetFrame = frame - (timeOffset * fps);

  // Find the keyframe at this frame
  const exactKf = keyframes.find(k => k.frame === Math.floor(targetFrame));
  if (exactKf) return exactKf.value;

  // Interpolate between keyframes
  const sortedKfs = [...keyframes].sort((a, b) => a.frame - b.frame);

  if (targetFrame <= sortedKfs[0].frame) return sortedKfs[0].value;
  if (targetFrame >= sortedKfs[sortedKfs.length - 1].frame) {
    return sortedKfs[sortedKfs.length - 1].value;
  }

  // Find surrounding keyframes
  for (let i = 0; i < sortedKfs.length - 1; i++) {
    if (targetFrame >= sortedKfs[i].frame && targetFrame < sortedKfs[i + 1].frame) {
      const t = (targetFrame - sortedKfs[i].frame) / (sortedKfs[i + 1].frame - sortedKfs[i].frame);
      return sortedKfs[i].value + t * (sortedKfs[i + 1].value - sortedKfs[i].value);
    }
  }

  return 0;
}

// ============================================================
// AUDIO NAMESPACE EXPORT
// ============================================================

/**
 * Audio expression namespace - convenient access to all audio functions
 */
export const audio = {
  valueAtTime,
  posterizeTime,
  posterizedFrame,
  linear: linearInterp,
  ease: easeInterp,
  easeIn: easeInInterp,
  easeOut: easeOutInterp,
  amplitude: audioAmplitude,
};
