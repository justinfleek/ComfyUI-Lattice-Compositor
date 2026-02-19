/**
 * Expression Helpers Module
 *
 * Utility functions used by various expression modules:
 * - Value interpolation at specific times
 * - Value arithmetic (add, subtract, scale)
 * - Easing application
 */

import type { InterpolationType, Keyframe } from "@/types/project";
import { EASING_FUNCTIONS } from "./easing";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // value // operations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Subtract two values (numbers or arrays)
 */
export function subtractValues(
  a: number | number[],
  b: number | number[],
): number | number[] {
  if (typeof a === "number" && typeof b === "number") {
    return a - b;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v - b[i]);
  }
  return 0;
}

/**
 * Add two values (numbers or arrays)
 */
export function addValues(
  a: number | number[],
  b: number | number[],
): number | number[] {
  if (typeof a === "number" && typeof b === "number") {
    return a + b;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v + b[i]);
  }
  return a;
}

/**
 * Scale a value by a scalar
 */
export function scaleValue(v: number | number[], s: number): number | number[] {
  if (typeof v === "number") {
    return v * s;
  }
  if (Array.isArray(v)) {
    return v.map((x) => x * s);
  }
  return 0;
}

/**
 * Linear interpolation between two values
 */
export function lerpValues(
  a: number | number[],
  b: number | number[],
  t: number,
): number | number[] {
  if (typeof a === "number" && typeof b === "number") {
    return a + (b - a) * t;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v + (b[i] - v) * t);
  }
  return a;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                    // easing // application
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Apply easing function to a t value
 */
export function applyEasing(
  t: number,
  interpolation: InterpolationType,
): number {
  const fn = EASING_FUNCTIONS[interpolation];
  return fn ? fn(t) : t;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                           // time // based // interpolation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Interpolate keyframes at a specific time
 */
export function interpolateAtTime(
  keyframes: Keyframe<number | number[]>[],
  time: number,
  fps: number,
): number | number[] {
  const frame = time * fps;

  // Find surrounding keyframes
  let before: Keyframe<number | number[]> | null = null;
  let after: Keyframe<number | number[]> | null = null;

  for (const kf of keyframes) {
    if (kf.frame <= frame) {
      before = kf;
    } else if (!after) {
      after = kf;
      break;
    }
  }

  if (!before) return keyframes.length > 0 ? keyframes[0].value : 0;
  if (!after) return before.value;

  const frameDelta = after.frame - before.frame;
  if (!Number.isFinite(frameDelta) || frameDelta === 0) return before.value;
  const t = (frame - before.frame) / frameDelta;
  const easedT = applyEasing(t, before.interpolation);

  return lerpValues(before.value, after.value, easedT);
}
