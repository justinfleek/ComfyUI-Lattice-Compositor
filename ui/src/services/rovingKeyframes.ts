/**
 * Roving Keyframes Service
 *
 * @module rovingKeyframes
 * @description
 * Implements roving (floating) keyframes that automatically redistribute timing
 * along a motion path to achieve constant velocity. When enabled, keyframe times
 * are determined by their spatial position rather than explicit frame numbers.
 *
 * **How it works:**
 * 1. Calculate total arc length of the motion path
 * 2. For each intermediate keyframe, find its position as percentage of path
 * 3. Redistribute frame times so motion is uniform speed
 *
 * **Usage:**
 * - Apply to position keyframes to get smooth, constant-speed motion
 * - First and last keyframes are anchored (their frames don't change)
 * - Intermediate keyframes "rove" to maintain even spacing
 *
 * @example
 * ```typescript
 * import { applyRovingKeyframes } from './rovingKeyframes';
 *
 * // Apply roving to position property
 * const newKeyframes = applyRovingKeyframes(positionKeyframes);
 * ```
 */

import * as THREE from "three";
import type { Keyframe } from "@/types/project";

/** Position can be either an array [x, y, z] or an object {x, y, z} */
export type PositionValue = number[] | { x: number; y: number; z?: number };

/** Extract x, y, z from either position format */
function extractXYZ(value: PositionValue): [number, number, number] {
  if (Array.isArray(value)) {
    return [value[0] || 0, value[1] || 0, value[2] || 0];
  }
  return [value.x || 0, value.y || 0, value.z || 0];
}

export interface RovingOptions {
  /**
   * Whether to preserve the first keyframe's frame number
   * @default true
   */
  anchorFirst?: boolean;

  /**
   * Whether to preserve the last keyframe's frame number
   * @default true
   */
  anchorLast?: boolean;

  /**
   * Minimum number of keyframes required for roving
   * @default 3
   */
  minKeyframes?: number;
}

export interface RovingResult<T extends PositionValue = PositionValue> {
  /** Updated keyframes with redistributed frame numbers */
  keyframes: Keyframe<T>[];
  /** Total arc length of the motion path */
  totalLength: number;
  /** Arc length at each keyframe position */
  segmentLengths: number[];
  /** Whether roving was applied successfully */
  success: boolean;
  /** Error message if roving failed */
  error?: string;
}

/**
 * Calculate arc length between two 3D points along a cubic bezier curve
 * Uses linear interpolation for simplicity (can upgrade to bezier if needed)
 */
function calculateSegmentLength(p1: PositionValue, p2: PositionValue): number {
  const [x1, y1, z1] = extractXYZ(p1);
  const [x2, y2, z2] = extractXYZ(p2);
  const dx = x2 - x1;
  const dy = y2 - y1;
  const dz = z2 - z1;
  return Math.sqrt(dx * dx + dy * dy + dz * dz);
}

/**
 * Build a Three.js curve path from position keyframes
 */
function buildCurvePath(
  keyframes: Keyframe<PositionValue>[],
): THREE.CurvePath<THREE.Vector3> {
  const path = new THREE.CurvePath<THREE.Vector3>();

  for (let i = 0; i < keyframes.length - 1; i++) {
    const curr = keyframes[i];
    const next = keyframes[i + 1];

    const [cx, cy, cz] = extractXYZ(curr.value);
    const [nx, ny, nz] = extractXYZ(next.value);

    const p0 = new THREE.Vector3(cx, cy, cz);
    const p3 = new THREE.Vector3(nx, ny, nz);

    // For bezier interpolation, calculate control points at 1/3 intervals
    // This creates a smooth catmull-rom like curve
    const dx = p3.x - p0.x;
    const dy = p3.y - p0.y;
    const dz = p3.z - p0.z;

    const p1 = new THREE.Vector3(
      p0.x + dx * 0.33,
      p0.y + dy * 0.33,
      p0.z + dz * 0.33,
    );
    const p2 = new THREE.Vector3(
      p0.x + dx * 0.66,
      p0.y + dy * 0.66,
      p0.z + dz * 0.66,
    );

    const curve = new THREE.CubicBezierCurve3(p0, p1, p2, p3);
    path.add(curve);
  }

  return path;
}

/**
 * Apply roving keyframes to redistribute timing based on arc length
 *
 * Roving keyframes maintain constant speed along a motion path by
 * automatically adjusting intermediate keyframe times based on their
 * spatial position along the path.
 *
 * @param keyframes - Array of position keyframes (Vec3 as number[] or {x,y,z} object)
 * @param options - Roving options
 * @returns Updated keyframes with redistributed frame numbers
 */
export function applyRovingKeyframes<T extends PositionValue>(
  keyframes: Keyframe<T>[],
  options: RovingOptions = {},
): RovingResult<T> {
  const { anchorFirst = true, anchorLast = true, minKeyframes = 3 } = options;

  // Validate input
  if (!keyframes || keyframes.length < minKeyframes) {
    return {
      keyframes,
      totalLength: 0,
      segmentLengths: [],
      success: false,
      error: `Roving requires at least ${minKeyframes} keyframes`,
    };
  }

  // Sort keyframes by frame number
  const sorted = [...keyframes].sort((a, b) => a.frame - b.frame);

  // Get anchor frames
  const firstFrame = sorted[0].frame;
  const lastFrame = sorted[sorted.length - 1].frame;
  const totalFrames = lastFrame - firstFrame;

  if (totalFrames <= 0) {
    return {
      keyframes: sorted,
      totalLength: 0,
      segmentLengths: [],
      success: false,
      error: "First and last keyframes must have different frame numbers",
    };
  }

  // Build curve path and calculate total length
  const curvePath = buildCurvePath(sorted);
  const totalLength = curvePath.getLength();

  if (totalLength <= 0) {
    return {
      keyframes: sorted,
      totalLength: 0,
      segmentLengths: [],
      success: false,
      error: "Motion path has zero length",
    };
  }

  // Calculate cumulative arc lengths at each keyframe position
  const segmentLengths: number[] = [0];
  let cumulativeLength = 0;

  for (let i = 1; i < sorted.length; i++) {
    const segmentLength = calculateSegmentLength(
      sorted[i - 1].value,
      sorted[i].value,
    );
    cumulativeLength += segmentLength;
    segmentLengths.push(cumulativeLength);
  }

  // Redistribute frame times based on arc length percentage
  const newKeyframes = sorted.map((kf, index) => {
    // Clone the keyframe
    const newKf = { ...kf };

    // First and last keyframes stay anchored
    if (index === 0 && anchorFirst) {
      return newKf;
    }
    if (index === sorted.length - 1 && anchorLast) {
      return newKf;
    }

    // Calculate arc length percentage
    const arcLengthPercent = segmentLengths[index] / totalLength;

    // Map to frame number
    newKf.frame = Math.round(firstFrame + arcLengthPercent * totalFrames);

    return newKf;
  });

  return {
    keyframes: newKeyframes,
    totalLength,
    segmentLengths,
    success: true,
  };
}

/**
 * Check if roving would change keyframe timing significantly
 *
 * @param keyframes - Position keyframes to check
 * @param threshold - Maximum frame difference to consider "similar" timing
 * @returns true if roving would make significant changes
 */
export function wouldRovingChange(
  keyframes: Keyframe<PositionValue>[],
  threshold: number = 2,
): boolean {
  if (keyframes.length < 3) return false;

  const result = applyRovingKeyframes(keyframes);
  if (!result.success) return false;

  // Compare original vs roving frames
  for (let i = 0; i < keyframes.length; i++) {
    const original = keyframes[i].frame;
    const roving = result.keyframes[i].frame;
    if (Math.abs(original - roving) > threshold) {
      return true;
    }
  }

  return false;
}

/**
 * Get frame times for evenly spaced positions along motion path
 *
 * @param keyframes - Position keyframes defining the path
 * @param numPoints - Number of evenly spaced points
 * @returns Array of frame numbers for evenly spaced positions
 */
export function getEvenlySpacedFrames(
  keyframes: Keyframe<PositionValue>[],
  numPoints: number,
): number[] {
  if (keyframes.length < 2 || numPoints < 2) {
    return [];
  }

  const sorted = [...keyframes].sort((a, b) => a.frame - b.frame);
  const firstFrame = sorted[0].frame;
  const lastFrame = sorted[sorted.length - 1].frame;

  // For simplicity, just return linearly spaced frames
  // A more sophisticated implementation would use actual arc-length
  const frames: number[] = [];
  for (let i = 0; i < numPoints; i++) {
    const t = i / (numPoints - 1);
    frames.push(Math.round(firstFrame + t * (lastFrame - firstFrame)));
  }

  return frames;
}

/**
 * Calculate velocity at each keyframe based on current timing
 *
 * @param keyframes - Position keyframes
 * @param fps - Frames per second
 * @returns Array of velocity magnitudes at each keyframe
 */
export function calculateVelocities(
  keyframes: Keyframe<PositionValue>[],
  fps: number = 16,
): number[] {
  if (keyframes.length < 2) return [];

  const sorted = [...keyframes].sort((a, b) => a.frame - b.frame);
  const velocities: number[] = [];

  for (let i = 0; i < sorted.length; i++) {
    if (i === 0) {
      // First keyframe: use forward difference
      const dt = (sorted[1].frame - sorted[0].frame) / fps;
      if (dt <= 0) {
        velocities.push(0);
      } else {
        const distance = calculateSegmentLength(
          sorted[0].value,
          sorted[1].value,
        );
        velocities.push(distance / dt);
      }
    } else if (i === sorted.length - 1) {
      // Last keyframe: use backward difference
      const dt = (sorted[i].frame - sorted[i - 1].frame) / fps;
      if (dt <= 0) {
        velocities.push(0);
      } else {
        const distance = calculateSegmentLength(
          sorted[i - 1].value,
          sorted[i].value,
        );
        velocities.push(distance / dt);
      }
    } else {
      // Middle keyframes: use central difference
      const dt1 = (sorted[i].frame - sorted[i - 1].frame) / fps;
      const dt2 = (sorted[i + 1].frame - sorted[i].frame) / fps;
      const d1 = calculateSegmentLength(sorted[i - 1].value, sorted[i].value);
      const d2 = calculateSegmentLength(sorted[i].value, sorted[i + 1].value);

      // Average velocity
      const v1 = dt1 > 0 ? d1 / dt1 : 0;
      const v2 = dt2 > 0 ? d2 / dt2 : 0;
      velocities.push((v1 + v2) / 2);
    }
  }

  return velocities;
}
