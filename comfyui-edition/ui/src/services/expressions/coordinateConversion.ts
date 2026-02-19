/**
 * Coordinate Conversion Expressions
 *
 * Functions for converting between layer space, composition space, and world space.
 * Also includes lookAt and orientToPath for 3D orientation.
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import { safeDivide } from "@/utils/numericSafety";
import type { ExpressionContext } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // coordinate // conversion // types
// ════════════════════════════════════════════════════════════════════════════

/**
 * Transform matrix interface for coordinate conversion
 */
export interface LayerTransform {
  position: number[];
  scale: number[];
  rotation: number[];
  anchor: number[];
  parent?: LayerTransform | null;
}

// ════════════════════════════════════════════════════════════════════════════
// 3D ORIENTATION FUNCTIONS
// ════════════════════════════════════════════════════════════════════════════

/**
 * lookAt - Calculate rotation to face a target point
 *
 * Returns [xRotation, yRotation, zRotation] in degrees
 *
 * @param fromPoint - Source position [x, y, z]
 * @param toPoint - Target position [x, y, z]
 * @returns Rotation angles [rx, ry, rz] in degrees
 */
export function lookAt(fromPoint: number[], toPoint: number[]): number[] {
  // Type proof: array element access ∈ ℝ ∪ {undefined} → ℝ
  const toPoint0 = toPoint[0];
  const fromPoint0 = fromPoint[0];
  const dx = (isFiniteNumber(toPoint0) ? toPoint0 : 0) - (isFiniteNumber(fromPoint0) ? fromPoint0 : 0);
  const toPoint1 = toPoint[1];
  const fromPoint1 = fromPoint[1];
  const dy = (isFiniteNumber(toPoint1) ? toPoint1 : 0) - (isFiniteNumber(fromPoint1) ? fromPoint1 : 0);
  const toPoint2 = toPoint[2];
  const fromPoint2 = fromPoint[2];
  const dz = (isFiniteNumber(toPoint2) ? toPoint2 : 0) - (isFiniteNumber(fromPoint2) ? fromPoint2 : 0);

  // Calculate yaw (Y rotation) and pitch (X rotation)
  const yaw = (Math.atan2(dx, dz) * 180) / Math.PI;
  const dist = Math.sqrt(dx * dx + dz * dz);
  const pitch = (-Math.atan2(dy, dist) * 180) / Math.PI;

  return [pitch, yaw, 0];
}

/**
 * orientToPath - Auto-orient layer along motion path
 *
 * Given position keyframes, calculates rotation to face movement direction
 */
export function orientToPath(
  ctx: ExpressionContext,
  tangentVector?: number[],
): number[] {
  // If tangent provided, use it directly
  if (tangentVector) {
    const [dx, dy, dz] = tangentVector;
    // Type proof: dx, dy, dz ∈ ℝ ∪ {undefined} → ℝ
    const dxVal = isFiniteNumber(dx) ? dx : 0;
    const dyVal = isFiniteNumber(dy) ? dy : 0;
    const dzVal = isFiniteNumber(dz) ? dz : 1;
    const yaw = (Math.atan2(dxVal, dzVal) * 180) / Math.PI;
    const dist = Math.sqrt(dxVal ** 2 + dzVal ** 2);
    const pitch = (-Math.atan2(dyVal, dist) * 180) / Math.PI;
    return [pitch, yaw, 0];
  }

  // Calculate tangent from velocity
  const vel = ctx.velocity;
  if (Array.isArray(vel) && vel.length >= 2) {
    // Type proof: vel[i] ∈ ℝ ∪ {undefined} → ℝ
    const vel0 = vel[0];
    const dx = isFiniteNumber(vel0) ? vel0 : 0;
    const vel1 = vel[1];
    const dy = isFiniteNumber(vel1) ? vel1 : 0;
    const vel2 = vel[2];
    const dz = isFiniteNumber(vel2) ? vel2 : 1;
    const yaw = (Math.atan2(dx, dz) * 180) / Math.PI;
    const dist = Math.sqrt(dx ** 2 + dz ** 2);
    const pitch = (-Math.atan2(dy, dist) * 180) / Math.PI;
    return [pitch, yaw, 0];
  }

  return [0, 0, 0];
}

// ════════════════════════════════════════════════════════════════════════════
//                                     // coordinate // conversion // functions
// ════════════════════════════════════════════════════════════════════════════

// Maximum recursion depth for parent traversal (prevents stack overflow)
const MAX_PARENT_DEPTH = 50;

/**
 * toComp - Convert point from layer space to composition space
 *
 * @param point - Point in layer coordinates [x, y] or [x, y, z]
 * @param layerTransform - The layer's transform properties
 * @param depth - Current recursion depth (for cycle protection)
 * @returns Point in composition coordinates
 */
export function toComp(
  point: number[],
  layerTransform: LayerTransform,
  depth: number = 0,
): number[] {
  // Guard against circular parent chains
  if (depth > MAX_PARENT_DEPTH) {
    console.warn(
      "[Expressions] Max parent depth exceeded in toComp - possible circular reference",
    );
    return point;
  }

  const [px, py, pz = 0] = point;
  const { position, scale, rotation, anchor } = layerTransform;

  // Apply anchor offset
  // Type proof: anchor[i] ∈ ℝ ∪ {undefined} → ℝ
  const anchor0 = anchor[0];
  let x = px - (isFiniteNumber(anchor0) ? anchor0 : 0);
  const anchor1 = anchor[1];
  let y = py - (isFiniteNumber(anchor1) ? anchor1 : 0);
  const anchor2 = anchor[2];
  let z = pz - (isFiniteNumber(anchor2) ? anchor2 : 0);

  // Apply scale (preserve intentional 0)
  // Type proof: scale[i] ∈ ℝ ∪ {undefined} → ℝ
  const scale0 = scale[0];
  x *= (isFiniteNumber(scale0) ? scale0 : 100) / 100;
  const scale1 = scale[1];
  y *= (isFiniteNumber(scale1) ? scale1 : 100) / 100;
  const scale2 = scale[2];
  z *= (isFiniteNumber(scale2) ? scale2 : 100) / 100;

  // Apply rotation (Z, then Y, then X - matching AE order)
  // Type proof: rotation[i] ∈ ℝ ∪ {undefined} → ℝ
  const rotation2 = rotation[2];
  const rotation0 = rotation[0];
  const rz = ((isFiniteNumber(rotation2) ? rotation2 : (isFiniteNumber(rotation0) ? rotation0 : 0)) * Math.PI) / 180;
  const rotation1 = rotation[1];
  const ry = ((isFiniteNumber(rotation1) ? rotation1 : 0) * Math.PI) / 180;
  const rx = ((isFiniteNumber(rotation0) ? rotation0 : 0) * Math.PI) / 180;

  // Rotate around Z
  const x1 = x * Math.cos(rz) - y * Math.sin(rz);
  const y1 = x * Math.sin(rz) + y * Math.cos(rz);
  const z1 = z;

  // Rotate around Y (3D only)
  const x2 = x1 * Math.cos(ry) + z1 * Math.sin(ry);
  const y2 = y1;
  const z2 = -x1 * Math.sin(ry) + z1 * Math.cos(ry);

  // Rotate around X (3D only)
  let x3 = x2;
  let y3 = y2 * Math.cos(rx) - z2 * Math.sin(rx);
  let z3 = y2 * Math.sin(rx) + z2 * Math.cos(rx);

  // Apply position offset
  // Type proof: position[i] ∈ ℝ ∪ {undefined} → ℝ
  const position0 = position[0];
  x3 += isFiniteNumber(position0) ? position0 : 0;
  const position1 = position[1];
  y3 += isFiniteNumber(position1) ? position1 : 0;
  const position2 = position[2];
  z3 += isFiniteNumber(position2) ? position2 : 0;

  // Recursively apply parent transforms
  if (layerTransform.parent) {
    return toComp([x3, y3, z3], layerTransform.parent, depth + 1);
  }

  return point.length === 2 ? [x3, y3] : [x3, y3, z3];
}

/**
 * fromComp - Convert point from composition space to layer space
 *
 * @param point - Point in composition coordinates [x, y] or [x, y, z]
 * @param layerTransform - The layer's transform properties
 * @param depth - Current recursion depth (for cycle protection)
 * @returns Point in layer coordinates
 */
export function fromComp(
  point: number[],
  layerTransform: LayerTransform,
  depth: number = 0,
): number[] {
  // Guard against circular parent chains
  if (depth > MAX_PARENT_DEPTH) {
    console.warn(
      "[Expressions] Max parent depth exceeded in fromComp - possible circular reference",
    );
    return point;
  }

  let [px, py, pz = 0] = point;

  // First, if there's a parent, convert from comp to parent space
  if (layerTransform.parent) {
    [px, py, pz] = fromComp([px, py, pz], layerTransform.parent, depth + 1);
  }

  const { position, scale, rotation, anchor } = layerTransform;

  // Subtract position
  // Type proof: position[i] ∈ ℝ ∪ {undefined} → ℝ
  const position0 = position[0];
  const x = px - (isFiniteNumber(position0) ? position0 : 0);
  const position1 = position[1];
  const y = py - (isFiniteNumber(position1) ? position1 : 0);
  const position2 = position[2];
  const z = pz - (isFiniteNumber(position2) ? position2 : 0);

  // Inverse rotation (X, then Y, then Z - reverse order)
  // Type proof: rotation[i] ∈ ℝ ∪ {undefined} → ℝ
  const rotation2 = rotation[2];
  const rotation0 = rotation[0];
  const rz = (-(isFiniteNumber(rotation2) ? rotation2 : (isFiniteNumber(rotation0) ? rotation0 : 0)) * Math.PI) / 180;
  const rotation1 = rotation[1];
  const ry = (-(isFiniteNumber(rotation1) ? rotation1 : 0) * Math.PI) / 180;
  const rx = (-(isFiniteNumber(rotation0) ? rotation0 : 0) * Math.PI) / 180;

  // Rotate around X (inverse)
  const x1 = x;
  const y1 = y * Math.cos(rx) - z * Math.sin(rx);
  const z1 = y * Math.sin(rx) + z * Math.cos(rx);

  // Rotate around Y (inverse)
  const x2 = x1 * Math.cos(ry) + z1 * Math.sin(ry);
  const y2 = y1;
  const z2 = -x1 * Math.sin(ry) + z1 * Math.cos(ry);

  // Rotate around Z (inverse)
  let x3 = x2 * Math.cos(rz) - y2 * Math.sin(rz);
  let y3 = x2 * Math.sin(rz) + y2 * Math.cos(rz);
  let z3 = z2;

  // Inverse scale (mathematically rigorous division by zero protection)
  //                                                                    // proven
  // Type proof: scale[i] ∈ ℝ ∪ {undefined} → ℝ
  const scale0 = scale[0];
  const sx = (isFiniteNumber(scale0) ? scale0 : 100) / 100;
  const scale1 = scale[1];
  const sy = (isFiniteNumber(scale1) ? scale1 : 100) / 100;
  const scale2 = scale[2];
  const sz = (isFiniteNumber(scale2) ? scale2 : 100) / 100;
  
  //                                                                    // proven
  // Fallback to 1.0 preserves coordinate (no scaling) when scale is 0
  // This is mathematically correct: inverse of scale 0 is undefined, so we preserve the coordinate
  x3 = safeDivide(x3, sx, x3); // If sx === 0, return x3 unchanged (no inverse scaling)
  y3 = safeDivide(y3, sy, y3); // If sy === 0, return y3 unchanged (no inverse scaling)
  z3 = safeDivide(z3, sz, z3); // If sz === 0, return z3 unchanged (no inverse scaling)

  // Add anchor
  // Type proof: anchor[i] ∈ ℝ ∪ {undefined} → ℝ
  const anchor0 = anchor[0];
  x3 += isFiniteNumber(anchor0) ? anchor0 : 0;
  const anchor1 = anchor[1];
  y3 += isFiniteNumber(anchor1) ? anchor1 : 0;
  const anchor2 = anchor[2];
  z3 += isFiniteNumber(anchor2) ? anchor2 : 0;

  return point.length === 2 ? [x3, y3] : [x3, y3, z3];
}

/**
 * toWorld - Convert point from layer space to world (3D) space
 * Alias for toComp in 3D context
 */
export function toWorld(
  point: number[],
  layerTransform: LayerTransform,
): number[] {
  // Ensure 3D point
  const point3D = point.length === 2 ? [...point, 0] : point;
  return toComp(point3D, layerTransform);
}

/**
 * fromWorld - Convert point from world space to layer space
 * Alias for fromComp in 3D context
 */
export function fromWorld(
  point: number[],
  layerTransform: LayerTransform,
): number[] {
  // Ensure 3D point
  const point3D = point.length === 2 ? [...point, 0] : point;
  return fromComp(point3D, layerTransform);
}

// ════════════════════════════════════════════════════════════════════════════
//                                     // coordinate // conversion // namespace
// ════════════════════════════════════════════════════════════════════════════

/**
 * Coordinate conversion namespace
 */
export const coords = {
  toComp,
  fromComp,
  toWorld,
  fromWorld,
  lookAt,
  orientToPath,
};
