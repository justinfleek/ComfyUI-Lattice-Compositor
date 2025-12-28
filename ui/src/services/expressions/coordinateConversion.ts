/**
 * Coordinate Conversion Expressions
 *
 * Functions for converting between layer space, composition space, and world space.
 * Also includes lookAt and orientToPath for 3D orientation.
 */

import type { ExpressionContext } from './types';

// ============================================================
// COORDINATE CONVERSION TYPES
// ============================================================

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

// ============================================================
// 3D ORIENTATION FUNCTIONS
// ============================================================

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
  const dx = (toPoint[0] || 0) - (fromPoint[0] || 0);
  const dy = (toPoint[1] || 0) - (fromPoint[1] || 0);
  const dz = (toPoint[2] || 0) - (fromPoint[2] || 0);

  // Calculate yaw (Y rotation) and pitch (X rotation)
  const yaw = Math.atan2(dx, dz) * 180 / Math.PI;
  const dist = Math.sqrt(dx * dx + dz * dz);
  const pitch = -Math.atan2(dy, dist) * 180 / Math.PI;

  return [pitch, yaw, 0];
}

/**
 * orientToPath - Auto-orient layer along motion path
 *
 * Given position keyframes, calculates rotation to face movement direction
 */
export function orientToPath(
  ctx: ExpressionContext,
  tangentVector?: number[]
): number[] {
  // If tangent provided, use it directly
  if (tangentVector) {
    const [dx, dy, dz] = tangentVector;
    const yaw = Math.atan2(dx || 0, dz || 1) * 180 / Math.PI;
    const dist = Math.sqrt((dx || 0) ** 2 + (dz || 1) ** 2);
    const pitch = -Math.atan2(dy || 0, dist) * 180 / Math.PI;
    return [pitch, yaw, 0];
  }

  // Calculate tangent from velocity
  const vel = ctx.velocity;
  if (Array.isArray(vel) && vel.length >= 2) {
    const dx = vel[0] || 0;
    const dy = vel[1] || 0;
    const dz = vel[2] || 0;
    const yaw = Math.atan2(dx, dz || 1) * 180 / Math.PI;
    const dist = Math.sqrt(dx ** 2 + (dz || 1) ** 2);
    const pitch = -Math.atan2(dy, dist) * 180 / Math.PI;
    return [pitch, yaw, 0];
  }

  return [0, 0, 0];
}

// ============================================================
// COORDINATE CONVERSION FUNCTIONS
// ============================================================

// Maximum recursion depth for parent traversal (BUG-010: prevent stack overflow)
const MAX_PARENT_DEPTH = 50;

/**
 * toComp - Convert point from layer space to composition space
 *
 * @param point - Point in layer coordinates [x, y] or [x, y, z]
 * @param layerTransform - The layer's transform properties
 * @param depth - Current recursion depth (for cycle protection)
 * @returns Point in composition coordinates
 */
export function toComp(point: number[], layerTransform: LayerTransform, depth: number = 0): number[] {
  // Guard against circular parent chains (BUG-010)
  if (depth > MAX_PARENT_DEPTH) {
    console.warn('[Expressions] Max parent depth exceeded in toComp - possible circular reference');
    return point;
  }

  const [px, py, pz = 0] = point;
  const { position, scale, rotation, anchor } = layerTransform;

  // Apply anchor offset
  let x = px - (anchor[0] || 0);
  let y = py - (anchor[1] || 0);
  let z = pz - (anchor[2] || 0);

  // Apply scale (BUG-011: use ?? to preserve intentional 0)
  x *= (scale[0] ?? 100) / 100;
  y *= (scale[1] ?? 100) / 100;
  z *= (scale[2] ?? 100) / 100;

  // Apply rotation (Z, then Y, then X - matching AE order)
  const rz = (rotation[2] || rotation[0] || 0) * Math.PI / 180;
  const ry = (rotation[1] || 0) * Math.PI / 180;
  const rx = (rotation[0] || 0) * Math.PI / 180;

  // Rotate around Z
  let x1 = x * Math.cos(rz) - y * Math.sin(rz);
  let y1 = x * Math.sin(rz) + y * Math.cos(rz);
  let z1 = z;

  // Rotate around Y (3D only)
  let x2 = x1 * Math.cos(ry) + z1 * Math.sin(ry);
  let y2 = y1;
  let z2 = -x1 * Math.sin(ry) + z1 * Math.cos(ry);

  // Rotate around X (3D only)
  let x3 = x2;
  let y3 = y2 * Math.cos(rx) - z2 * Math.sin(rx);
  let z3 = y2 * Math.sin(rx) + z2 * Math.cos(rx);

  // Apply position offset
  x3 += position[0] || 0;
  y3 += position[1] || 0;
  z3 += position[2] || 0;

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
export function fromComp(point: number[], layerTransform: LayerTransform, depth: number = 0): number[] {
  // Guard against circular parent chains (BUG-010)
  if (depth > MAX_PARENT_DEPTH) {
    console.warn('[Expressions] Max parent depth exceeded in fromComp - possible circular reference');
    return point;
  }

  let [px, py, pz = 0] = point;

  // First, if there's a parent, convert from comp to parent space
  if (layerTransform.parent) {
    [px, py, pz] = fromComp([px, py, pz], layerTransform.parent, depth + 1);
  }

  const { position, scale, rotation, anchor } = layerTransform;

  // Subtract position
  let x = px - (position[0] || 0);
  let y = py - (position[1] || 0);
  let z = pz - (position[2] || 0);

  // Inverse rotation (X, then Y, then Z - reverse order)
  const rz = -(rotation[2] || rotation[0] || 0) * Math.PI / 180;
  const ry = -(rotation[1] || 0) * Math.PI / 180;
  const rx = -(rotation[0] || 0) * Math.PI / 180;

  // Rotate around X (inverse)
  let x1 = x;
  let y1 = y * Math.cos(rx) - z * Math.sin(rx);
  let z1 = y * Math.sin(rx) + z * Math.cos(rx);

  // Rotate around Y (inverse)
  let x2 = x1 * Math.cos(ry) + z1 * Math.sin(ry);
  let y2 = y1;
  let z2 = -x1 * Math.sin(ry) + z1 * Math.cos(ry);

  // Rotate around Z (inverse)
  let x3 = x2 * Math.cos(rz) - y2 * Math.sin(rz);
  let y3 = x2 * Math.sin(rz) + y2 * Math.cos(rz);
  let z3 = z2;

  // Inverse scale (BUG-011: use ?? to preserve intentional 0, || 1 guards div/0)
  const sx = (scale[0] ?? 100) / 100;
  const sy = (scale[1] ?? 100) / 100;
  const sz = (scale[2] ?? 100) / 100;
  if (sx === 0 || sy === 0 || sz === 0) {
    console.warn('[Expressions] Scale of 0 in fromComp produces undefined inverse');
  }
  x3 /= sx || 1;
  y3 /= sy || 1;
  z3 /= sz || 1;

  // Add anchor
  x3 += anchor[0] || 0;
  y3 += anchor[1] || 0;
  z3 += anchor[2] || 0;

  return point.length === 2 ? [x3, y3] : [x3, y3, z3];
}

/**
 * toWorld - Convert point from layer space to world (3D) space
 * Alias for toComp in 3D context
 */
export function toWorld(point: number[], layerTransform: LayerTransform): number[] {
  // Ensure 3D point
  const point3D = point.length === 2 ? [...point, 0] : point;
  return toComp(point3D, layerTransform);
}

/**
 * fromWorld - Convert point from world space to layer space
 * Alias for fromComp in 3D context
 */
export function fromWorld(point: number[], layerTransform: LayerTransform): number[] {
  // Ensure 3D point
  const point3D = point.length === 2 ? [...point, 0] : point;
  return fromComp(point3D, layerTransform);
}

// ============================================================
// COORDINATE CONVERSION NAMESPACE
// ============================================================

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
