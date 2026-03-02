/**
 * Mesh Warp Schemas
 *
 * Zod schemas for mesh deformation pins and meshes.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  finiteNumber,
  normalized01,
  positiveFinite,
} from "../layers/primitives-schema";
import { AnimatablePropertySchema } from "../layers/animation-schema";
import {
  entityId,
  boundedArray,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ============================================================================
// Warp Pin Type
// ============================================================================

export const WarpPinTypeSchema = z.enum([
  "position",
  "rotation",
  "starch",
  "overlap",
  "bend",
  "advanced",
]);

export type WarpPinType = z.infer<typeof WarpPinTypeSchema>;

// ============================================================================
// Position 2D
// ============================================================================

const Position2DSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
}).strict();

// ============================================================================
// Warp Pin
// ============================================================================

export const WarpPinSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: WarpPinTypeSchema,
  position: AnimatablePropertySchema,
  radius: positiveFinite.max(10000), // Max reasonable radius
  stiffness: normalized01,
  rotation: AnimatablePropertySchema,
  scale: AnimatablePropertySchema,
  depth: finiteNumber.max(10000).min(-10000), // Max reasonable depth
  selected: z.boolean().optional(),
  inFront: AnimatablePropertySchema.optional(),
}).strict();

export type WarpPin = z.infer<typeof WarpPinSchema>;

// ============================================================================
// Warp Pin Rest State
// ============================================================================

export const WarpPinRestStateSchema = z.object({
  pinId: entityId,
  position: Position2DSchema,
  rotation: finiteNumber,
  scale: positiveFinite.max(100), // Max reasonable scale
  inFront: finiteNumber.optional(),
}).strict();

export type WarpPinRestState = z.infer<typeof WarpPinRestStateSchema>;

// ============================================================================
// Warp Weight Method
// ============================================================================

export const WarpWeightMethodSchema = z.enum([
  "inverse-distance",
  "heat-diffusion",
  "radial-basis",
  "bounded",
]);

export type WarpWeightMethod = z.infer<typeof WarpWeightMethodSchema>;

// ============================================================================
// Warp Weight Options
// ============================================================================

export const WarpWeightOptionsSchema = z.object({
  method: WarpWeightMethodSchema,
  falloffPower: positiveFinite.max(100), // Max reasonable falloff
  normalize: z.boolean(),
  minWeight: normalized01,
}).strict();

export type WarpWeightOptions = z.infer<typeof WarpWeightOptionsSchema>;

// ============================================================================
// Control Point (for deformation result)
// ============================================================================

const ControlPointSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  inHandle: Position2DSchema,
  outHandle: Position2DSchema,
}).strict();

// ============================================================================
// Warp Deformation Result
// ============================================================================

export const WarpDeformationResultSchema = z.object({
  vertices: z.instanceof(Float32Array).refine(
    (arr) => arr.length > 0 && arr.length <= 10000000, // Max 10M vertices (5M points)
    { message: "Vertices array must have reasonable size" }
  ),
  controlPoints: boundedArray(ControlPointSchema, 100000), // Max 100k control points
}).strict();

export type WarpDeformationResult = z.infer<typeof WarpDeformationResultSchema>;

// ============================================================================
// Warp Mesh
// ============================================================================

export const WarpMeshSchema = z.object({
  layerId: entityId,
  pins: boundedArray(WarpPinSchema, 10000), // Max 10k pins
  triangulation: boundedArray(z.number().int().nonnegative(), 30000000).min(0), // Max 10M triangles (3 indices each)
  weights: z.instanceof(Float32Array).refine(
    (arr) => arr.length > 0 && arr.length <= 100000000, // Max 100M weights
    { message: "Weights array must have reasonable size" }
  ),
  originalVertices: z.instanceof(Float32Array).refine(
    (arr) => arr.length > 0 && arr.length <= 10000000,
    { message: "Original vertices array must have reasonable size" }
  ),
  pinRestStates: boundedArray(WarpPinRestStateSchema, 10000),
  vertexCount: z.number().int().nonnegative().max(10000000), // Max 10M vertices
  dirty: z.boolean(),
}).strict().refine(
  (data) => {
    // vertexCount should match originalVertices length / 2 (x, y pairs)
    const expectedVertices = data.vertexCount * 2;
    return data.originalVertices.length === expectedVertices;
  },
  { message: "vertexCount must match originalVertices length / 2", path: ["vertexCount"] }
).refine(
  (data) => {
    // Triangulation should be multiple of 3 (triangles)
    return data.triangulation.length % 3 === 0;
  },
  { message: "triangulation length must be multiple of 3", path: ["triangulation"] }
).refine(
  (data) => {
    // pinRestStates should match pins length
    return data.pinRestStates.length === data.pins.length;
  },
  { message: "pinRestStates length must match pins length", path: ["pinRestStates"] }
);

export type WarpMesh = z.infer<typeof WarpMeshSchema>;
