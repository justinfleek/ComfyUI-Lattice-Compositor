/**
 * Camera Import Schemas
 *
 * Zod schemas for validating camera data imports.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
  entityId,
  iso8601DateTime,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitive Schemas
// ═══════════════════════════════════════════════════════════════════════════

const finiteNumber = z.number().finite();
const positiveFinite = z.number().finite().positive();
const nonNegativeFinite = z.number().finite().nonnegative();
const normalized01 = z.number().finite().min(0).max(1);

// ═══════════════════════════════════════════════════════════════════════════
// Vector Schemas
// ═══════════════════════════════════════════════════════════════════════════

export const Vector3Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
}).strict();

export const Vector2Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
}).strict();

// ═══════════════════════════════════════════════════════════════════════════
// Camera Types
// ═══════════════════════════════════════════════════════════════════════════

export const CameraTypeSchema = z.enum(["one-node", "two-node"]);

export const AutoOrientModeSchema = z.enum([
  "off",
  "orient-along-path",
  "orient-towards-poi",
]);

export const MeasureFilmSizeSchema = z.enum([
  "horizontal",
  "vertical",
  "diagonal",
]);

// ═══════════════════════════════════════════════════════════════════════════
// Depth of Field Schema
// ═══════════════════════════════════════════════════════════════════════════

export const DepthOfFieldSchema = z.object({
  enabled: z.boolean(),
  focusDistance: nonNegativeFinite.max(100000), // Max 100k units
  aperture: nonNegativeFinite.max(100), // Max f/100
  fStop: positiveFinite.max(100), // Max f/100
  blurLevel: normalized01,
  lockToZoom: z.boolean(),
}).strict();

// ═══════════════════════════════════════════════════════════════════════════
// Iris Schema
// ═══════════════════════════════════════════════════════════════════════════

export const IrisSchema = z.object({
  shape: finiteNumber.min(0).max(10),
  rotation: finiteNumber.max(360), // Max 360 degrees
  roundness: normalized01,
  aspectRatio: finiteNumber.min(0.5).max(2),
  diffractionFringe: normalized01,
}).strict();

// ═══════════════════════════════════════════════════════════════════════════
// Highlight Schema
// ═══════════════════════════════════════════════════════════════════════════

export const HighlightSchema = z.object({
  gain: normalized01,
  threshold: normalized01,
  saturation: normalized01,
}).strict();

// ═══════════════════════════════════════════════════════════════════════════
// Main Camera3D Schema
// ═══════════════════════════════════════════════════════════════════════════

export const Camera3DSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: CameraTypeSchema,

  // Transform
  position: Vector3Schema,
  pointOfInterest: Vector3Schema,
  orientation: Vector3Schema,
  xRotation: finiteNumber.max(360), // Max 360 degrees
  yRotation: finiteNumber.max(360), // Max 360 degrees
  zRotation: finiteNumber.max(360), // Max 360 degrees

  // Lens settings
  zoom: positiveFinite.min(0.1).max(1000), // Reasonable zoom range
  focalLength: positiveFinite.max(10000), // Max 10k mm focal length
  angleOfView: positiveFinite.max(180), // Max 180 degrees
  filmSize: positiveFinite.max(100), // Max 100mm film size
  measureFilmSize: MeasureFilmSizeSchema,

  // Depth of field
  depthOfField: DepthOfFieldSchema,

  // Iris
  iris: IrisSchema,

  // Highlight
  highlight: HighlightSchema,

  // Auto-orient
  autoOrient: AutoOrientModeSchema,

  // Clipping
  nearClip: positiveFinite.max(100000), // Max 100k units
  farClip: positiveFinite.max(100000), // Max 100k units
}).strict().refine(
  (data) => {
    // farClip should be > nearClip
    return data.farClip > data.nearClip;
  },
  { message: "farClip must be greater than nearClip", path: ["farClip"] }
);

export type Camera3D = z.infer<typeof Camera3DSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Camera Keyframe Schema
// ═══════════════════════════════════════════════════════════════════════════

export const SpatialInterpolationSchema = z.enum([
  "linear",
  "bezier",
  "auto-bezier",
  "continuous-bezier",
]);

export const TemporalInterpolationSchema = z.enum([
  "linear",
  "bezier",
  "hold",
]);

export const CameraKeyframeSchema = z.object({
  frame: z.number().int().nonnegative().max(100000), // Max 100k frames

  // Transform (optional - only keyframed properties)
  position: Vector3Schema.optional(),
  pointOfInterest: Vector3Schema.optional(),
  orientation: Vector3Schema.optional(),
  xRotation: finiteNumber.max(360).optional(), // Max 360 degrees
  yRotation: finiteNumber.max(360).optional(), // Max 360 degrees
  zRotation: finiteNumber.max(360).optional(), // Max 360 degrees

  // Lens
  zoom: positiveFinite.min(0.1).max(1000).optional(), // Reasonable zoom range
  focalLength: positiveFinite.max(10000).optional(), // Max 10k mm focal length
  focusDistance: nonNegativeFinite.max(100000).optional(), // Max 100k units
  aperture: nonNegativeFinite.max(100).optional(), // Max f/100

  // Bezier handles for curve editor
  inHandle: Vector2Schema.optional(),
  outHandle: Vector2Schema.optional(),

  // Spatial interpolation type
  spatialInterpolation: SpatialInterpolationSchema.optional(),

  // Temporal interpolation type
  temporalInterpolation: TemporalInterpolationSchema.optional(),

  // Separate dimensions
  separateDimensions: z.boolean().optional(),
}).strict();

export type CameraKeyframe = z.infer<typeof CameraKeyframeSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Camera Import Schema (for importCameraJSON)
// ═══════════════════════════════════════════════════════════════════════════

export const CameraImportDataSchema = z.object({
  camera: Camera3DSchema,
  keyframes: boundedArray(CameraKeyframeSchema, 100000), // Max 100k keyframes
  exportedAt: iso8601DateTime.optional(),
  version: z.string().min(1).max(50).trim().optional(), // Version string
}).strict();

export type CameraImportData = z.infer<typeof CameraImportDataSchema>;
