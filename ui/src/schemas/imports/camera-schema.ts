/**
 * Camera Import Schemas
 *
 * Zod schemas for validating camera data imports.
 * All numeric values use .finite() to reject NaN/Infinity.
 */

import { z } from "zod";

// ============================================================================
// Primitive Schemas
// ============================================================================

const finiteNumber = z.number().finite();
const positiveFinite = z.number().finite().positive();
const nonNegativeFinite = z.number().finite().nonnegative();
const normalized01 = z.number().finite().min(0).max(1);

// ============================================================================
// Vector Schemas
// ============================================================================

export const Vector3Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
});

export const Vector2Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
});

// ============================================================================
// Camera Types
// ============================================================================

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

// ============================================================================
// Depth of Field Schema
// ============================================================================

export const DepthOfFieldSchema = z.object({
  enabled: z.boolean(),
  focusDistance: nonNegativeFinite,
  aperture: nonNegativeFinite,
  fStop: positiveFinite,
  blurLevel: normalized01,
  lockToZoom: z.boolean(),
});

// ============================================================================
// Iris Schema
// ============================================================================

export const IrisSchema = z.object({
  shape: finiteNumber.refine((n) => n >= 0 && n <= 10, {
    message: "Iris shape must be between 0 and 10",
  }),
  rotation: finiteNumber,
  roundness: normalized01,
  aspectRatio: finiteNumber.refine((n) => n >= 0.5 && n <= 2, {
    message: "Iris aspect ratio must be between 0.5 and 2",
  }),
  diffractionFringe: normalized01,
});

// ============================================================================
// Highlight Schema
// ============================================================================

export const HighlightSchema = z.object({
  gain: normalized01,
  threshold: normalized01,
  saturation: normalized01,
});

// ============================================================================
// Main Camera3D Schema
// ============================================================================

export const Camera3DSchema = z.object({
  id: z.string().min(1),
  name: z.string(),
  type: CameraTypeSchema,

  // Transform
  position: Vector3Schema,
  pointOfInterest: Vector3Schema,
  orientation: Vector3Schema,
  xRotation: finiteNumber,
  yRotation: finiteNumber,
  zRotation: finiteNumber,

  // Lens settings
  zoom: positiveFinite,
  focalLength: positiveFinite,
  angleOfView: positiveFinite,
  filmSize: positiveFinite,
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
  nearClip: positiveFinite,
  farClip: positiveFinite,
});

export type Camera3D = z.infer<typeof Camera3DSchema>;

// ============================================================================
// Camera Keyframe Schema
// ============================================================================

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
  frame: z.number().int().nonnegative(),

  // Transform (optional - only keyframed properties)
  position: Vector3Schema.optional(),
  pointOfInterest: Vector3Schema.optional(),
  orientation: Vector3Schema.optional(),
  xRotation: finiteNumber.optional(),
  yRotation: finiteNumber.optional(),
  zRotation: finiteNumber.optional(),

  // Lens
  zoom: positiveFinite.optional(),
  focalLength: positiveFinite.optional(),
  focusDistance: nonNegativeFinite.optional(),
  aperture: nonNegativeFinite.optional(),

  // Bezier handles for curve editor
  inHandle: Vector2Schema.optional(),
  outHandle: Vector2Schema.optional(),

  // Spatial interpolation type
  spatialInterpolation: SpatialInterpolationSchema.optional(),

  // Temporal interpolation type
  temporalInterpolation: TemporalInterpolationSchema.optional(),

  // Separate dimensions
  separateDimensions: z.boolean().optional(),
});

export type CameraKeyframe = z.infer<typeof CameraKeyframeSchema>;

// ============================================================================
// Camera Import Schema (for importCameraJSON)
// ============================================================================

export const CameraImportDataSchema = z.object({
  camera: Camera3DSchema,
  keyframes: z.array(CameraKeyframeSchema),
  exportedAt: z.string().optional(),
  version: z.string().optional(),
});

export type CameraImportData = z.infer<typeof CameraImportDataSchema>;
