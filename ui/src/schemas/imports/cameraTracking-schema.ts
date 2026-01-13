/**
 * Camera Tracking Import Schemas
 *
 * Zod schemas for validating camera tracking data from external tools.
 * All numeric values use .finite() to reject NaN/Infinity.
 */

import { z } from "zod";

// ============================================================================
// Primitive Schemas with Validation
// ============================================================================

/** Finite number that rejects NaN and Infinity */
const finiteNumber = z.number().finite();

/** Positive finite number */
const positiveFinite = z.number().finite().positive();

/** Non-negative finite number */
const nonNegativeFinite = z.number().finite().nonnegative();

/** Normalized value 0-1 */
const normalized = z.number().finite().min(0).max(1);

/** RGB color value 0-255 */
const colorChannel = z.number().finite().int().min(0).max(255);

// ============================================================================
// Vector Schemas
// ============================================================================

export const Vector2Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
});

export const Vector3Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
});

export const QuaternionSchema = z.object({
  w: finiteNumber,
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
});

export const RGBColorSchema = z.object({
  r: colorChannel,
  g: colorChannel,
  b: colorChannel,
});

// ============================================================================
// Track Point Schemas
// ============================================================================

export const TrackPoint2DSchema = z.object({
  id: z.string().min(1),
  frame: z.number().int().nonnegative(),
  x: normalized,
  y: normalized,
  confidence: normalized,
  color: z.string().optional(),
});

export const TrackPoint3DSchema = z.object({
  id: z.string().min(1),
  position: Vector3Schema,
  color: RGBColorSchema.optional(),
  track2DIDs: z.array(z.string()),
  error: nonNegativeFinite.optional(),
});

// ============================================================================
// Camera Schemas
// ============================================================================

export const DistortionSchema = z.object({
  k1: finiteNumber.optional(),
  k2: finiteNumber.optional(),
  k3: finiteNumber.optional(),
  p1: finiteNumber.optional(),
  p2: finiteNumber.optional(),
});

export const CameraModelSchema = z.enum([
  "pinhole",
  "radial",
  "brown",
  "fisheye",
]);

export const CameraIntrinsicsSchema = z.object({
  focalLength: positiveFinite,
  principalPoint: Vector2Schema,
  width: z.number().int().positive(),
  height: z.number().int().positive(),
  distortion: DistortionSchema.optional(),
  model: CameraModelSchema.optional(),
});

export const CameraPoseSchema = z.object({
  frame: z.number().int().nonnegative(),
  position: Vector3Schema,
  rotation: QuaternionSchema,
  eulerAngles: Vector3Schema.optional(),
  fov: positiveFinite.optional(),
});

// ============================================================================
// Ground Plane Schema
// ============================================================================

export const GroundPlaneSchema = z.object({
  normal: Vector3Schema,
  origin: Vector3Schema,
  up: Vector3Schema,
  scale: positiveFinite.optional(),
});

// ============================================================================
// Metadata Schema
// ============================================================================

export const TrackingMetadataSchema = z.object({
  sourceWidth: z.number().int().positive(),
  sourceHeight: z.number().int().positive(),
  frameRate: positiveFinite,
  frameCount: z.number().int().positive(),
  averageError: nonNegativeFinite.optional(),
  solveMethod: z.string().optional(),
  solveDate: z.string().optional(),
});

// ============================================================================
// Main Camera Tracking Solve Schema
// ============================================================================

export const CameraTrackingSolveSchema = z.object({
  version: z.string().min(1),
  source: z.string().min(1),
  metadata: TrackingMetadataSchema,
  intrinsics: z.union([
    CameraIntrinsicsSchema,
    z.array(CameraIntrinsicsSchema).min(1),
  ]),
  cameraPath: z.array(CameraPoseSchema),
  trackPoints3D: z.array(TrackPoint3DSchema).optional(),
  trackPoints2D: z.array(TrackPoint2DSchema).optional(),
  groundPlane: GroundPlaneSchema.optional(),
});

export type CameraTrackingSolve = z.infer<typeof CameraTrackingSolveSchema>;

// ============================================================================
// Blender Format Schemas
// ============================================================================

export const BlenderMarkerSchema = z.object({
  frame: z.number().int().nonnegative(),
  co: z.tuple([finiteNumber, finiteNumber]),
});

export const BlenderTrackSchema = z.object({
  name: z.string(),
  markers: z.array(BlenderMarkerSchema),
});

export const BlenderCameraPoseSchema = z.object({
  frame: z.number().int().nonnegative(),
  location: z.tuple([finiteNumber, finiteNumber, finiteNumber]),
  rotation: z.tuple([finiteNumber, finiteNumber, finiteNumber, finiteNumber]),
});

export const BlenderPointSchema = z.object({
  co: z.tuple([finiteNumber, finiteNumber, finiteNumber]),
  color: z.tuple([finiteNumber, finiteNumber, finiteNumber]).optional(),
});

export const BlenderReconstructionSchema = z.object({
  camera_poses: z.array(BlenderCameraPoseSchema),
  points: z.array(BlenderPointSchema),
});

export const BlenderCameraSettingsSchema = z.object({
  focal_length: positiveFinite,
  sensor_width: positiveFinite,
});

export const BlenderMotionTrackingDataSchema = z.object({
  fps: positiveFinite,
  clip_width: z.number().int().positive(),
  clip_height: z.number().int().positive(),
  camera: BlenderCameraSettingsSchema,
  tracks: z.array(BlenderTrackSchema),
  reconstruction: BlenderReconstructionSchema.optional(),
});

export type BlenderMotionTrackingData = z.infer<
  typeof BlenderMotionTrackingDataSchema
>;

// ============================================================================
// Format Detection Schemas (looser for detection only)
// ============================================================================

/** Schema for detecting Lattice format - checks key fields exist */
export const LatticeFormatDetectionSchema = z.object({
  version: z.unknown(),
  source: z.unknown(),
  cameraPath: z.unknown(),
});

/** Schema for detecting Blender format - checks key fields exist */
export const BlenderFormatDetectionSchema = z.object({
  fps: z.unknown(),
  tracks: z.unknown(),
  clip_width: z.unknown(),
});
