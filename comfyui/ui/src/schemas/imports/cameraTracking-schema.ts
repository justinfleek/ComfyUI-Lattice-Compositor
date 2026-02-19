/**
 * Camera Tracking Import Schemas
 *
 * Zod schemas for validating camera tracking data from external tools.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
  entityId,
  hexColor,
  iso8601DateTime,
  jsonSerializable,
  MAX_NAME_LENGTH,
  MAX_STRING_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitive Schemas with Validation
// ═══════════════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════════════
// Vector Schemas
// ═══════════════════════════════════════════════════════════════════════════

export const Vector2Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
}).strict();

export const Vector3Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
}).strict();

export const QuaternionSchema = z.object({
  w: finiteNumber,
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
}).strict().refine(
  (q) => {
    // Quaternion should be normalized (approximately)
    const len = Math.sqrt(q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z);
    return Math.abs(len - 1) < 0.1; // Allow 10% tolerance
  },
  { message: "Quaternion should be normalized", path: ["w"] }
);

export const RGBColorSchema = z.object({
  r: colorChannel,
  g: colorChannel,
  b: colorChannel,
}).strict();

// ═══════════════════════════════════════════════════════════════════════════
// Track Point Schemas
// ═══════════════════════════════════════════════════════════════════════════

export const TrackPoint2DSchema = z.object({
  id: entityId,
  frame: z.number().int().nonnegative().max(100000), // Max 100k frames
  x: normalized,
  y: normalized,
  confidence: normalized,
  color: hexColor.optional(),
}).strict();

export const TrackPoint3DSchema = z.object({
  id: entityId,
  position: Vector3Schema,
  color: RGBColorSchema.optional(),
  track2DIDs: boundedArray(entityId, 1000), // Max 1000 2D track IDs
  error: nonNegativeFinite.max(100000).optional(), // Max 100k units error
}).strict();

// ═══════════════════════════════════════════════════════════════════════════
// Camera Schemas
// ═══════════════════════════════════════════════════════════════════════════

export const DistortionSchema = z.object({
  k1: finiteNumber.max(10).optional(), // Max reasonable distortion
  k2: finiteNumber.max(10).optional(), // Max reasonable distortion
  k3: finiteNumber.max(10).optional(), // Max reasonable distortion
  p1: finiteNumber.max(1).optional(), // Max reasonable tangential distortion
  p2: finiteNumber.max(1).optional(), // Max reasonable tangential distortion
}).strict();

export const CameraModelSchema = z.enum([
  "pinhole",
  "radial",
  "brown",
  "fisheye",
]);

export const CameraIntrinsicsSchema = z.object({
  focalLength: positiveFinite.max(10000), // Max 10k mm focal length
  principalPoint: Vector2Schema,
  width: z.number().int().positive().max(16384), // Max reasonable dimension
  height: z.number().int().positive().max(16384), // Max reasonable dimension
  distortion: DistortionSchema.optional(),
  model: CameraModelSchema.optional(),
}).strict();

export const CameraPoseSchema = z.object({
  frame: z.number().int().nonnegative().max(100000), // Max 100k frames
  position: Vector3Schema,
  rotation: QuaternionSchema,
  eulerAngles: Vector3Schema.optional(),
  fov: positiveFinite.max(180).optional(), // Max 180 degrees FOV
}).strict();

// ═══════════════════════════════════════════════════════════════════════════
// Ground Plane Schema
// ═══════════════════════════════════════════════════════════════════════════

export const GroundPlaneSchema = z.object({
  normal: Vector3Schema,
  origin: Vector3Schema,
  up: Vector3Schema,
  scale: positiveFinite.max(100000).optional(), // Max 100k units scale
}).strict();

// ═══════════════════════════════════════════════════════════════════════════
// Metadata Schema
// ═══════════════════════════════════════════════════════════════════════════

export const TrackingMetadataSchema = z.object({
  sourceWidth: z.number().int().positive().max(16384), // Max reasonable dimension
  sourceHeight: z.number().int().positive().max(16384), // Max reasonable dimension
  frameRate: positiveFinite.max(120), // Max 120 FPS
  frameCount: z.number().int().positive().max(100000), // Max 100k frames
  averageError: nonNegativeFinite.max(100000).optional(), // Max 100k units error
  solveMethod: z.string().max(MAX_NAME_LENGTH).trim().optional(),
  solveDate: iso8601DateTime.optional(),
}).strict();

// ═══════════════════════════════════════════════════════════════════════════
// Main Camera Tracking Solve Schema
// ═══════════════════════════════════════════════════════════════════════════

export const CameraTrackingSolveSchema = z.object({
  version: z.string().min(1).max(50).trim(), // Version string
  source: z.string().min(1).max(MAX_STRING_LENGTH).trim(),
  metadata: TrackingMetadataSchema,
  intrinsics: z.union([
    CameraIntrinsicsSchema,
    boundedArray(CameraIntrinsicsSchema, 1000).min(1), // Max 1000 camera intrinsics
  ]),
  cameraPath: boundedArray(CameraPoseSchema, 100000), // Max 100k camera poses
  trackPoints3D: boundedArray(TrackPoint3DSchema, 100000).optional(), // Max 100k 3D track points
  trackPoints2D: boundedArray(TrackPoint2DSchema, 1000000).optional(), // Max 1M 2D track points
  groundPlane: GroundPlaneSchema.optional(),
}).strict();

export type CameraTrackingSolve = z.infer<typeof CameraTrackingSolveSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Blender Format Schemas
// ═══════════════════════════════════════════════════════════════════════════

export const BlenderMarkerSchema = z.object({
  frame: z.number().int().nonnegative().max(100000), // Max 100k frames
  co: z.tuple([finiteNumber.max(16384), finiteNumber.max(16384)]), // Max reasonable coordinates
}).strict();

export const BlenderTrackSchema = z.object({
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  markers: boundedArray(BlenderMarkerSchema, 100000), // Max 100k markers per track
}).strict();

export const BlenderCameraPoseSchema = z.object({
  frame: z.number().int().nonnegative().max(100000), // Max 100k frames
  location: z.tuple([finiteNumber, finiteNumber, finiteNumber]),
  rotation: z.tuple([finiteNumber.max(360), finiteNumber.max(360), finiteNumber.max(360), finiteNumber.max(360)]), // Max 360 degrees each
}).strict();

export const BlenderPointSchema = z.object({
  co: z.tuple([finiteNumber, finiteNumber, finiteNumber]),
  color: z.tuple([normalized, normalized, normalized]).optional(), // RGB 0-1
}).strict();

export const BlenderReconstructionSchema = z.object({
  camera_poses: boundedArray(BlenderCameraPoseSchema, 100000), // Max 100k camera poses
  points: boundedArray(BlenderPointSchema, 10000000), // Max 10M points
}).strict();

export const BlenderCameraSettingsSchema = z.object({
  focal_length: positiveFinite.max(10000), // Max 10k mm focal length
  sensor_width: positiveFinite.max(100), // Max 100mm sensor width
}).strict();

export const BlenderMotionTrackingDataSchema = z.object({
  fps: positiveFinite.max(120), // Max 120 FPS
  clip_width: z.number().int().positive().max(16384), // Max reasonable dimension
  clip_height: z.number().int().positive().max(16384), // Max reasonable dimension
  camera: BlenderCameraSettingsSchema,
  tracks: boundedArray(BlenderTrackSchema, 10000), // Max 10k tracks
  reconstruction: BlenderReconstructionSchema.optional(),
}).strict();

export type BlenderMotionTrackingData = z.infer<
  typeof BlenderMotionTrackingDataSchema
>;

// ═══════════════════════════════════════════════════════════════════════════
// Format Detection Schemas (looser for detection only)
// ═══════════════════════════════════════════════════════════════════════════

/** Schema for detecting Lattice format - checks key fields exist */
export const LatticeFormatDetectionSchema = z.object({
  version: jsonSerializable.optional(),
  source: jsonSerializable.optional(),
  cameraPath: jsonSerializable.optional(),
}).passthrough(); // Allow additional fields for detection

/** Schema for detecting Blender format - checks key fields exist */
export const BlenderFormatDetectionSchema = z.object({
  fps: jsonSerializable.optional(),
  tracks: jsonSerializable.optional(),
  clip_width: jsonSerializable.optional(),
}).passthrough(); // Allow additional fields for detection
