/**
 * Schema for camera export data consumed by ComfyUI nodes.
 * 
 * Supports multiple AI video model formats:
 * - MotionCtrl: Camera trajectory for Stable Video Diffusion
 * - Wan-Move: Camera movement for Wan video generation
 * - Uni3C: Universal 3D camera control
 * - CameraCtrl: Generic camera control format
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from 'zod';
import {
  boundedArray,
  iso8601DateTime,
  MAX_NAME_LENGTH,
} from "../shared-validation";

/**
 * Supported camera export formats.
 */
export const CameraFormatSchema = z.enum([
  'motionctrl',
  'wan-move',
  'uni3c',
  'cameractrl',
  'blender',
  'fbx',
]);

/**
 * Coordinate system conventions.
 * Different tools expect different conventions.
 */
export const CoordinateSystemSchema = z.enum([
  'opengl',   // Y-up, right-handed
  'opencv',   // Y-down, right-handed  
  'blender',  // Z-up, right-handed
  'unity',    // Y-up, left-handed
]);

/**
 * 4x4 transformation matrix (row-major).
 * Used for camera extrinsics.
 */
export const Matrix4x4Schema = z.tuple([
  z.tuple([z.number().finite(), z.number().finite(), z.number().finite(), z.number().finite()]),
  z.tuple([z.number().finite(), z.number().finite(), z.number().finite(), z.number().finite()]),
  z.tuple([z.number().finite(), z.number().finite(), z.number().finite(), z.number().finite()]),
  z.tuple([z.number().finite(), z.number().finite(), z.number().finite(), z.number().finite()]),
]);

/**
 * Camera intrinsic parameters.
 */
export const CameraIntrinsicsSchema = z.object({
  focalLength: z.number().positive().max(10000), // Max 10k mm focal length
  sensorWidth: z.number().positive().max(100).optional(), // Max 100mm sensor width
  sensorHeight: z.number().positive().max(100).optional(), // Max 100mm sensor height
  fov: z.number().positive().max(180), // Field of view in degrees
  aspectRatio: z.number().positive().max(10), // Max 10:1 aspect ratio
  principalPoint: z.object({
    x: z.number().finite(),
    y: z.number().finite(),
  }).strict().optional(),
}).strict();

/**
 * Single camera frame data.
 */
export const CameraFrameSchema = z.object({
  frame: z.number().int().nonnegative().max(100000), // Max 100k frames
  timestamp: z.number().nonnegative().max(86400).optional(), // Max 24 hours timestamp
  
  // Position in world space
  position: z.object({
    x: z.number().finite(),
    y: z.number().finite(),
    z: z.number().finite(),
  }).strict(),
  
  // Rotation as Euler angles (degrees) or quaternion
  rotation: z.union([
    // Euler angles
    z.object({
      type: z.literal('euler'),
      x: z.number().finite().max(360), // Max 360 degrees
      y: z.number().finite().max(360), // Max 360 degrees
      z: z.number().finite().max(360), // Max 360 degrees
      order: z.enum(['XYZ', 'YXZ', 'ZXY', 'ZYX', 'XZY', 'YZX']).optional(),
    }).strict(),
    // Quaternion
    z.object({
      type: z.literal('quaternion'),
      x: z.number().finite(),
      y: z.number().finite(),
      z: z.number().finite(),
      w: z.number().finite(),
    }).strict().refine(
      (q) => {
        // Quaternion should be normalized (approximately)
        const len = Math.sqrt(q.x * q.x + q.y * q.y + q.z * q.z + q.w * q.w);
        return Math.abs(len - 1) < 0.1; // Allow 10% tolerance
      },
      { message: "Quaternion should be normalized", path: ["w"] }
    ),
  ]),
  
  // Optional: Full 4x4 matrix (overrides position/rotation)
  matrix: Matrix4x4Schema.optional(),
  
  // Optional: Per-frame intrinsics (for dolly zoom etc)
  intrinsics: CameraIntrinsicsSchema.optional(),
}).strict();

/**
 * MotionCtrl-specific format.
 */
export const MotionCtrlOutputSchema = z.object({
  format: z.literal('motionctrl'),
  version: z.string().min(1).max(50).trim(), // Version string
  
  // Camera trajectory as list of 4x4 matrices
  camera_poses: boundedArray(Matrix4x4Schema, 100000), // Max 100k camera poses
  
  // Intrinsics
  focal_length: z.number().positive().max(10000), // Max 10k mm focal length
  image_width: z.number().int().positive().max(16384), // Max reasonable dimension
  image_height: z.number().int().positive().max(16384), // Max reasonable dimension
}).strict();

/**
 * Wan-Move specific format.
 */
export const WanMoveOutputSchema = z.object({
  format: z.literal('wan-move'),
  version: z.string().min(1).max(50).trim(), // Version string
  
  // Control points
  control_points: boundedArray(z.object({
    frame: z.number().int().nonnegative().max(100000), // Max 100k frames
    position: z.tuple([z.number().finite(), z.number().finite(), z.number().finite()]),
    rotation: z.tuple([z.number().finite().max(360), z.number().finite().max(360), z.number().finite().max(360)]), // Max 360 degrees each
  }).strict(), 100000), // Max 100k control points
  
  // Interpolation type
  interpolation: z.enum(['linear', 'bezier', 'spline']),
}).strict();

/**
 * Full camera export output.
 */
export const CameraExportOutputSchema = z.object({
  // Metadata
  version: z.string().min(1).max(50).trim(), // Version string
  exportedAt: iso8601DateTime,
  format: CameraFormatSchema,
  coordinateSystem: CoordinateSystemSchema,
  
  // Composition info
  composition: z.object({
    width: z.number().int().positive().max(16384), // Max reasonable dimension
    height: z.number().int().positive().max(16384), // Max reasonable dimension
    fps: z.number().positive().max(120), // Max 120 FPS
    frameCount: z.number().int().positive().max(100000), // Max 100k frames
  }).strict(),
  
  // Camera settings
  intrinsics: CameraIntrinsicsSchema,
  
  // Frame data
  frames: boundedArray(CameraFrameSchema, 100000), // Max 100k frames
  
  // Format-specific data
  formatSpecific: z.union([
    MotionCtrlOutputSchema,
    WanMoveOutputSchema,
    z.object({}).strict(), // Generic format
  ]).optional(),
}).strict();

// Type exports
export type CameraFormat = z.infer<typeof CameraFormatSchema>;
export type CoordinateSystem = z.infer<typeof CoordinateSystemSchema>;
export type Matrix4x4 = z.infer<typeof Matrix4x4Schema>;
export type CameraIntrinsics = z.infer<typeof CameraIntrinsicsSchema>;
export type CameraFrame = z.infer<typeof CameraFrameSchema>;
export type CameraExportOutput = z.infer<typeof CameraExportOutputSchema>;

// Validation helpers
export function validateCameraOutput(data: unknown): CameraExportOutput {
  return CameraExportOutputSchema.parse(data);
}

export function safeValidateCameraOutput(data: unknown) {
  return CameraExportOutputSchema.safeParse(data);
}
