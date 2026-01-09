/**
 * Schema for camera export data consumed by ComfyUI nodes.
 * 
 * Supports multiple AI video model formats:
 * - MotionCtrl: Camera trajectory for Stable Video Diffusion
 * - Wan-Move: Camera movement for Wan video generation
 * - Uni3C: Universal 3D camera control
 * - CameraCtrl: Generic camera control format
 */

import { z } from 'zod';

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
  focalLength: z.number().positive(),
  sensorWidth: z.number().positive().optional(),
  sensorHeight: z.number().positive().optional(),
  fov: z.number().positive().max(180), // Field of view in degrees
  aspectRatio: z.number().positive(),
  principalPoint: z.object({
    x: z.number().finite(),
    y: z.number().finite(),
  }).optional(),
});

/**
 * Single camera frame data.
 */
export const CameraFrameSchema = z.object({
  frame: z.number().int().nonnegative(),
  timestamp: z.number().nonnegative().optional(),
  
  // Position in world space
  position: z.object({
    x: z.number().finite(),
    y: z.number().finite(),
    z: z.number().finite(),
  }),
  
  // Rotation as Euler angles (degrees) or quaternion
  rotation: z.union([
    // Euler angles
    z.object({
      type: z.literal('euler'),
      x: z.number().finite(),
      y: z.number().finite(), 
      z: z.number().finite(),
      order: z.enum(['XYZ', 'YXZ', 'ZXY', 'ZYX', 'XZY', 'YZX']).optional(),
    }),
    // Quaternion
    z.object({
      type: z.literal('quaternion'),
      x: z.number().finite(),
      y: z.number().finite(),
      z: z.number().finite(),
      w: z.number().finite(),
    }),
  ]),
  
  // Optional: Full 4x4 matrix (overrides position/rotation)
  matrix: Matrix4x4Schema.optional(),
  
  // Optional: Per-frame intrinsics (for dolly zoom etc)
  intrinsics: CameraIntrinsicsSchema.optional(),
});

/**
 * MotionCtrl-specific format.
 */
export const MotionCtrlOutputSchema = z.object({
  format: z.literal('motionctrl'),
  version: z.string(),
  
  // Camera trajectory as list of 4x4 matrices
  camera_poses: z.array(Matrix4x4Schema),
  
  // Intrinsics
  focal_length: z.number().positive(),
  image_width: z.number().int().positive(),
  image_height: z.number().int().positive(),
});

/**
 * Wan-Move specific format.
 */
export const WanMoveOutputSchema = z.object({
  format: z.literal('wan-move'),
  version: z.string(),
  
  // Control points
  control_points: z.array(z.object({
    frame: z.number().int().nonnegative(),
    position: z.tuple([z.number(), z.number(), z.number()]),
    rotation: z.tuple([z.number(), z.number(), z.number()]),
  })),
  
  // Interpolation type
  interpolation: z.enum(['linear', 'bezier', 'spline']),
});

/**
 * Full camera export output.
 */
export const CameraExportOutputSchema = z.object({
  // Metadata
  version: z.string(),
  exportedAt: z.string().datetime(),
  format: CameraFormatSchema,
  coordinateSystem: CoordinateSystemSchema,
  
  // Composition info
  composition: z.object({
    width: z.number().int().positive(),
    height: z.number().int().positive(),
    fps: z.number().positive(),
    frameCount: z.number().int().positive(),
  }),
  
  // Camera settings
  intrinsics: CameraIntrinsicsSchema,
  
  // Frame data
  frames: z.array(CameraFrameSchema),
  
  // Format-specific data
  formatSpecific: z.union([
    MotionCtrlOutputSchema,
    WanMoveOutputSchema,
    z.object({}), // Generic format
  ]).optional(),
});

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
