/**
 * Schema for depth export data consumed by ComfyUI LatticeDepth node.
 * 
 * This schema MUST match what the Python node expects.
 * Any changes here require corresponding changes in:
 * - src/lattice/nodes/compositor_node.py
 * - ui/src/services/export/depthRenderer.ts
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from 'zod';
import {
  boundedArray,
  iso8601DateTime,
  MAX_STRING_LENGTH,
} from "../shared-validation";

/**
 * Valid depth output formats.
 * - raw: Float32Array direct depth values
 * - png: 8-bit grayscale PNG
 * - png16: 16-bit grayscale PNG
 * - exr: OpenEXR floating point
 * - depth-anything: Format expected by Depth-Anything model
 * - marigold: Format expected by Marigold model
 */
export const DepthFormatSchema = z.enum([
  'raw',
  'png',
  'png16', 
  'exr',
  'depth-anything',
  'marigold',
]);

/**
 * Valid colormap names for visualization.
 */
export const ColormapSchema = z.enum([
  'grayscale',
  'viridis',
  'plasma',
  'magma',
  'inferno',
  'turbo',
]);

/**
 * Depth range specification.
 * nearClip MUST be less than farClip.
 */
export const DepthRangeSchema = z.object({
  near: z.number().positive().finite().max(100000), // Max 100k units
  far: z.number().positive().finite().max(100000), // Max 100k units
}).strict().refine(
  (range) => range.near < range.far,
  { message: 'nearClip must be less than farClip' }
);

/**
 * Single frame depth output.
 */
export const DepthFrameOutputSchema = z.object({
  // Frame metadata
  frame: z.number().int().nonnegative().max(100000), // Max 100k frames
  width: z.number().int().positive().max(16384),
  height: z.number().int().positive().max(16384),
  
  // Depth data
  format: DepthFormatSchema,
  depthRange: DepthRangeSchema,
  
  // Actual depth values - format depends on `format` field
  // For 'raw': Float32Array
  // For 'png'/'png16': Uint8Array (PNG bytes)
  // For 'exr': ArrayBuffer (EXR bytes)
  data: z.union([
    z.instanceof(Float32Array),
    z.instanceof(Uint8Array),
    z.instanceof(Uint16Array),
    z.instanceof(ArrayBuffer),
  ]),
  
  // Statistics for validation
  stats: z.object({
    min: z.number().finite(),
    max: z.number().finite(),
    mean: z.number().finite().optional(),
  }).strict().optional(),
}).strict();

/**
 * Full depth export output (multiple frames).
 */
export const DepthExportOutputSchema = z.object({
  // Export metadata
  version: z.string().min(1).max(50).trim(), // Version string
  exportedAt: iso8601DateTime,
  
  // Composition info
  composition: z.object({
    width: z.number().int().positive().max(16384), // Max reasonable dimension
    height: z.number().int().positive().max(16384), // Max reasonable dimension
    fps: z.number().positive().max(120), // Max 120 FPS
    frameCount: z.number().int().positive().max(100000), // Max 100k frames
  }).strict(),
  
  // Export settings used
  settings: z.object({
    format: DepthFormatSchema,
    colormap: ColormapSchema.optional(),
    nearClip: z.number().positive().max(100000), // Max 100k units
    farClip: z.number().positive().max(100000), // Max 100k units
    normalize: z.boolean(),
    invert: z.boolean().optional(),
  }).strict().refine(
    (settings) => settings.farClip > settings.nearClip,
    { message: "farClip must be greater than nearClip", path: ["farClip"] }
  ),
  
  // Frame data
  frames: boundedArray(DepthFrameOutputSchema, 100000), // Max 100k frames
}).strict();

/**
 * Type exports for TypeScript
 */
export type DepthFormat = z.infer<typeof DepthFormatSchema>;
export type Colormap = z.infer<typeof ColormapSchema>;
export type DepthRange = z.infer<typeof DepthRangeSchema>;
export type DepthFrameOutput = z.infer<typeof DepthFrameOutputSchema>;
export type DepthExportOutput = z.infer<typeof DepthExportOutputSchema>;

/**
 * Validation helper
 */
export function validateDepthOutput(data: unknown): DepthExportOutput {
  return DepthExportOutputSchema.parse(data);
}

/**
 * Safe validation that returns result instead of throwing
 */
export function safeValidateDepthOutput(data: unknown) {
  return DepthExportOutputSchema.safeParse(data);
}
