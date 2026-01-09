/**
 * Schema for depth export data consumed by ComfyUI LatticeDepth node.
 * 
 * This schema MUST match what the Python node expects.
 * Any changes here require corresponding changes in:
 * - src/lattice/nodes/compositor_node.py
 * - ui/src/services/export/depthRenderer.ts
 */

import { z } from 'zod';

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
  near: z.number().positive().finite(),
  far: z.number().positive().finite(),
}).refine(
  (range) => range.near < range.far,
  { message: 'nearClip must be less than farClip' }
);

/**
 * Single frame depth output.
 */
export const DepthFrameOutputSchema = z.object({
  // Frame metadata
  frame: z.number().int().nonnegative(),
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
  }).optional(),
});

/**
 * Full depth export output (multiple frames).
 */
export const DepthExportOutputSchema = z.object({
  // Export metadata
  version: z.string(),
  exportedAt: z.string().datetime(),
  
  // Composition info
  composition: z.object({
    width: z.number().int().positive(),
    height: z.number().int().positive(),
    fps: z.number().positive(),
    frameCount: z.number().int().positive(),
  }),
  
  // Export settings used
  settings: z.object({
    format: DepthFormatSchema,
    colormap: ColormapSchema.optional(),
    nearClip: z.number().positive(),
    farClip: z.number().positive(),
    normalize: z.boolean(),
    invert: z.boolean().optional(),
  }),
  
  // Frame data
  frames: z.array(DepthFrameOutputSchema),
});

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
