/**
 * Frame Sequence Export Schemas
 *
 * Zod schemas for validating frame sequence export data.
 * Matches FrameSequenceResult and related interfaces.
 */

import { z } from "zod";

// ============================================================================
// Primitives
// ============================================================================

const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();
const normalized0100 = z.number().finite().min(0).max(100);

// ============================================================================
// Frame Format Schema
// ============================================================================

export const FrameFormatSchema = z.enum([
  "png", // Lossless, 8-bit RGBA
  "jpeg", // Lossy, 8-bit RGB
  "webp", // Modern, supports lossless
  "tiff", // Via backend - 8/16-bit
  "exr", // Via backend - HDR 32-bit float
  "dpx", // Via backend - 10/16-bit film format
]);

export type FrameFormat = z.infer<typeof FrameFormatSchema>;

// ============================================================================
// Color Space Schema
// ============================================================================

export const ColorSpaceSchema = z.enum([
  "sRGB",
  "Linear",
  "ACEScg",
  "Rec709",
]);

export type ColorSpace = z.infer<typeof ColorSpaceSchema>;

// ============================================================================
// Bit Depth Schema
// ============================================================================

export const BitDepthSchema = z.union([
  z.literal(8),
  z.literal(10),
  z.literal(16),
  z.literal(32),
]);

export type BitDepth = z.infer<typeof BitDepthSchema>;

// ============================================================================
// Frame Export Options Schema
// ============================================================================

export const FrameExportOptionsSchema = z.object({
  format: FrameFormatSchema,
  quality: normalized0100, // 0-100 for lossy formats
  filenamePattern: z.string().min(1), // e.g., "frame_{frame:04d}"
  outputDir: z.string(),
  startFrame: nonNegativeInt,
  endFrame: nonNegativeInt,
  bitDepth: BitDepthSchema.optional(), // For HDR formats
  colorSpace: ColorSpaceSchema.optional(),
});

export type FrameExportOptions = z.infer<typeof FrameExportOptionsSchema>;

// ============================================================================
// Exported Frame Schema
// ============================================================================

export const ExportedFrameSchema = z.object({
  frameNumber: nonNegativeInt,
  filename: z.string().min(1),
  blob: z.instanceof(Blob).optional(),
  dataUrl: z.string().optional(),
  size: nonNegativeInt,
});

export type ExportedFrame = z.infer<typeof ExportedFrameSchema>;

// ============================================================================
// Frame Sequence Result Schema
// ============================================================================

/**
 * Frame sequence export result.
 * Matches FrameSequenceResult interface exactly.
 */
export const FrameSequenceResultSchema = z.object({
  success: z.boolean(),
  frames: z.array(ExportedFrameSchema),
  totalSize: nonNegativeInt,
  errors: z.array(z.string()),
  warnings: z.array(z.string()),
});

export type FrameSequenceResult = z.infer<typeof FrameSequenceResultSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateFrameSequenceResult(
  data: unknown,
): FrameSequenceResult {
  return FrameSequenceResultSchema.parse(data);
}

export function safeValidateFrameSequenceResult(data: unknown) {
  return FrameSequenceResultSchema.safeParse(data);
}
