/**
 * Frame Sequence Export Schemas
 *
 * Zod schemas for validating frame sequence export data.
 * Matches FrameSequenceResult and related interfaces.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
  filename,
  MAX_PATH_LENGTH,
  MAX_FILENAME_LENGTH,
  MAX_STRING_LENGTH,
} from "../shared-validation";

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
  filenamePattern: z.string().min(1).max(MAX_FILENAME_LENGTH).trim(), // e.g., "frame_{frame:04d}"
  outputDir: z.string().max(MAX_PATH_LENGTH).trim(),
  startFrame: nonNegativeInt.max(100000), // Max 100k frames
  endFrame: nonNegativeInt.max(100000), // Max 100k frames
  bitDepth: BitDepthSchema.optional(), // For HDR formats
  colorSpace: ColorSpaceSchema.optional(),
}).strict().refine(
  (data) => {
    // endFrame should be >= startFrame
    return data.endFrame >= data.startFrame;
  },
  { message: "endFrame must be >= startFrame", path: ["endFrame"] }
);

export type FrameExportOptions = z.infer<typeof FrameExportOptionsSchema>;

// ============================================================================
// Exported Frame Schema
// ============================================================================

export const ExportedFrameSchema = z.object({
  frameNumber: nonNegativeInt.max(100000), // Max 100k frames
  filename: filename,
  blob: z.instanceof(Blob).optional(),
  dataUrl: z.string().max(MAX_STRING_LENGTH).optional(),
  size: nonNegativeInt.max(2147483647), // Max 32-bit int (2GB)
}).strict();

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
  frames: boundedArray(ExportedFrameSchema, 100000), // Max 100k frames
  totalSize: nonNegativeInt.max(2147483647), // Max 32-bit int (2GB)
  errors: boundedArray(z.string().max(MAX_STRING_LENGTH), 1000), // Max 1000 errors
  warnings: boundedArray(z.string().max(MAX_STRING_LENGTH), 1000), // Max 1000 warnings
}).strict();

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
