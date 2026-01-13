/**
 * ATI Export Schemas
 *
 * Zod schemas for validating ATI (Attention-based Temporal Interpolation) trajectory export data.
 * ATI format uses exactly 121 frames with pixel coordinate trajectories.
 * All numeric values use .finite() to reject NaN/Infinity.
 */

import { z } from "zod";

// ============================================================================
// Constants
// ============================================================================

/** ATI format requires exactly 121 frames */
export const ATI_FIXED_FRAMES = 121;

/** Maximum supported resolution */
export const ATI_MAX_DIMENSION = 8192;

/** Minimum supported resolution */
export const ATI_MIN_DIMENSION = 1;

// ============================================================================
// Primitive Schemas
// ============================================================================

/** Finite number that rejects NaN and Infinity */
const finiteNumber = z.number().finite();

/** Positive integer for dimensions */
const positiveDimension = z
  .number()
  .int()
  .positive()
  .max(ATI_MAX_DIMENSION, { message: `Dimension cannot exceed ${ATI_MAX_DIMENSION}` });

/** Non-negative integer for counts */
const nonNegativeInt = z.number().int().nonnegative();

// ============================================================================
// Track Point Schemas
// ============================================================================

/**
 * A single 2D point in pixel coordinates.
 * Used for tracking positions in ATI format.
 */
export const ATITrackPointSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
});

export type ATITrackPoint = z.infer<typeof ATITrackPointSchema>;

/**
 * Array of track points representing one frame's worth of data for a single track.
 * In ATI format, each point is a [x, y] tuple.
 */
export const ATIPointTupleSchema = z.tuple([finiteNumber, finiteNumber]);

export type ATIPointTuple = z.infer<typeof ATIPointTupleSchema>;

// ============================================================================
// Track Data Schemas
// ============================================================================

/**
 * A single track's trajectory across all 121 frames.
 * Each element is a [x, y] point for that frame.
 */
export const ATITrackFramesSchema = z
  .array(ATIPointTupleSchema)
  .length(ATI_FIXED_FRAMES, {
    message: `ATI track must have exactly ${ATI_FIXED_FRAMES} frames`,
  });

export type ATITrackFrames = z.infer<typeof ATITrackFramesSchema>;

/**
 * All tracks in the ATI export.
 * Outer array: tracks, Inner array: 121 frames of [x, y] points.
 */
export const ATITracksArraySchema = z.array(ATITrackFramesSchema).min(1, {
  message: "ATI export must have at least one track",
});

export type ATITracksArray = z.infer<typeof ATITracksArraySchema>;

// ============================================================================
// Visibility Schema
// ============================================================================

/**
 * Visibility data for each track at each frame.
 * Outer array: tracks, Inner array: 121 boolean visibility values.
 */
export const ATIVisibilitySchema = z.array(
  z.array(z.boolean()).length(ATI_FIXED_FRAMES, {
    message: `Visibility array must have exactly ${ATI_FIXED_FRAMES} frames`,
  })
);

export type ATIVisibility = z.infer<typeof ATIVisibilitySchema>;

// ============================================================================
// Export Result Schema
// ============================================================================

/**
 * The result of an ATI export operation.
 * Contains the serialized tracks and metadata.
 */
export const ATIExportResultSchema = z.object({
  /** JSON-serialized track data: number[][][] format */
  tracks: z.string().min(1),

  /** Width of the composition in pixels */
  width: positiveDimension,

  /** Height of the composition in pixels */
  height: positiveDimension,

  /** Number of tracks exported */
  numTracks: nonNegativeInt,

  /** Original frame count before resampling to 121 */
  originalFrames: nonNegativeInt,
});

export type ATIExportResult = z.infer<typeof ATIExportResultSchema>;

// ============================================================================
// Export Configuration Schema
// ============================================================================

/**
 * Configuration options for ATI export.
 */
export const ATIExportConfigSchema = z.object({
  /** Composition ID to export */
  compositionId: z.string().min(1),

  /** Whether to include visibility data */
  includeVisibility: z.boolean().default(true),

  /** Frame range start (will be resampled to 121 frames) */
  startFrame: nonNegativeInt.optional(),

  /** Frame range end (will be resampled to 121 frames) */
  endFrame: nonNegativeInt.optional(),
});

export type ATIExportConfig = z.infer<typeof ATIExportConfigSchema>;

// ============================================================================
// Import/Validation Schema
// ============================================================================

/**
 * Schema for validating imported ATI track data (parsed from JSON string).
 * This validates the actual track array structure after JSON.parse.
 */
export const ATITracksImportSchema = ATITracksArraySchema;

/**
 * Full ATI data structure for import/export operations.
 */
export const ATIDataSchema = z.object({
  /** Track coordinate data */
  tracks: ATITracksArraySchema,

  /** Optional visibility data */
  visibility: ATIVisibilitySchema.optional(),

  /** Metadata */
  metadata: z.object({
    version: z.string().min(1),
    width: positiveDimension,
    height: positiveDimension,
    fps: z.number().finite().positive(),
    frameCount: z.literal(ATI_FIXED_FRAMES),
    numTracks: nonNegativeInt,
    exportedAt: z.string().optional(),
  }),
});

export type ATIData = z.infer<typeof ATIDataSchema>;
