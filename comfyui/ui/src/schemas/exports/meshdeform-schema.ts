/**
 * Mesh Deform Export Schemas
 *
 * Zod schemas for validating mesh deformation export data.
 * Matches export functions: exportPinsAsTrajectory, exportDeformedMeshMask, exportOverlapAsDepth
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import { WanMoveTrajectorySchema } from "./wanmove-schema";
import {
  boundedArray,
  entityId,
  base64OrDataUrl,
  filename,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ============================================================================
// Primitives
// ============================================================================

const finiteNumber = z.number().finite();
const positiveInt = z.number().int().positive();
const positiveFinite = z.number().finite().positive();

// ============================================================================
// Composition Info Schema
// ============================================================================

export const CompositionInfoSchema = z.object({
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  frameRate: positiveFinite.max(120), // Max 120 FPS
}).strict();

export type CompositionInfo = z.infer<typeof CompositionInfoSchema>;

// ============================================================================
// Pin Metadata Schema
// ============================================================================

export const PinMetadataSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: z.string().max(50).trim(), // Pin type
}).strict();

export type PinMetadata = z.infer<typeof PinMetadataSchema>;

// ============================================================================
// Pin Trajectory Export Schema
// ============================================================================

/**
 * Pin trajectory export with metadata.
 * Matches exportPinsAsTrajectoryWithMetadata() return type.
 */
import { WanMoveTrajectoryBaseSchema } from "./wanmove-schema";

export const PinTrajectoryExportSchema = WanMoveTrajectoryBaseSchema.extend({
  pinMetadata: boundedArray(PinMetadataSchema, 10000), // Max 10k pins
}).strict().refine(
  (data) => {
    // tracks and visibility should have same length
    return data.tracks.length === data.visibility.length;
  },
  { message: "tracks and visibility arrays must have same length", path: ["visibility"] }
).refine(
  (data) => {
    // numPoints should match tracks length
    return data.metadata.numPoints === data.tracks.length;
  },
  { message: "numPoints must match tracks array length", path: ["metadata", "numPoints"] }
).refine(
  (data) => {
    // pinMetadata length should match tracks length
    return data.pinMetadata.length === data.tracks.length;
  },
  { message: "pinMetadata length must match tracks array length", path: ["pinMetadata"] }
);

export type PinTrajectoryExport = z.infer<typeof PinTrajectoryExportSchema>;

// ============================================================================
// Depth Format Schema
// ============================================================================

export const MeshDeformDepthFormatSchema = z.enum([
  "uint8",
  "uint16",
  "float32",
]);

export type MeshDeformDepthFormat = z.infer<
  typeof MeshDeformDepthFormatSchema
>;

// ============================================================================
// Mesh Mask Export Schema
// ============================================================================

/**
 * Mesh mask export result.
 * Returns ImageData (cannot be validated by Zod, but we validate dimensions).
 */
export const MeshMaskExportMetadataSchema = z.object({
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  format: z.literal("ImageData"), // Runtime type, not validated
}).strict();

export type MeshMaskExportMetadata = z.infer<
  typeof MeshMaskExportMetadataSchema
>;

// ============================================================================
// Overlap Depth Export Schema
// ============================================================================

/**
 * Overlap depth export result.
 * Returns ImageData with depth values mapped from pin inFront values.
 */
export const OverlapDepthExportMetadataSchema = z.object({
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  minDepth: finiteNumber.max(100000), // Max 100k units
  maxDepth: finiteNumber.max(100000), // Max 100k units
  format: z.literal("ImageData"), // Runtime type, not validated
}).strict().refine(
  (data) => {
    // maxDepth should be > minDepth
    return data.maxDepth > data.minDepth;
  },
  { message: "maxDepth must be greater than minDepth", path: ["maxDepth"] }
);

export type OverlapDepthExportMetadata = z.infer<
  typeof OverlapDepthExportMetadataSchema
>;

// ============================================================================
// Mesh Mask Sequence Export Schema
// ============================================================================

export const MeshMaskSequenceExportSchema = z.object({
  frames: boundedArray(
    z.object({
      frame: z.number().int().nonnegative().max(100000), // Max 100k frames
      mask: z.union([base64OrDataUrl, filename]), // Base64 PNG or filename
    }).strict(),
    100000 // Max 100k frames
  ),
  metadata: z.object({
    frameCount: positiveInt.max(100000), // Max 100k frames
    width: positiveInt.max(16384), // Max reasonable dimension
    height: positiveInt.max(16384), // Max reasonable dimension
  }).strict(),
}).strict();

export type MeshMaskSequenceExport = z.infer<
  typeof MeshMaskSequenceExportSchema
>;

// ============================================================================
// Overlap Depth Sequence Export Schema
// ============================================================================

export const OverlapDepthSequenceExportSchema = z.object({
  frames: boundedArray(
    z.object({
      frame: z.number().int().nonnegative().max(100000), // Max 100k frames
      depth: z.union([base64OrDataUrl, filename]), // Base64 PNG or filename
    }).strict(),
    100000 // Max 100k frames
  ),
  metadata: z.object({
    frameCount: positiveInt.max(100000), // Max 100k frames
    width: positiveInt.max(16384), // Max reasonable dimension
    height: positiveInt.max(16384), // Max reasonable dimension
    minDepth: finiteNumber.max(100000), // Max 100k units
    maxDepth: finiteNumber.max(100000), // Max 100k units
  }).strict().refine(
    (data) => {
      // maxDepth should be > minDepth
      return data.maxDepth > data.minDepth;
    },
    { message: "maxDepth must be greater than minDepth", path: ["maxDepth"] }
  ),
}).strict();

export type OverlapDepthSequenceExport = z.infer<
  typeof OverlapDepthSequenceExportSchema
>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validatePinTrajectoryExport(data: unknown): PinTrajectoryExport {
  return PinTrajectoryExportSchema.parse(data);
}

export function safeValidatePinTrajectoryExport(data: unknown) {
  return PinTrajectoryExportSchema.safeParse(data);
}
