/**
 * Mesh Deform Export Schemas
 *
 * Zod schemas for validating mesh deformation export data.
 * Matches export functions: exportPinsAsTrajectory, exportDeformedMeshMask, exportOverlapAsDepth
 */

import { z } from "zod";
import { WanMoveTrajectorySchema } from "./wanmove-schema";

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
  width: positiveInt,
  height: positiveInt,
  frameRate: positiveFinite,
});

export type CompositionInfo = z.infer<typeof CompositionInfoSchema>;

// ============================================================================
// Pin Metadata Schema
// ============================================================================

export const PinMetadataSchema = z.object({
  id: z.string().min(1),
  name: z.string(),
  type: z.string(),
});

export type PinMetadata = z.infer<typeof PinMetadataSchema>;

// ============================================================================
// Pin Trajectory Export Schema
// ============================================================================

/**
 * Pin trajectory export with metadata.
 * Matches exportPinsAsTrajectoryWithMetadata() return type.
 */
export const PinTrajectoryExportSchema = WanMoveTrajectorySchema.extend({
  pinMetadata: z.array(PinMetadataSchema),
});

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
  width: positiveInt,
  height: positiveInt,
  format: z.literal("ImageData"), // Runtime type, not validated
});

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
  width: positiveInt,
  height: positiveInt,
  minDepth: finiteNumber,
  maxDepth: finiteNumber,
  format: z.literal("ImageData"), // Runtime type, not validated
});

export type OverlapDepthExportMetadata = z.infer<
  typeof OverlapDepthExportMetadataSchema
>;

// ============================================================================
// Mesh Mask Sequence Export Schema
// ============================================================================

export const MeshMaskSequenceExportSchema = z.object({
  frames: z.array(
    z.object({
      frame: z.number().int().nonnegative(),
      mask: z.string().min(1), // Base64 PNG or filename
    }),
  ),
  metadata: z.object({
    frameCount: positiveInt,
    width: positiveInt,
    height: positiveInt,
  }),
});

export type MeshMaskSequenceExport = z.infer<
  typeof MeshMaskSequenceExportSchema
>;

// ============================================================================
// Overlap Depth Sequence Export Schema
// ============================================================================

export const OverlapDepthSequenceExportSchema = z.object({
  frames: z.array(
    z.object({
      frame: z.number().int().nonnegative(),
      depth: z.string().min(1), // Base64 PNG or filename
    }),
  ),
  metadata: z.object({
    frameCount: positiveInt,
    width: positiveInt,
    height: positiveInt,
    minDepth: finiteNumber,
    maxDepth: finiteNumber,
  }),
});

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
