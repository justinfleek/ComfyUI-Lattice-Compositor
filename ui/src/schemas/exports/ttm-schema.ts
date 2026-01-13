/**
 * TTM (Time-to-Move) Export Schemas
 *
 * Zod schemas for validating TTM export data.
 * Matches the exact structure returned by exportForModel() for TTM target.
 */

import { z } from "zod";

// ============================================================================
// Primitives
// ============================================================================

const finiteNumber = z.number().finite();
const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();

// ============================================================================
// TTM Model Schema
// ============================================================================

export const TTMModelSchema = z.enum(["wan", "cogvideox", "svd"]);

export type TTMModel = z.infer<typeof TTMModelSchema>;

// ============================================================================
// TTM Layer Export Schema
// ============================================================================

/**
 * Per-layer TTM export data.
 * Matches TTMLayerExport interface exactly.
 */
export const TTMLayerExportSchema = z.object({
  layerId: z.string().min(1),
  layerName: z.string().min(1),
  motionMask: z.string().min(1), // Base64 PNG
  trajectory: z.array(
    z.object({
      frame: nonNegativeInt,
      x: finiteNumber,
      y: finiteNumber,
    }),
  ),
  visibility: z.array(z.boolean()),
});

export type TTMLayerExport = z.infer<typeof TTMLayerExportSchema>;

// ============================================================================
// TTM Model Config Schema
// ============================================================================

export const TTMModelConfigSchema = z.object({
  model: TTMModelSchema,
  tweakIndex: finiteNumber,
  tstrongIndex: finiteNumber,
  inferenceSteps: positiveInt,
});

export type TTMModelConfig = z.infer<typeof TTMModelConfigSchema>;

// ============================================================================
// TTM Metadata Schema
// ============================================================================

export const TTMMetadataSchema = z.object({
  layerCount: nonNegativeInt,
  frameCount: positiveInt,
  width: positiveInt,
  height: positiveInt,
});

export type TTMMetadata = z.infer<typeof TTMMetadataSchema>;

// ============================================================================
// TTM Export Schema
// ============================================================================

/**
 * TTM export format - supports multiple animated layers.
 * Matches TTMExport interface exactly.
 */
export const TTMExportSchema = z.object({
  referenceImage: z.string().min(1), // base64 or path
  lastFrame: z.string().optional(), // Last frame for temporal context
  layers: z.array(TTMLayerExportSchema),
  combinedMotionMask: z.string().min(1), // Base64 PNG
  modelConfig: TTMModelConfigSchema,
  metadata: TTMMetadataSchema,
});

export type TTMExport = z.infer<typeof TTMExportSchema>;

// ============================================================================
// TTM Single Layer Export Schema (Legacy)
// ============================================================================

/**
 * Legacy single-layer TTM export (backwards compatibility).
 * Matches TTMSingleLayerExport interface.
 */
export const TTMSingleLayerExportSchema = z.object({
  referenceImage: z.string().min(1),
  motionMask: z.string().min(1),
  trajectory: z.array(
    z.object({
      x: finiteNumber,
      y: finiteNumber,
    }),
  ),
  modelConfig: TTMModelConfigSchema,
});

export type TTMSingleLayerExport = z.infer<typeof TTMSingleLayerExportSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateTTMExport(data: unknown): TTMExport {
  return TTMExportSchema.parse(data);
}

export function safeValidateTTMExport(data: unknown) {
  return TTMExportSchema.safeParse(data);
}
