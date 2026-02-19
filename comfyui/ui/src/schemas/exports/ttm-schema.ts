/**
 * TTM (Time-to-Move) Export Schemas
 *
 * Zod schemas for validating TTM export data.
 * Matches the exact structure returned by exportForModel() for TTM target.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
  base64OrDataUrl,
  filename,
  entityId,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ═══════════════════════════════════════════════════════════════════════════

const finiteNumber = z.number().finite();
const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();

// ═══════════════════════════════════════════════════════════════════════════
// TTM Model Schema
// ═══════════════════════════════════════════════════════════════════════════

export const TTMModelSchema = z.enum(["wan", "cogvideox", "svd"]);

export type TTMModel = z.infer<typeof TTMModelSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// TTM Layer Export Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Per-layer TTM export data.
 * Matches TTMLayerExport interface exactly.
 */
export const TTMLayerExportSchema = z.object({
  layerId: entityId,
  layerName: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  motionMask: base64OrDataUrl, // Base64 PNG
  trajectory: boundedArray(
    z.object({
      frame: nonNegativeInt.max(100000), // Max 100k frames
      x: finiteNumber.max(16384), // Max reasonable coordinate
      y: finiteNumber.max(16384), // Max reasonable coordinate
    }).strict(),
    100000 // Max 100k trajectory points
  ),
  visibility: boundedArray(z.boolean(), 100000), // Max 100k visibility values
}).strict().refine(
  (data) => {
    // trajectory and visibility should have same length
    return data.trajectory.length === data.visibility.length;
  },
  { message: "trajectory and visibility arrays must have same length", path: ["visibility"] }
);

export type TTMLayerExport = z.infer<typeof TTMLayerExportSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// TTM Model Config Schema
// ═══════════════════════════════════════════════════════════════════════════

export const TTMModelConfigSchema = z.object({
  model: TTMModelSchema,
  tweakIndex: finiteNumber.max(100), // Max 100 tweak index
  tstrongIndex: finiteNumber.max(100), // Max 100 strong index
  inferenceSteps: positiveInt.max(1000), // Max 1000 inference steps
}).strict();

export type TTMModelConfig = z.infer<typeof TTMModelConfigSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// TTM Metadata Schema
// ═══════════════════════════════════════════════════════════════════════════

export const TTMMetadataSchema = z.object({
  layerCount: nonNegativeInt.max(1000), // Max 1000 layers
  frameCount: positiveInt.max(100000), // Max 100k frames
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
}).strict();

export type TTMMetadata = z.infer<typeof TTMMetadataSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// TTM Export Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * TTM export format - supports multiple animated layers.
 * Matches TTMExport interface exactly.
 */
export const TTMExportSchema = z.object({
  referenceImage: z.union([base64OrDataUrl, filename]), // base64 or path
  lastFrame: z.union([base64OrDataUrl, filename]).optional(), // Last frame for temporal context
  layers: boundedArray(TTMLayerExportSchema, 1000), // Max 1000 layers
  combinedMotionMask: base64OrDataUrl, // Base64 PNG
  modelConfig: TTMModelConfigSchema,
  metadata: TTMMetadataSchema,
}).strict().refine(
  (data) => {
    // layerCount should match layers array length
    return data.metadata.layerCount === data.layers.length;
  },
  { message: "layerCount must match layers array length", path: ["metadata", "layerCount"] }
);

export type TTMExport = z.infer<typeof TTMExportSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// TTM Single Layer Export Schema (Legacy)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Legacy single-layer TTM export (backwards compatibility).
 * Matches TTMSingleLayerExport interface.
 */
export const TTMSingleLayerExportSchema = z.object({
  referenceImage: z.union([base64OrDataUrl, filename]),
  motionMask: base64OrDataUrl,
  trajectory: boundedArray(
    z.object({
      x: finiteNumber.max(16384), // Max reasonable coordinate
      y: finiteNumber.max(16384), // Max reasonable coordinate
    }).strict(),
    100000 // Max 100k trajectory points
  ),
  modelConfig: TTMModelConfigSchema,
}).strict();

export type TTMSingleLayerExport = z.infer<typeof TTMSingleLayerExportSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════

export function validateTTMExport(data: unknown): TTMExport {
  return TTMExportSchema.parse(data);
}

export function safeValidateTTMExport(data: unknown) {
  return TTMExportSchema.safeParse(data);
}
