/**
 * Normal Map Export Schemas
 *
 * Zod schemas for validating normal map export data.
 * Matches the exact structure returned by BackendDepthService.generateNormal().
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  base64OrDataUrl,
  MAX_NAME_LENGTH,
  MAX_STRING_LENGTH,
} from "../shared-validation";

// ============================================================================
// Primitives
// ============================================================================

const positiveInt = z.number().int().positive();
const positiveFinite = z.number().finite().positive();

// ============================================================================
// Normal Generation Options Schema
// ============================================================================

export const NormalGenerationMethodSchema = z.enum(["algebraic", "normalcrafter"]);

export type NormalGenerationMethod = z.infer<typeof NormalGenerationMethodSchema>;

export const NormalDepthModelSchema = z.enum([
  "DA3-LARGE-1.1",
  "DA3-GIANT-1.1",
  "DA3NESTED-GIANT-LARGE-1.1",
]);

export type NormalDepthModel = z.infer<typeof NormalDepthModelSchema>;

export const NormalGenerationOptionsSchema = z.object({
  method: NormalGenerationMethodSchema.optional(),
  depthModel: NormalDepthModelSchema.optional(),
}).strict();

export type NormalGenerationOptions = z.infer<typeof NormalGenerationOptionsSchema>;

// ============================================================================
// Normal Generation Result Schema
// ============================================================================

/**
 * Normal map generation result.
 * Matches the exact structure returned by BackendDepthService.generateNormal().
 */
export const NormalGenerationMetadataSchema = z.object({
  method: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
}).strict();

export type NormalGenerationMetadata = z.infer<typeof NormalGenerationMetadataSchema>;

export const NormalGenerationResultSchema = z.object({
  status: z.enum(["success", "error"]),
  normal: base64OrDataUrl, // base64 encoded PNG (RGB normal map)
  depth: base64OrDataUrl.optional(), // base64 depth map used (if generated)
  fallback: z.boolean().optional(),
  message: z.string().max(MAX_STRING_LENGTH).trim().optional(),
  metadata: NormalGenerationMetadataSchema.optional(),
}).strict();

export type NormalGenerationResult = z.infer<typeof NormalGenerationResultSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateNormalGenerationResult(
  data: unknown,
): NormalGenerationResult {
  return NormalGenerationResultSchema.parse(data);
}

export function safeValidateNormalGenerationResult(data: unknown) {
  return NormalGenerationResultSchema.safeParse(data);
}
