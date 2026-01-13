/**
 * Normal Map Export Schemas
 *
 * Zod schemas for validating normal map export data.
 * Matches the exact structure returned by BackendDepthService.generateNormal().
 */

import { z } from "zod";

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
});

export type NormalGenerationOptions = z.infer<typeof NormalGenerationOptionsSchema>;

// ============================================================================
// Normal Generation Result Schema
// ============================================================================

/**
 * Normal map generation result.
 * Matches the exact structure returned by BackendDepthService.generateNormal().
 */
export const NormalGenerationMetadataSchema = z.object({
  method: z.string().min(1),
  width: positiveInt,
  height: positiveInt,
});

export type NormalGenerationMetadata = z.infer<typeof NormalGenerationMetadataSchema>;

export const NormalGenerationResultSchema = z.object({
  status: z.enum(["success", "error"]),
  normal: z.string(), // base64 encoded PNG (RGB normal map)
  depth: z.string().optional(), // base64 depth map used (if generated)
  fallback: z.boolean().optional(),
  message: z.string().optional(),
  metadata: NormalGenerationMetadataSchema.optional(),
});

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
