/**
 * SCAIL (Pose-Driven Video) Export Schemas
 *
 * Zod schemas for validating SCAIL export data.
 * SCAIL uses reference image (identity/appearance) + pose video/sequence for motion guidance.
 */

import { z } from "zod";

// ============================================================================
// Primitives
// ============================================================================

const positiveInt = z.number().int().positive();
const positiveFinite = z.number().finite().positive();

// ============================================================================
// SCAIL Export Config Schema
// ============================================================================

/**
 * SCAIL export configuration.
 * Matches WorkflowParams.scail* properties used in generateSCAILWorkflow().
 */
export const SCAILExportConfigSchema = z.object({
  referenceImage: z.string().min(1), // Reference image (identity/appearance source)
  poseVideo: z.string().optional(), // Pose video filename or path
  poseDirectory: z.string().optional(), // Directory of pose frame images
  width: positiveInt,
  height: positiveInt,
  frameCount: positiveInt,
  fps: positiveFinite,
  prompt: z.string(),
  negativePrompt: z.string().optional(),
});

export type SCAILExportConfig = z.infer<typeof SCAILExportConfigSchema>;

// ============================================================================
// SCAIL Export Result Schema
// ============================================================================

/**
 * SCAIL export result.
 * Contains reference image and pose data paths.
 */
export const SCAILExportResultSchema = z.object({
  referenceImage: z.string().min(1), // Uploaded reference image filename
  poseInput: z.string().min(1), // Uploaded pose video or image sequence
  poseWidth: positiveInt, // Pose resolution (half of generation resolution)
  poseHeight: positiveInt,
  generationWidth: positiveInt,
  generationHeight: positiveInt,
  frameCount: positiveInt,
});

export type SCAILExportResult = z.infer<typeof SCAILExportResultSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateSCAILExportConfig(data: unknown): SCAILExportConfig {
  return SCAILExportConfigSchema.parse(data);
}

export function safeValidateSCAILExportConfig(data: unknown) {
  return SCAILExportConfigSchema.safeParse(data);
}
