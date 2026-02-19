/**
 * SCAIL (Pose-Driven Video) Export Schemas
 *
 * Zod schemas for validating SCAIL export data.
 * SCAIL uses reference image (identity/appearance) + pose video/sequence for motion guidance.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  filename,
  MAX_PATH_LENGTH,
  MAX_STRING_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ═══════════════════════════════════════════════════════════════════════════

const positiveInt = z.number().int().positive();
const positiveFinite = z.number().finite().positive();

// ═══════════════════════════════════════════════════════════════════════════
// SCAIL Export Config Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * SCAIL export configuration.
 * Matches WorkflowParams.scail* properties used in generateSCAILWorkflow().
 */
export const SCAILExportConfigSchema = z.object({
  referenceImage: filename, // Reference image (identity/appearance source)
  poseVideo: filename.optional(), // Pose video filename or path
  poseDirectory: z.string().max(MAX_PATH_LENGTH).trim().optional(), // Directory of pose frame images
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  frameCount: positiveInt.max(100000), // Max 100k frames
  fps: positiveFinite.max(120), // Max 120 FPS
  prompt: z.string().max(MAX_STRING_LENGTH).trim(),
  negativePrompt: z.string().max(MAX_STRING_LENGTH).trim().optional(),
}).strict();

export type SCAILExportConfig = z.infer<typeof SCAILExportConfigSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// SCAIL Export Result Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * SCAIL export result.
 * Contains reference image and pose data paths.
 */
export const SCAILExportResultSchema = z.object({
  referenceImage: filename, // Uploaded reference image filename
  poseInput: filename, // Uploaded pose video or image sequence
  poseWidth: positiveInt.max(16384), // Max reasonable dimension
  poseHeight: positiveInt.max(16384), // Max reasonable dimension
  generationWidth: positiveInt.max(16384), // Max reasonable dimension
  generationHeight: positiveInt.max(16384), // Max reasonable dimension
  frameCount: positiveInt.max(100000), // Max 100k frames
}).strict();

export type SCAILExportResult = z.infer<typeof SCAILExportResultSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════

export function validateSCAILExportConfig(data: unknown): SCAILExportConfig {
  return SCAILExportConfigSchema.parse(data);
}

export function safeValidateSCAILExportConfig(data: unknown) {
  return SCAILExportConfigSchema.safeParse(data);
}
