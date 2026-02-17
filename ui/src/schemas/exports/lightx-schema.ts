/**
 * Light-X Export Schemas
 *
 * Zod schemas for validating Light-X export data.
 * Matches the exact structure returned by LightXExport interface.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import { WanMoveTrajectorySchema } from "./wanmove-schema";
import {
  boundedArray,
  base64OrDataUrl,
  hexColor,
  MAX_STRING_LENGTH,
  MAX_PATH_LENGTH,
} from "../shared-validation";

// ============================================================================
// Primitives
// ============================================================================

const finiteNumber = z.number().finite();
const positiveFinite = z.number().finite().positive();

// ============================================================================
// Light-X Motion Style Schema
// ============================================================================

export const LightXMotionStyleSchema = z.enum([
  "gradual",
  "bullet",
  "direct",
  "dolly-zoom",
]);

export type LightXMotionStyle = z.infer<typeof LightXMotionStyleSchema>;

// ============================================================================
// Light-X Relight Source Schema
// ============================================================================

export const LightXRelightSourceSchema = z.enum([
  "text",
  "reference",
  "hdr",
  "background",
]);

export type LightXRelightSource = z.infer<typeof LightXRelightSourceSchema>;

// ============================================================================
// Camera Trajectory Export Schema
// ============================================================================

/**
 * Camera trajectory export.
 * Matches CameraTrajectoryExport interface.
 */
export const CameraTrajectoryExportSchema = z.object({
  matrices: boundedArray(
    z.array(z.array(finiteNumber).length(4)).length(4),
    100000
  ), // Max 100k frames, [frame][4][4]
  metadata: z.object({
    frameCount: z.number().int().positive().max(100000), // Max 100k frames
    fps: positiveFinite.max(120), // Max 120 FPS
    fov: positiveFinite.max(180), // Max 180 degrees FOV
    nearClip: positiveFinite.max(100000), // Max 100k units
    farClip: positiveFinite.max(100000), // Max 100k units
    width: z.number().int().positive().max(16384), // Max reasonable dimension
    height: z.number().int().positive().max(16384), // Max reasonable dimension
  }).strict().refine(
    (data) => {
      // farClip should be > nearClip
      return data.farClip > data.nearClip;
    },
    { message: "farClip must be greater than nearClip", path: ["farClip"] }
  ),
}).strict();

export type CameraTrajectoryExport = z.infer<
  typeof CameraTrajectoryExportSchema
>;

// ============================================================================
// Light-X Relighting Config Schema
// ============================================================================

export const LightXRelightingConfigSchema = z.object({
  source: LightXRelightSourceSchema,
  textPrompt: z.string().max(MAX_STRING_LENGTH).trim().optional(),
  referenceImage: base64OrDataUrl.optional(), // Base64
  hdrMap: z.union([base64OrDataUrl, z.string().max(MAX_PATH_LENGTH)]).optional(), // Base64 or path
  backgroundColor: hexColor.optional(), // Hex
}).strict();

export type LightXRelightingConfig = z.infer<
  typeof LightXRelightingConfigSchema
>;

// ============================================================================
// Light-X Export Schema
// ============================================================================

/**
 * Light-X export format.
 * Matches LightXExport interface exactly.
 */
export const LightXExportSchema = z.object({
  cameraTrajectory: CameraTrajectoryExportSchema,
  motionStyle: LightXMotionStyleSchema,
  relighting: LightXRelightingConfigSchema,
}).strict();

export type LightXExport = z.infer<typeof LightXExportSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateLightXExport(data: unknown): LightXExport {
  return LightXExportSchema.parse(data);
}

export function safeValidateLightXExport(data: unknown) {
  return LightXExportSchema.safeParse(data);
}
