/**
 * Light-X Export Schemas
 *
 * Zod schemas for validating Light-X export data.
 * Matches the exact structure returned by LightXExport interface.
 */

import { z } from "zod";
import { WanMoveTrajectorySchema } from "./wanmove-schema";

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
  matrices: z.array(
    z.array(z.array(finiteNumber).length(4)).length(4),
  ), // [frame][4][4]
  metadata: z.object({
    frameCount: z.number().int().positive(),
    fps: positiveFinite,
    fov: positiveFinite,
    nearClip: positiveFinite,
    farClip: positiveFinite,
    width: z.number().int().positive(),
    height: z.number().int().positive(),
  }),
});

export type CameraTrajectoryExport = z.infer<
  typeof CameraTrajectoryExportSchema
>;

// ============================================================================
// Light-X Relighting Config Schema
// ============================================================================

export const LightXRelightingConfigSchema = z.object({
  source: LightXRelightSourceSchema,
  textPrompt: z.string().optional(),
  referenceImage: z.string().optional(), // Base64
  hdrMap: z.string().optional(), // Base64 or path
  backgroundColor: z.string().optional(), // Hex
});

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
});

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
