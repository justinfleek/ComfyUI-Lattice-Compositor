/**
 * VACE (Video Animation Control Engine) Export Schemas
 *
 * Zod schemas for validating VACE export data.
 * Matches VACEExportConfig and related interfaces.
 */

import { z } from "zod";

// ============================================================================
// Primitives
// ============================================================================

const finiteNumber = z.number().finite();
const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();
const positiveFinite = z.number().finite().positive();
const normalized01 = z.number().finite().min(0).max(1);

// ============================================================================
// Path Follower Shape Schema
// ============================================================================

export const PathFollowerShapeSchema = z.enum([
  "circle",
  "square",
  "triangle",
  "diamond",
  "arrow",
  "custom",
]);

export type PathFollowerShape = z.infer<typeof PathFollowerShapeSchema>;

// ============================================================================
// Path Follower Easing Schema
// ============================================================================

export const PathFollowerEasingSchema = z.enum([
  "linear",
  "ease-in",
  "ease-out",
  "ease-in-out",
  "ease-in-cubic",
  "ease-out-cubic",
]);

export type PathFollowerEasing = z.infer<typeof PathFollowerEasingSchema>;

// ============================================================================
// Spline Control Point Schema
// ============================================================================

export const SplineControlPointSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber.optional(),
  handleIn: z
    .object({
      x: finiteNumber,
      y: finiteNumber,
      z: finiteNumber.optional(),
    })
    .nullable()
    .optional(),
  handleOut: z
    .object({
      x: finiteNumber,
      y: finiteNumber,
      z: finiteNumber.optional(),
    })
    .nullable()
    .optional(),
});

export type SplineControlPoint = z.infer<typeof SplineControlPointSchema>;

// ============================================================================
// Path Follower Config Schema
// ============================================================================

export const PathFollowerConfigSchema = z.object({
  id: z.string().min(1),
  controlPoints: z.array(SplineControlPointSchema),
  closed: z.boolean(),
  shape: PathFollowerShapeSchema,
  size: z.tuple([positiveFinite, positiveFinite]),
  fillColor: z.string(),
  strokeColor: z.string().optional(),
  strokeWidth: positiveFinite.optional(),
  startFrame: nonNegativeInt,
  duration: positiveInt,
  easing: PathFollowerEasingSchema,
  alignToPath: z.boolean(),
  rotationOffset: finiteNumber,
  loop: z.boolean(),
  loopMode: z.enum(["restart", "pingpong"]).optional(),
  scaleStart: normalized01.optional(),
  scaleEnd: normalized01.optional(),
  opacityStart: normalized01.optional(),
  opacityEnd: normalized01.optional(),
});

export type PathFollowerConfig = z.infer<typeof PathFollowerConfigSchema>;

// ============================================================================
// VACE Export Config Schema
// ============================================================================

export const VACEExportConfigSchema = z.object({
  width: positiveInt,
  height: positiveInt,
  startFrame: nonNegativeInt,
  endFrame: nonNegativeInt,
  frameRate: positiveFinite,
  backgroundColor: z.string(),
  pathFollowers: z.array(PathFollowerConfigSchema),
  outputFormat: z.enum(["canvas", "webm", "frames"]),
  antiAlias: z.boolean(),
});

export type VACEExportConfig = z.infer<typeof VACEExportConfigSchema>;

// ============================================================================
// Path Follower State Schema
// ============================================================================

export const PathFollowerStateSchema = z.object({
  position: z.object({
    x: finiteNumber,
    y: finiteNumber,
  }),
  rotation: finiteNumber, // radians
  scale: positiveFinite,
  opacity: normalized01,
  progress: normalized01, // 0-1 along path
  visible: z.boolean(),
});

export type PathFollowerState = z.infer<typeof PathFollowerStateSchema>;

// ============================================================================
// VACE Frame Schema
// ============================================================================

/**
 * VACE frame export.
 * Note: canvas is HTMLCanvasElement (runtime type, not validated by Zod).
 */
export const VACEFrameMetadataSchema = z.object({
  frameNumber: nonNegativeInt,
  states: z.record(z.string(), PathFollowerStateSchema),
});

export type VACEFrameMetadata = z.infer<typeof VACEFrameMetadataSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateVACEExportConfig(data: unknown): VACEExportConfig {
  return VACEExportConfigSchema.parse(data);
}

export function safeValidateVACEExportConfig(data: unknown) {
  return VACEExportConfigSchema.safeParse(data);
}
