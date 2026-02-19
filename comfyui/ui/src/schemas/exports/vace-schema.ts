/**
 * VACE (Video Animation Control Engine) Export Schemas
 *
 * Zod schemas for validating VACE export data.
 * Matches VACEExportConfig and related interfaces.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
  entityId,
  hexColor,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ═══════════════════════════════════════════════════════════════════════════

const finiteNumber = z.number().finite();
const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();
const positiveFinite = z.number().finite().positive();
const normalized01 = z.number().finite().min(0).max(1);

// ═══════════════════════════════════════════════════════════════════════════
// Path Follower Shape Schema
// ═══════════════════════════════════════════════════════════════════════════

export const PathFollowerShapeSchema = z.enum([
  "circle",
  "square",
  "triangle",
  "diamond",
  "arrow",
  "custom",
]);

export type PathFollowerShape = z.infer<typeof PathFollowerShapeSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Path Follower Easing Schema
// ═══════════════════════════════════════════════════════════════════════════

export const PathFollowerEasingSchema = z.enum([
  "linear",
  "ease-in",
  "ease-out",
  "ease-in-out",
  "ease-in-cubic",
  "ease-out-cubic",
]);

export type PathFollowerEasing = z.infer<typeof PathFollowerEasingSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Spline Control Point Schema
// ═══════════════════════════════════════════════════════════════════════════

export const SplineControlPointSchema = z.object({
  x: finiteNumber.max(16384), // Max reasonable coordinate
  y: finiteNumber.max(16384), // Max reasonable coordinate
  z: finiteNumber.max(16384).optional(), // Max reasonable coordinate
  handleIn: z
    .object({
      x: finiteNumber.max(16384), // Max reasonable coordinate
      y: finiteNumber.max(16384), // Max reasonable coordinate
      z: finiteNumber.max(16384).optional(), // Max reasonable coordinate
    })
    .strict()
    .nullable()
    .optional(),
  handleOut: z
    .object({
      x: finiteNumber.max(16384), // Max reasonable coordinate
      y: finiteNumber.max(16384), // Max reasonable coordinate
      z: finiteNumber.max(16384).optional(), // Max reasonable coordinate
    })
    .strict()
    .nullable()
    .optional(),
}).strict();

export type SplineControlPoint = z.infer<typeof SplineControlPointSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Path Follower Config Schema
// ═══════════════════════════════════════════════════════════════════════════

export const PathFollowerConfigSchema = z.object({
  id: entityId,
  controlPoints: boundedArray(SplineControlPointSchema, 100000), // Max 100k control points
  closed: z.boolean(),
  shape: PathFollowerShapeSchema,
  size: z.tuple([positiveFinite.max(10000), positiveFinite.max(10000)]), // Max 10k px size
  fillColor: hexColor,
  strokeColor: hexColor.optional(),
  strokeWidth: positiveFinite.max(1000).optional(), // Max 1000px stroke width
  startFrame: nonNegativeInt.max(100000), // Max 100k frames
  duration: positiveInt.max(100000), // Max 100k frames duration
  easing: PathFollowerEasingSchema,
  alignToPath: z.boolean(),
  rotationOffset: finiteNumber.max(360), // Max 360 degrees offset
  loop: z.boolean(),
  loopMode: z.enum(["restart", "pingpong"]).optional(),
  scaleStart: normalized01.optional(),
  scaleEnd: normalized01.optional(),
  opacityStart: normalized01.optional(),
  opacityEnd: normalized01.optional(),
}).strict().refine(
  (data) => {
    // Closed paths should have at least 3 control points
    if (data.closed && data.controlPoints.length < 3) {
      return false;
    }
    return true;
  },
  { message: "Closed paths must have at least 3 control points", path: ["controlPoints"] }
);

export type PathFollowerConfig = z.infer<typeof PathFollowerConfigSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// VACE Export Config Schema
// ═══════════════════════════════════════════════════════════════════════════

export const VACEExportConfigSchema = z.object({
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  startFrame: nonNegativeInt.max(100000), // Max 100k frames
  endFrame: nonNegativeInt.max(100000), // Max 100k frames
  frameRate: positiveFinite.max(120), // Max 120 FPS
  backgroundColor: hexColor,
  pathFollowers: boundedArray(PathFollowerConfigSchema, 1000), // Max 1000 path followers
  outputFormat: z.enum(["canvas", "webm", "frames"]),
  antiAlias: z.boolean(),
}).strict().refine(
  (data) => {
    // endFrame should be >= startFrame
    return data.endFrame >= data.startFrame;
  },
  { message: "endFrame must be >= startFrame", path: ["endFrame"] }
);

export type VACEExportConfig = z.infer<typeof VACEExportConfigSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Path Follower State Schema
// ═══════════════════════════════════════════════════════════════════════════

export const PathFollowerStateSchema = z.object({
  position: z.object({
    x: finiteNumber.max(16384), // Max reasonable coordinate
    y: finiteNumber.max(16384), // Max reasonable coordinate
  }).strict(),
  rotation: finiteNumber.max(6.28318), // Max 2π radians (360 degrees)
  scale: positiveFinite.max(100), // Max 100x scale
  opacity: normalized01,
  progress: normalized01, // 0-1 along path
  visible: z.boolean(),
}).strict();

export type PathFollowerState = z.infer<typeof PathFollowerStateSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// VACE Frame Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * VACE frame export.
 * Note: canvas is HTMLCanvasElement (runtime type, not validated by Zod).
 */
export const VACEFrameMetadataSchema = z.object({
  frameNumber: nonNegativeInt.max(100000), // Max 100k frames
  states: z.record(z.string().max(200), PathFollowerStateSchema).refine(
    (states) => Object.keys(states).length <= 1000,
    { message: "Maximum 1000 path followers per frame" }
  ),
}).strict();

export type VACEFrameMetadata = z.infer<typeof VACEFrameMetadataSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════

export function validateVACEExportConfig(data: unknown): VACEExportConfig {
  return VACEExportConfigSchema.parse(data);
}

export function safeValidateVACEExportConfig(data: unknown) {
  return VACEExportConfigSchema.safeParse(data);
}
