/**
 * ControlNet Export Schemas
 *
 * Zod schemas for validating ControlNet export data formats.
 * These define the contract between TypeScript and Python ComfyUI nodes.
 *
 * ControlNet types:
 * - depth: Depth map for ControlNet
 * - canny: Canny edge detection
 * - lineart: Line art extraction
 * - softedge: Soft edge detection (HED/PIDI)
 * - normal: Normal map
 * - scribble: Scribble/sketch input
 * - seg: Semantic segmentation
 * - pose: OpenPose skeleton
 */

import { z } from "zod";

// ============================================================================
// Primitives
// ============================================================================

const finiteNumber = z.number().finite();
const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();
const positiveFinite = z.number().finite().positive();

// ============================================================================
// ControlNet Type Schema
// ============================================================================

export const ControlNetTypeSchema = z.enum([
  "depth",
  "canny",
  "lineart",
  "softedge",
  "normal",
  "scribble",
  "seg",
  "pose",
]);

export type ControlNetType = z.infer<typeof ControlNetTypeSchema>;

// ============================================================================
// ControlNet Export Config Schema
// ============================================================================

export const ControlNetExportConfigSchema = z.object({
  type: ControlNetTypeSchema,
  resolution: positiveInt,
  threshold_low: finiteNumber.optional(),
  threshold_high: finiteNumber.optional(),
  detect_resolution: positiveInt.optional(),
});

export type ControlNetExportConfig = z.infer<typeof ControlNetExportConfigSchema>;

// ============================================================================
// OpenPose JSON Schema (ControlNet Pose)
// ============================================================================

/**
 * OpenPose JSON format for pose export.
 * Matches the exact structure returned by exportToOpenPoseJSON().
 */
export const OpenPosePersonSchema = z.object({
  person_id: z.array(z.number().int()),
  pose_keypoints_2d: z.array(finiteNumber),
  face_keypoints_2d: z.array(finiteNumber),
  hand_left_keypoints_2d: z.array(finiteNumber),
  hand_right_keypoints_2d: z.array(finiteNumber),
  pose_keypoints_3d: z.array(finiteNumber),
  face_keypoints_3d: z.array(finiteNumber),
  hand_left_keypoints_3d: z.array(finiteNumber),
  hand_right_keypoints_3d: z.array(finiteNumber),
});

export type OpenPosePerson = z.infer<typeof OpenPosePersonSchema>;

export const OpenPoseJSONSchema = z.object({
  version: z.number().int().nonnegative(),
  people: z.array(OpenPosePersonSchema),
});

export type OpenPoseJSON = z.infer<typeof OpenPoseJSONSchema>;

// ============================================================================
// Pose Export Config Schema
// ============================================================================

export const PoseExportConfigSchema = z.object({
  width: positiveInt,
  height: positiveInt,
  startFrame: nonNegativeInt,
  endFrame: nonNegativeInt,
  boneWidth: positiveFinite,
  keypointRadius: positiveFinite,
  showKeypoints: z.boolean(),
  showBones: z.boolean(),
  useOpenPoseColors: z.boolean(),
  customColor: z.string().optional(),
  backgroundColor: z.string(),
  outputFormat: z.enum(["images", "json", "both"]),
});

export type PoseExportConfig = z.infer<typeof PoseExportConfigSchema>;

// ============================================================================
// Pose Export Result Schema
// ============================================================================

export const PoseSequenceMetadataSchema = z.object({
  frameCount: positiveInt,
  fps: positiveFinite,
  width: positiveInt,
  height: positiveInt,
});

export type PoseSequenceMetadata = z.infer<typeof PoseSequenceMetadataSchema>;

export const PoseSequenceJsonSchema = z.object({
  frames: z.array(OpenPoseJSONSchema),
  metadata: PoseSequenceMetadataSchema,
});

export type PoseSequenceJson = z.infer<typeof PoseSequenceJsonSchema>;

export const PoseExportResultSchema = z.object({
  images: z.array(z.instanceof(HTMLCanvasElement)).optional(),
  jsonFrames: z.array(OpenPoseJSONSchema).optional(),
  sequenceJson: PoseSequenceJsonSchema.optional(),
});

export type PoseExportResult = z.infer<typeof PoseExportResultSchema>;

// ============================================================================
// ControlNet Export Result Schema (Generic)
// ============================================================================

/**
 * Generic ControlNet export result.
 * For canny, lineart, softedge, normal, scribble, seg:
 * Returns array of filenames (PNG images).
 */
export const ControlNetExportResultSchema = z.object({
  files: z.array(z.string().min(1)),
  format: ControlNetTypeSchema,
  width: positiveInt,
  height: positiveInt,
  frameCount: positiveInt,
});

export type ControlNetExportResult = z.infer<typeof ControlNetExportResultSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateOpenPoseJSON(data: unknown): OpenPoseJSON {
  return OpenPoseJSONSchema.parse(data);
}

export function safeValidateOpenPoseJSON(data: unknown) {
  return OpenPoseJSONSchema.safeParse(data);
}

export function validatePoseExportResult(data: unknown): PoseExportResult {
  return PoseExportResultSchema.parse(data);
}

export function safeValidatePoseExportResult(data: unknown) {
  return PoseExportResultSchema.safeParse(data);
}
