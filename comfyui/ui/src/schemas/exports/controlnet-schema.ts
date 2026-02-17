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
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
  filename,
  hexColor,
  MAX_NAME_LENGTH,
} from "../shared-validation";

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
  resolution: positiveInt.max(16384), // Max reasonable resolution
  threshold_low: finiteNumber.min(0).max(255).optional(), // 0-255 range
  threshold_high: finiteNumber.min(0).max(255).optional(), // 0-255 range
  detect_resolution: positiveInt.max(16384).optional(), // Max reasonable resolution
}).strict().refine(
  (data) => {
    // If both thresholds present, high should be >= low
    if (data.threshold_low !== undefined && data.threshold_high !== undefined) {
      return data.threshold_high >= data.threshold_low;
    }
    return true;
  },
  { message: "threshold_high must be >= threshold_low", path: ["threshold_high"] }
);

export type ControlNetExportConfig = z.infer<typeof ControlNetExportConfigSchema>;

// ============================================================================
// OpenPose JSON Schema (ControlNet Pose)
// ============================================================================

/**
 * OpenPose JSON format for pose export.
 * Matches the exact structure returned by exportToOpenPoseJSON().
 */
export const OpenPosePersonSchema = z.object({
  person_id: boundedArray(z.number().int(), 100), // Max 100 person IDs
  pose_keypoints_2d: boundedArray(finiteNumber, 1000), // Max 1000 2D pose keypoints
  face_keypoints_2d: boundedArray(finiteNumber, 1000), // Max 1000 2D face keypoints
  hand_left_keypoints_2d: boundedArray(finiteNumber, 500), // Max 500 2D left hand keypoints
  hand_right_keypoints_2d: boundedArray(finiteNumber, 500), // Max 500 2D right hand keypoints
  pose_keypoints_3d: boundedArray(finiteNumber, 1000), // Max 1000 3D pose keypoints
  face_keypoints_3d: boundedArray(finiteNumber, 1000), // Max 1000 3D face keypoints
  hand_left_keypoints_3d: boundedArray(finiteNumber, 500), // Max 500 3D left hand keypoints
  hand_right_keypoints_3d: boundedArray(finiteNumber, 500), // Max 500 3D right hand keypoints
}).strict();

export type OpenPosePerson = z.infer<typeof OpenPosePersonSchema>;

export const OpenPoseJSONSchema = z.object({
  version: z.number().int().nonnegative().max(100), // Max version 100
  people: boundedArray(OpenPosePersonSchema, 1000), // Max 1000 people per frame
}).strict();

export type OpenPoseJSON = z.infer<typeof OpenPoseJSONSchema>;

// ============================================================================
// Pose Export Config Schema
// ============================================================================

export const PoseExportConfigSchema = z.object({
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  startFrame: nonNegativeInt.max(100000), // Max 100k frames
  endFrame: nonNegativeInt.max(100000), // Max 100k frames
  boneWidth: positiveFinite.max(100), // Max 100px bone width
  keypointRadius: positiveFinite.max(100), // Max 100px keypoint radius
  showKeypoints: z.boolean(),
  showBones: z.boolean(),
  useOpenPoseColors: z.boolean(),
  customColor: hexColor.optional(),
  backgroundColor: hexColor,
  outputFormat: z.enum(["images", "json", "both"]),
}).strict().refine(
  (data) => {
    // endFrame should be >= startFrame
    return data.endFrame >= data.startFrame;
  },
  { message: "endFrame must be >= startFrame", path: ["endFrame"] }
);

export type PoseExportConfig = z.infer<typeof PoseExportConfigSchema>;

// ============================================================================
// Pose Export Result Schema
// ============================================================================

export const PoseSequenceMetadataSchema = z.object({
  frameCount: positiveInt.max(100000), // Max 100k frames
  fps: positiveFinite.max(120), // Max 120 FPS
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
}).strict();

export type PoseSequenceMetadata = z.infer<typeof PoseSequenceMetadataSchema>;

export const PoseSequenceJsonSchema = z.object({
  frames: boundedArray(OpenPoseJSONSchema, 100000), // Max 100k frames
  metadata: PoseSequenceMetadataSchema,
}).strict();

export type PoseSequenceJson = z.infer<typeof PoseSequenceJsonSchema>;

export const PoseExportResultSchema = z.object({
  images: boundedArray(z.instanceof(HTMLCanvasElement), 100000).optional(), // Max 100k images
  jsonFrames: boundedArray(OpenPoseJSONSchema, 100000).optional(), // Max 100k JSON frames
  sequenceJson: PoseSequenceJsonSchema.optional(),
}).strict();

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
  files: boundedArray(filename, 100000), // Max 100k files
  format: ControlNetTypeSchema,
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  frameCount: positiveInt.max(100000), // Max 100k frames
}).strict().refine(
  (data) => {
    // files array length should match frameCount
    return data.files.length === data.frameCount;
  },
  { message: "files array length must match frameCount", path: ["files"] }
);

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
