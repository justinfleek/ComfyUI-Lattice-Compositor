/**
 * ComfyUI Schema
 *
 * Zod schemas for validating ComfyUI integration types.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
  filename,
  url,
  jsonSerializable,
  MAX_NAME_LENGTH,
  MAX_STRING_LENGTH,
  MAX_ARRAY_LENGTH,
  MAX_URL_LENGTH,
  MAX_PATH_LENGTH,
  MAX_FILENAME_LENGTH,
} from "./shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ═══════════════════════════════════════════════════════════════════════════

const finiteNumber = z.number().finite();
const positiveFinite = z.number().finite().positive();
const nonNegativeFinite = z.number().finite().nonnegative();
const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();
const normalized0100 = z.number().finite().min(0).max(100);

// ═══════════════════════════════════════════════════════════════════════════
// Export Target
// ═══════════════════════════════════════════════════════════════════════════

export const ExportTargetSchema = z.enum([
  "wan22-i2v",
  "wan22-t2v",
  "wan22-fun-camera",
  "wan22-first-last",
  "uni3c-camera",
  "uni3c-motion",
  "motionctrl",
  "motionctrl-svd",
  "cogvideox",
  "controlnet-depth",
  "controlnet-canny",
  "controlnet-lineart",
  "controlnet-pose",
  "animatediff-cameractrl",
  "custom-workflow",
  "light-x",
  "wan-move",
  "ati",
  "ttm",
  "ttm-wan",
  "ttm-cogvideox",
  "ttm-svd",
  "scail",
  "camera-comfyui",
]);

export type ExportTarget = z.infer<typeof ExportTargetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Depth Map Format
// ═══════════════════════════════════════════════════════════════════════════

export const DepthMapFormatSchema = z.enum([
  "raw",
  "midas",
  "zoe",
  "depth-pro",
  "depth-anything",
  "marigold",
  "normalized",
]);

export type DepthMapFormat = z.infer<typeof DepthMapFormatSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Control Type
// ═══════════════════════════════════════════════════════════════════════════

export const ControlTypeSchema = z.enum([
  "depth",
  "canny",
  "lineart",
  "softedge",
  "normal",
  "scribble",
  "seg",
  "pose",
]);

export type ControlType = z.infer<typeof ControlTypeSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Depth Export Options
// ═══════════════════════════════════════════════════════════════════════════

export const DepthExportOptionsSchema = z.object({
  format: DepthMapFormatSchema,
  bitDepth: z.union([z.literal(8), z.literal(16), z.literal(32)]),
  invert: z.boolean(),
  normalize: z.boolean(),
  colormap: z.enum(["grayscale", "viridis", "magma", "plasma", "inferno", "turbo"]),
  nearClip: finiteNumber.max(100000), // Max 100k units
  farClip: finiteNumber.max(100000), // Max 100k units
}).strict().refine(
  (data) => {
    // farClip should be > nearClip
    return data.farClip > data.nearClip;
  },
  { message: "farClip must be greater than nearClip", path: ["farClip"] }
);

export type DepthExportOptions = z.infer<typeof DepthExportOptionsSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Control Export Config
// ═══════════════════════════════════════════════════════════════════════════

export const ControlExportConfigSchema = z.object({
  type: ControlTypeSchema,
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

export type ControlExportConfig = z.infer<typeof ControlExportConfigSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Export Config
// ═══════════════════════════════════════════════════════════════════════════

export const ExportConfigSchema = z.object({
  target: ExportTargetSchema,
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  frameCount: positiveInt.max(100000), // Max 100k frames
  fps: positiveFinite.max(120), // Max 120 FPS
  startFrame: nonNegativeInt.max(100000), // Max 100k frames
  endFrame: nonNegativeInt.max(100000), // Max 100k frames
  outputDir: z.string().max(MAX_PATH_LENGTH).trim(),
  filenamePrefix: filename,
  exportDepthMap: z.boolean(),
  exportControlImages: z.boolean(),
  exportCameraData: z.boolean(),
  exportReferenceFrame: z.boolean(),
  exportLastFrame: z.boolean(),
  depthFormat: DepthMapFormatSchema,
  controlType: ControlTypeSchema.optional(),
  prompt: z.string().max(MAX_STRING_LENGTH).trim(),
  negativePrompt: z.string().max(MAX_STRING_LENGTH).trim(),
  seed: z.number().int().min(-1).max(2147483647).optional(), // Max 32-bit signed int
  steps: positiveInt.max(1000).optional(), // Max 1000 steps
  cfgScale: positiveFinite.max(100).optional(), // Max 100 CFG scale
  comfyuiServer: url.optional(),
  autoQueueWorkflow: z.boolean(),
  workflowTemplate: z.string().max(MAX_STRING_LENGTH).trim().optional(),
}).strict().refine(
  (data) => {
    // endFrame should be >= startFrame
    return data.endFrame >= data.startFrame;
  },
  { message: "endFrame must be >= startFrame", path: ["endFrame"] }
).refine(
  (data) => {
    // endFrame should be < frameCount
    return data.endFrame < data.frameCount;
  },
  { message: "endFrame must be < frameCount", path: ["endFrame"] }
);

export type ExportConfig = z.infer<typeof ExportConfigSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Export Result
// ═══════════════════════════════════════════════════════════════════════════

export const ExportResultSchema = z.object({
  success: z.boolean(),
  outputFiles: z.object({
    referenceImage: filename.optional(),
    lastImage: filename.optional(),
    depthSequence: boundedArray(filename, 100000).optional(), // Max 100k depth frames
    controlSequence: boundedArray(filename, 100000).optional(), // Max 100k control frames
    cameraData: filename.optional(),
    workflowJson: z.string().max(MAX_STRING_LENGTH).optional(),
    promptId: z.string().max(200).trim().optional(),
  }).strict(),
  errors: boundedArray(z.string().max(MAX_STRING_LENGTH), 1000), // Max 1000 errors
  warnings: boundedArray(z.string().max(MAX_STRING_LENGTH), 1000), // Max 1000 warnings
  duration: nonNegativeFinite.max(86400), // Max 24 hours duration
}).strict();

export type ExportResult = z.infer<typeof ExportResultSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Camera Formats
// ═══════════════════════════════════════════════════════════════════════════

// MotionCtrl
export const MotionCtrlPoseSchema = z.object({
  RT: z.array(z.array(finiteNumber).length(4)).length(4),
}).strict();

export type MotionCtrlPose = z.infer<typeof MotionCtrlPoseSchema>;

export const MotionCtrlCameraDataSchema = z.object({
  camera_poses: boundedArray(MotionCtrlPoseSchema, 100000), // Max 100k camera poses
}).strict();

export type MotionCtrlCameraData = z.infer<typeof MotionCtrlCameraDataSchema>;

// MotionCtrl-SVD
export const MotionCtrlSVDPresetSchema = z.enum([
  "zoom_in",
  "zoom_out",
  "pan_left",
  "pan_right",
  "pan_up",
  "pan_down",
  "rotate_cw",
  "rotate_ccw",
  "static",
]);

export type MotionCtrlSVDPreset = z.infer<typeof MotionCtrlSVDPresetSchema>;

export const MotionCtrlSVDCameraDataSchema = z.object({
  motion_camera: MotionCtrlSVDPresetSchema,
  camera_poses: z.string().max(MAX_STRING_LENGTH).optional(),
}).strict();

export type MotionCtrlSVDCameraData = z.infer<typeof MotionCtrlSVDCameraDataSchema>;

// Wan 2.2 Fun Camera
export const Wan22CameraMotionSchema = z.enum([
  "Static",
  "Pan Up",
  "Pan Down",
  "Pan Left",
  "Pan Right",
  "Zoom In",
  "Zoom Out",
  "Pan Up + Zoom In",
  "Pan Up + Zoom Out",
  "Pan Down + Zoom In",
  "Pan Down + Zoom Out",
  "Pan Left + Zoom In",
  "Pan Left + Zoom Out",
  "Pan Right + Zoom In",
  "Pan Right + Zoom Out",
  "Orbital Left",
  "Orbital Right",
]);

export type Wan22CameraMotion = z.infer<typeof Wan22CameraMotionSchema>;

export const Wan22FunCameraDataSchema = z.object({
  camera_motion: Wan22CameraMotionSchema,
}).strict();

export type Wan22FunCameraData = z.infer<typeof Wan22FunCameraDataSchema>;

// Uni3C
export const Uni3CCameraTrajectorySchema = z.object({
  zoom: finiteNumber.min(0.1).max(100), // Reasonable zoom range
  x_offset: finiteNumber.max(10000), // Max 10k units offset
  y_offset: finiteNumber.max(10000), // Max 10k units offset
  z_offset: finiteNumber.max(10000), // Max 10k units offset
  pitch: finiteNumber.max(180), // Max 180 degrees
  yaw: finiteNumber.max(360), // Max 360 degrees
  roll: finiteNumber.max(360), // Max 360 degrees
}).strict();

export type Uni3CCameraTrajectory = z.infer<typeof Uni3CCameraTrajectorySchema>;

export const Uni3CTrajTypeSchema = z.enum([
  "custom",
  "free1",
  "free2",
  "free3",
  "free4",
  "free5",
  "swing1",
  "swing2",
  "orbit",
]);

export type Uni3CTrajType = z.infer<typeof Uni3CTrajTypeSchema>;

export const Uni3CKeyframeSchema = z.object({
  frame: nonNegativeInt.max(100000), // Max 100k frames
  params: Uni3CCameraTrajectorySchema,
  interpolation: z.enum(["linear", "bezier"]),
}).strict();

export type Uni3CKeyframe = z.infer<typeof Uni3CKeyframeSchema>;

export const Uni3CCameraDataSchema = z.object({
  traj_type: Uni3CTrajTypeSchema,
  custom_trajectory: boundedArray(Uni3CCameraTrajectorySchema, 100000).optional(), // Max 100k trajectory points
  keyframes: boundedArray(Uni3CKeyframeSchema, 100000).optional(), // Max 100k keyframes
}).strict();

export type Uni3CCameraData = z.infer<typeof Uni3CCameraDataSchema>;

// AnimateDiff CameraCtrl
export const CameraCtrlMotionTypeSchema = z.enum([
  "Static",
  "Move Forward",
  "Move Backward",
  "Move Left",
  "Move Right",
  "Move Up",
  "Move Down",
  "Rotate Left",
  "Rotate Right",
  "Rotate Up",
  "Rotate Down",
  "Roll Left",
  "Roll Right",
]);

export type CameraCtrlMotionType = z.infer<typeof CameraCtrlMotionTypeSchema>;

export const CameraCtrlPosesSchema = z.object({
  motion_type: CameraCtrlMotionTypeSchema,
  speed: finiteNumber.max(100), // Max 100x speed
  frame_length: positiveInt.max(100000), // Max 100k frames
  prev_poses: boundedArray(boundedArray(finiteNumber, 16), 100000).optional(), // Max 100k poses, 16 values each
}).strict();

export type CameraCtrlPoses = z.infer<typeof CameraCtrlPosesSchema>;

// Full Camera Export
export const FullCameraFrameSchema = z.object({
  frame: nonNegativeInt.max(100000), // Max 100k frames
  timestamp: nonNegativeFinite.max(86400), // Max 24 hours timestamp
  view_matrix: z.array(z.array(finiteNumber).length(4)).length(4), // 4x4 matrix
  projection_matrix: z.array(z.array(finiteNumber).length(4)).length(4), // 4x4 matrix
  position: z.tuple([finiteNumber, finiteNumber, finiteNumber]),
  rotation: z.tuple([finiteNumber.max(360), finiteNumber.max(360), finiteNumber.max(360)]), // Max 360 degrees each
  fov: positiveFinite.max(180), // Max 180 degrees FOV
  focal_length: positiveFinite.max(10000), // Max 10k mm focal length
  focus_distance: nonNegativeFinite.max(100000), // Max 100k units focus distance
}).strict();

export type FullCameraFrame = z.infer<typeof FullCameraFrameSchema>;

export const FullCameraExportSchema = z.object({
  frames: boundedArray(FullCameraFrameSchema, 100000), // Max 100k frames
  metadata: z.object({
    width: positiveInt.max(16384), // Max reasonable dimension
    height: positiveInt.max(16384), // Max reasonable dimension
    fps: positiveFinite.max(120), // Max 120 FPS
    total_frames: positiveInt.max(100000), // Max 100k frames
    camera_type: z.string().max(MAX_NAME_LENGTH).trim(),
    film_size: positiveFinite.max(100), // Max 100mm film size
  }).strict(),
}).strict();

export type FullCameraExport = z.infer<typeof FullCameraExportSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// ComfyUI Types
// ═══════════════════════════════════════════════════════════════════════════

export const NodeConnectionSchema = z.tuple([
  z.string().max(200).trim(), // Node ID
  z.number().int().min(0).max(1000), // Port index
]);

export type NodeConnection = z.infer<typeof NodeConnectionSchema>;

export const ComfyUINodeSchema = z.object({
  class_type: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  inputs: z.record(z.string().max(200), jsonSerializable).refine(
    (inputs) => Object.keys(inputs).length <= 1000,
    { message: "Maximum 1000 inputs per node" }
  ),
  _meta: z.object({
    title: z.string().max(MAX_NAME_LENGTH).trim(),
  }).strict().optional(),
}).strict();

export type ComfyUINode = z.infer<typeof ComfyUINodeSchema>;

export const ComfyUIWorkflowSchema = z.record(z.string().max(200), ComfyUINodeSchema).refine(
  (workflow) => Object.keys(workflow).length <= 10000,
  { message: "Maximum 10000 nodes per workflow" }
);

export type ComfyUIWorkflow = z.infer<typeof ComfyUIWorkflowSchema>;

export const ComfyUIPromptResultSchema = z.object({
  prompt_id: z.string().min(1).max(200).trim(),
  number: nonNegativeInt.max(1000000), // Max 1M prompt number
  node_errors: z.record(z.string().max(200), z.string().max(MAX_STRING_LENGTH)).refine(
    (errors) => Object.keys(errors).length <= 1000,
    { message: "Maximum 1000 node errors" }
  ).optional(),
}).strict();

export type ComfyUIPromptResult = z.infer<typeof ComfyUIPromptResultSchema>;

export const ComfyUIImageOutputSchema = z.object({
  filename: filename,
  subfolder: z.string().max(MAX_PATH_LENGTH).trim(),
  type: z.string().max(50).trim(), // Output type
}).strict();

export type ComfyUIImageOutput = z.infer<typeof ComfyUIImageOutputSchema>;

export const ComfyUIHistoryEntrySchema = z.object({
  prompt: ComfyUIWorkflowSchema,
  outputs: z.record(z.string().max(200), z.object({
    images: boundedArray(ComfyUIImageOutputSchema, 10000).optional(), // Max 10k images
    gifs: boundedArray(ComfyUIImageOutputSchema, 10000).optional(), // Max 10k GIFs
  }).strict()).refine(
    (outputs) => Object.keys(outputs).length <= 1000,
    { message: "Maximum 1000 output nodes" }
  ),
  status: z.object({
    status_str: z.string().max(200).trim(),
    completed: z.boolean(),
    messages: boundedArray(z.string().max(MAX_STRING_LENGTH), 1000), // Max 1000 messages
  }).strict(),
}).strict();

export type ComfyUIHistoryEntry = z.infer<typeof ComfyUIHistoryEntrySchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Video Output Types
// ═══════════════════════════════════════════════════════════════════════════

export const VideoFormatSchema = z.enum(["mp4", "webm", "gif", "webp", "image_sequence"]);

export type VideoFormat = z.infer<typeof VideoFormatSchema>;

export const VideoCodecSchema = z.enum(["h264", "h265", "vp9", "av1"]);

export type VideoCodec = z.infer<typeof VideoCodecSchema>;

export const FrameSequenceFormatSchema = z.enum(["png", "jpeg", "webp", "tiff", "exr", "dpx"]);

export type FrameSequenceFormat = z.infer<typeof FrameSequenceFormatSchema>;

export const FrameSequenceOptionsSchema = z.object({
  format: FrameSequenceFormatSchema,
  quality: normalized0100,
  filenamePattern: z.string().max(MAX_FILENAME_LENGTH).trim(),
  outputDir: z.string().max(MAX_PATH_LENGTH).trim(),
  bitDepth: z.union([z.literal(8), z.literal(10), z.literal(16), z.literal(32)]).optional(),
  colorSpace: z.enum(["sRGB", "Linear", "ACEScg", "Rec709"]).optional(),
}).strict();

export type FrameSequenceOptions = z.infer<typeof FrameSequenceOptionsSchema>;

export const VideoEncoderOptionsSchema = z.object({
  format: VideoFormatSchema,
  codec: VideoCodecSchema.optional(),
  fps: positiveFinite.max(120), // Max 120 FPS
  quality: normalized0100,
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  loop: z.boolean().optional(),
}).strict();

export type VideoEncoderOptions = z.infer<typeof VideoEncoderOptionsSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Progress Tracking
// ═══════════════════════════════════════════════════════════════════════════

export const ExportStageSchema = z.enum([
  "preparing",
  "rendering_frames",
  "rendering_depth",
  "rendering_control",
  "exporting_camera",
  "generating_workflow",
  "uploading",
  "queuing",
  "generating",
  "downloading",
  "complete",
  "error",
]);

export type ExportStage = z.infer<typeof ExportStageSchema>;

export const ExportProgressSchema = z.object({
  stage: ExportStageSchema,
  stageProgress: normalized0100,
  overallProgress: normalized0100,
  currentFrame: nonNegativeInt.max(100000).optional(), // Max 100k frames
  totalFrames: positiveInt.max(100000).optional(), // Max 100k frames
  message: z.string().max(MAX_STRING_LENGTH).trim(),
  preview: url.optional(),
}).strict().refine(
  (data) => {
    // If both present, currentFrame should be <= totalFrames
    if (data.currentFrame !== undefined && data.totalFrames !== undefined) {
      return data.currentFrame <= data.totalFrames;
    }
    return true;
  },
  { message: "currentFrame must be <= totalFrames", path: ["currentFrame"] }
);

export type ExportProgress = z.infer<typeof ExportProgressSchema>;

export const GenerationStatusSchema = z.enum([
  "queued",
  "executing",
  "completed",
  "error",
]);

export type GenerationStatus = z.infer<typeof GenerationStatusSchema>;

export const GenerationProgressSchema = z.object({
  status: GenerationStatusSchema,
  currentNode: z.string().max(MAX_NAME_LENGTH).trim().optional(),
  currentStep: nonNegativeInt.max(1000000).optional(), // Max 1M steps
  totalSteps: positiveInt.max(1000000).optional(), // Max 1M steps
  progress: normalized0100.optional(),
  preview: url.optional(),
  errorMessage: z.string().max(MAX_STRING_LENGTH).trim().optional(),
}).strict().refine(
  (data) => {
    // If both present, currentStep should be <= totalSteps
    if (data.currentStep !== undefined && data.totalSteps !== undefined) {
      return data.currentStep <= data.totalSteps;
    }
    return true;
  },
  { message: "currentStep must be <= totalSteps", path: ["currentStep"] }
);

export type GenerationProgress = z.infer<typeof GenerationProgressSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Client Types
// ═══════════════════════════════════════════════════════════════════════════

export const ComfyUIClientConfigSchema = z.object({
  serverAddress: url,
  clientId: z.string().max(200).trim().optional(),
}).strict();

export type ComfyUIClientConfig = z.infer<typeof ComfyUIClientConfigSchema>;

export const UploadResultSchema = z.object({
  name: filename,
  subfolder: z.string().max(MAX_PATH_LENGTH).trim(),
  type: z.string().max(50).trim(), // File type
}).strict();

export type UploadResult = z.infer<typeof UploadResultSchema>;

export const SystemStatsDeviceSchema = z.object({
  name: z.string().max(MAX_NAME_LENGTH).trim(),
  type: z.string().max(50).trim(), // Device type
  index: nonNegativeInt.max(100), // Max 100 devices
  vram_total: nonNegativeInt.max(2147483647), // Max 32-bit int (2GB in MB)
  vram_free: nonNegativeInt.max(2147483647), // Max 32-bit int
  torch_vram_total: nonNegativeInt.max(2147483647), // Max 32-bit int
  torch_vram_free: nonNegativeInt.max(2147483647), // Max 32-bit int
}).strict().refine(
  (data) => {
    // Free should be <= total
    return data.vram_free <= data.vram_total && data.torch_vram_free <= data.torch_vram_total;
  },
  { message: "Free VRAM must be <= total VRAM", path: ["vram_free"] }
);

export type SystemStatsDevice = z.infer<typeof SystemStatsDeviceSchema>;

export const SystemStatsSchema = z.object({
  system: z.object({
    os: z.string().max(100).trim(),
    python_version: z.string().max(50).trim(), // Version string
    embedded_python: z.boolean(),
  }).strict(),
  devices: boundedArray(SystemStatsDeviceSchema, 100), // Max 100 devices
}).strict();

export type SystemStats = z.infer<typeof SystemStatsSchema>;

export const QueueStatusSchema = z.object({
  exec_info: z.object({
    queue_remaining: nonNegativeInt.max(1000000), // Max 1M queue items
  }).strict(),
}).strict();

export type QueueStatus = z.infer<typeof QueueStatusSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════

export function validateExportConfig(data: unknown): ExportConfig {
  return ExportConfigSchema.parse(data);
}

export function safeValidateExportConfig(data: unknown) {
  return ExportConfigSchema.safeParse(data);
}

export function validateWorkflow(data: unknown): ComfyUIWorkflow {
  return ComfyUIWorkflowSchema.parse(data);
}

export function safeValidateWorkflow(data: unknown) {
  return ComfyUIWorkflowSchema.safeParse(data);
}

export function validateMotionCtrlCamera(data: unknown): MotionCtrlCameraData {
  return MotionCtrlCameraDataSchema.parse(data);
}

export function safeValidateMotionCtrlCamera(data: unknown) {
  return MotionCtrlCameraDataSchema.safeParse(data);
}
