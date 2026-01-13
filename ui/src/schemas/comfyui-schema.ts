/**
 * ComfyUI Schema
 *
 * Zod schemas for validating ComfyUI integration types.
 * All numeric values use .finite() to reject NaN/Infinity.
 */

import { z } from "zod";

// ============================================================================
// Primitives
// ============================================================================

const finiteNumber = z.number().finite();
const positiveFinite = z.number().finite().positive();
const nonNegativeFinite = z.number().finite().nonnegative();
const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();
const normalized0100 = z.number().finite().min(0).max(100);

// ============================================================================
// Export Target
// ============================================================================

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

// ============================================================================
// Depth Map Format
// ============================================================================

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

// ============================================================================
// Control Type
// ============================================================================

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

// ============================================================================
// Depth Export Options
// ============================================================================

export const DepthExportOptionsSchema = z.object({
  format: DepthMapFormatSchema,
  bitDepth: z.union([z.literal(8), z.literal(16), z.literal(32)]),
  invert: z.boolean(),
  normalize: z.boolean(),
  colormap: z.enum(["grayscale", "viridis", "magma", "plasma", "inferno", "turbo"]),
  nearClip: finiteNumber,
  farClip: finiteNumber,
});

export type DepthExportOptions = z.infer<typeof DepthExportOptionsSchema>;

// ============================================================================
// Control Export Config
// ============================================================================

export const ControlExportConfigSchema = z.object({
  type: ControlTypeSchema,
  resolution: positiveInt,
  threshold_low: finiteNumber.optional(),
  threshold_high: finiteNumber.optional(),
  detect_resolution: positiveInt.optional(),
});

export type ControlExportConfig = z.infer<typeof ControlExportConfigSchema>;

// ============================================================================
// Export Config
// ============================================================================

export const ExportConfigSchema = z.object({
  target: ExportTargetSchema,
  width: positiveInt,
  height: positiveInt,
  frameCount: positiveInt,
  fps: positiveFinite,
  startFrame: nonNegativeInt,
  endFrame: nonNegativeInt,
  outputDir: z.string(),
  filenamePrefix: z.string(),
  exportDepthMap: z.boolean(),
  exportControlImages: z.boolean(),
  exportCameraData: z.boolean(),
  exportReferenceFrame: z.boolean(),
  exportLastFrame: z.boolean(),
  depthFormat: DepthMapFormatSchema,
  controlType: ControlTypeSchema.optional(),
  prompt: z.string(),
  negativePrompt: z.string(),
  seed: z.number().int().optional(),
  steps: positiveInt.optional(),
  cfgScale: positiveFinite.optional(),
  comfyuiServer: z.string().optional(),
  autoQueueWorkflow: z.boolean(),
  workflowTemplate: z.string().optional(),
});

export type ExportConfig = z.infer<typeof ExportConfigSchema>;

// ============================================================================
// Export Result
// ============================================================================

export const ExportResultSchema = z.object({
  success: z.boolean(),
  outputFiles: z.object({
    referenceImage: z.string().optional(),
    lastImage: z.string().optional(),
    depthSequence: z.array(z.string()).optional(),
    controlSequence: z.array(z.string()).optional(),
    cameraData: z.string().optional(),
    workflowJson: z.string().optional(),
    promptId: z.string().optional(),
  }),
  errors: z.array(z.string()),
  warnings: z.array(z.string()),
  duration: nonNegativeFinite,
});

export type ExportResult = z.infer<typeof ExportResultSchema>;

// ============================================================================
// Camera Formats
// ============================================================================

// MotionCtrl
export const MotionCtrlPoseSchema = z.object({
  RT: z.array(z.array(finiteNumber).length(4)).length(4),
});

export type MotionCtrlPose = z.infer<typeof MotionCtrlPoseSchema>;

export const MotionCtrlCameraDataSchema = z.object({
  camera_poses: z.array(MotionCtrlPoseSchema),
});

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
  camera_poses: z.string().optional(),
});

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
});

export type Wan22FunCameraData = z.infer<typeof Wan22FunCameraDataSchema>;

// Uni3C
export const Uni3CCameraTrajectorySchema = z.object({
  zoom: finiteNumber,
  x_offset: finiteNumber,
  y_offset: finiteNumber,
  z_offset: finiteNumber,
  pitch: finiteNumber,
  yaw: finiteNumber,
  roll: finiteNumber,
});

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
  frame: nonNegativeInt,
  params: Uni3CCameraTrajectorySchema,
  interpolation: z.enum(["linear", "bezier"]),
});

export type Uni3CKeyframe = z.infer<typeof Uni3CKeyframeSchema>;

export const Uni3CCameraDataSchema = z.object({
  traj_type: Uni3CTrajTypeSchema,
  custom_trajectory: z.array(Uni3CCameraTrajectorySchema).optional(),
  keyframes: z.array(Uni3CKeyframeSchema).optional(),
});

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
  speed: finiteNumber,
  frame_length: positiveInt,
  prev_poses: z.array(z.array(finiteNumber)).optional(),
});

export type CameraCtrlPoses = z.infer<typeof CameraCtrlPosesSchema>;

// Full Camera Export
export const FullCameraFrameSchema = z.object({
  frame: nonNegativeInt,
  timestamp: nonNegativeFinite,
  view_matrix: z.array(z.array(finiteNumber)),
  projection_matrix: z.array(z.array(finiteNumber)),
  position: z.tuple([finiteNumber, finiteNumber, finiteNumber]),
  rotation: z.tuple([finiteNumber, finiteNumber, finiteNumber]),
  fov: positiveFinite,
  focal_length: positiveFinite,
  focus_distance: nonNegativeFinite,
});

export type FullCameraFrame = z.infer<typeof FullCameraFrameSchema>;

export const FullCameraExportSchema = z.object({
  frames: z.array(FullCameraFrameSchema),
  metadata: z.object({
    width: positiveInt,
    height: positiveInt,
    fps: positiveFinite,
    total_frames: positiveInt,
    camera_type: z.string(),
    film_size: positiveFinite,
  }),
});

export type FullCameraExport = z.infer<typeof FullCameraExportSchema>;

// ============================================================================
// ComfyUI Types
// ============================================================================

export const NodeConnectionSchema = z.tuple([z.string(), z.number().int()]);

export type NodeConnection = z.infer<typeof NodeConnectionSchema>;

export const ComfyUINodeSchema = z.object({
  class_type: z.string(),
  inputs: z.record(z.unknown()),
  _meta: z.object({
    title: z.string(),
  }).optional(),
});

export type ComfyUINode = z.infer<typeof ComfyUINodeSchema>;

export const ComfyUIWorkflowSchema = z.record(ComfyUINodeSchema);

export type ComfyUIWorkflow = z.infer<typeof ComfyUIWorkflowSchema>;

export const ComfyUIPromptResultSchema = z.object({
  prompt_id: z.string(),
  number: nonNegativeInt,
  node_errors: z.record(z.string()).optional(),
});

export type ComfyUIPromptResult = z.infer<typeof ComfyUIPromptResultSchema>;

export const ComfyUIImageOutputSchema = z.object({
  filename: z.string(),
  subfolder: z.string(),
  type: z.string(),
});

export type ComfyUIImageOutput = z.infer<typeof ComfyUIImageOutputSchema>;

export const ComfyUIHistoryEntrySchema = z.object({
  prompt: ComfyUIWorkflowSchema,
  outputs: z.record(z.object({
    images: z.array(ComfyUIImageOutputSchema).optional(),
    gifs: z.array(ComfyUIImageOutputSchema).optional(),
  })),
  status: z.object({
    status_str: z.string(),
    completed: z.boolean(),
    messages: z.array(z.string()),
  }),
});

export type ComfyUIHistoryEntry = z.infer<typeof ComfyUIHistoryEntrySchema>;

// ============================================================================
// Video Output Types
// ============================================================================

export const VideoFormatSchema = z.enum(["mp4", "webm", "gif", "webp", "image_sequence"]);

export type VideoFormat = z.infer<typeof VideoFormatSchema>;

export const VideoCodecSchema = z.enum(["h264", "h265", "vp9", "av1"]);

export type VideoCodec = z.infer<typeof VideoCodecSchema>;

export const FrameSequenceFormatSchema = z.enum(["png", "jpeg", "webp", "tiff", "exr", "dpx"]);

export type FrameSequenceFormat = z.infer<typeof FrameSequenceFormatSchema>;

export const FrameSequenceOptionsSchema = z.object({
  format: FrameSequenceFormatSchema,
  quality: normalized0100,
  filenamePattern: z.string(),
  outputDir: z.string(),
  bitDepth: z.union([z.literal(8), z.literal(10), z.literal(16), z.literal(32)]).optional(),
  colorSpace: z.enum(["sRGB", "Linear", "ACEScg", "Rec709"]).optional(),
});

export type FrameSequenceOptions = z.infer<typeof FrameSequenceOptionsSchema>;

export const VideoEncoderOptionsSchema = z.object({
  format: VideoFormatSchema,
  codec: VideoCodecSchema.optional(),
  fps: positiveFinite,
  quality: normalized0100,
  width: positiveInt,
  height: positiveInt,
  loop: z.boolean().optional(),
});

export type VideoEncoderOptions = z.infer<typeof VideoEncoderOptionsSchema>;

// ============================================================================
// Progress Tracking
// ============================================================================

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
  currentFrame: nonNegativeInt.optional(),
  totalFrames: positiveInt.optional(),
  message: z.string(),
  preview: z.string().optional(),
});

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
  currentNode: z.string().optional(),
  currentStep: nonNegativeInt.optional(),
  totalSteps: positiveInt.optional(),
  progress: normalized0100.optional(),
  preview: z.string().optional(),
  errorMessage: z.string().optional(),
});

export type GenerationProgress = z.infer<typeof GenerationProgressSchema>;

// ============================================================================
// Client Types
// ============================================================================

export const ComfyUIClientConfigSchema = z.object({
  serverAddress: z.string(),
  clientId: z.string().optional(),
});

export type ComfyUIClientConfig = z.infer<typeof ComfyUIClientConfigSchema>;

export const UploadResultSchema = z.object({
  name: z.string(),
  subfolder: z.string(),
  type: z.string(),
});

export type UploadResult = z.infer<typeof UploadResultSchema>;

export const SystemStatsDeviceSchema = z.object({
  name: z.string(),
  type: z.string(),
  index: nonNegativeInt,
  vram_total: nonNegativeInt,
  vram_free: nonNegativeInt,
  torch_vram_total: nonNegativeInt,
  torch_vram_free: nonNegativeInt,
});

export type SystemStatsDevice = z.infer<typeof SystemStatsDeviceSchema>;

export const SystemStatsSchema = z.object({
  system: z.object({
    os: z.string(),
    python_version: z.string(),
    embedded_python: z.boolean(),
  }),
  devices: z.array(SystemStatsDeviceSchema),
});

export type SystemStats = z.infer<typeof SystemStatsSchema>;

export const QueueStatusSchema = z.object({
  exec_info: z.object({
    queue_remaining: nonNegativeInt,
  }),
});

export type QueueStatus = z.infer<typeof QueueStatusSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

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
