/**
 * Export Types for ComfyUI Integration
 * Defines output formats for Wan 2.2, Uni3C, MotionCtrl, CogVideoX, and ControlNet
 */

// ============================================================================
// Export Target Types
// ============================================================================

export type ExportTarget =
  | 'wan22-i2v'           // Wan 2.2 Image-to-Video
  | 'wan22-t2v'           // Wan 2.2 Text-to-Video
  | 'wan22-fun-camera'    // Wan 2.2 Fun Camera Control
  | 'wan22-first-last'    // Wan 2.2 First+Last Frame
  | 'uni3c-camera'        // Uni3C Camera Control
  | 'uni3c-motion'        // Uni3C Human Motion + Camera
  | 'motionctrl'          // MotionCtrl camera poses
  | 'motionctrl-svd'      // MotionCtrl for SVD
  | 'cogvideox'           // CogVideoX I2V
  | 'controlnet-depth'    // Depth map for ControlNet
  | 'controlnet-canny'    // Canny edge for ControlNet
  | 'controlnet-lineart'  // Line art for ControlNet
  | 'animatediff-cameractrl' // AnimateDiff CameraCtrl
  | 'custom-workflow'     // User's custom workflow
  // New model targets (Dec 2025)
  | 'light-x'             // Light-X relighting + camera
  | 'wan-move'            // Wan-Move point trajectories
  | 'ati'                 // ATI Any Trajectory Instruction
  | 'ttm'                 // TTM Time-to-Move cut-and-drag
  | 'ttm-wan'             // TTM with Wan 2.1 backend
  | 'ttm-cogvideox'       // TTM with CogVideoX backend
  | 'ttm-svd'             // TTM with SVD backend
  | 'camera-comfyui';     // camera-comfyUI 4x4 matrices

// ============================================================================
// Export Configuration
// ============================================================================

export interface ExportConfig {
  target: ExportTarget;

  // Resolution
  width: number;
  height: number;

  // Frame settings
  frameCount: number;
  fps: number;

  // Time range
  startFrame: number;
  endFrame: number;

  // Output paths
  outputDir: string;
  filenamePrefix: string;

  // What to export
  exportDepthMap: boolean;
  exportControlImages: boolean;
  exportCameraData: boolean;
  exportReferenceFrame: boolean;
  exportLastFrame: boolean;

  // Depth map settings
  depthFormat: DepthMapFormat;

  // Control image settings
  controlType?: ControlType;

  // Generation settings (for workflow)
  prompt: string;
  negativePrompt: string;
  seed?: number;
  steps?: number;
  cfgScale?: number;

  // ComfyUI integration
  comfyuiServer?: string;
  autoQueueWorkflow: boolean;
  workflowTemplate?: string;
}

// ============================================================================
// Export Result
// ============================================================================

export interface ExportResult {
  success: boolean;
  outputFiles: {
    referenceImage?: string;
    lastImage?: string;
    depthSequence?: string[];
    controlSequence?: string[];
    cameraData?: string;
    workflowJson?: string;
    promptId?: string;
  };
  errors: string[];
  warnings: string[];
  duration: number; // milliseconds
}

// ============================================================================
// Depth Map Types
// ============================================================================

export type DepthMapFormat =
  | 'midas'        // MiDaS format: 0=far, 255=near (inverted)
  | 'zoe'          // Zoe format: linear, 0=near, 65535=far (16-bit)
  | 'depth-pro'    // Depth-Pro format: metric depth in meters
  | 'normalized';  // Normalized 0-1 range (model-agnostic)

export interface DepthExportOptions {
  format: DepthMapFormat;
  bitDepth: 8 | 16;
  invert: boolean;
  normalize: boolean;
  colormap: 'grayscale' | 'viridis' | 'magma' | 'plasma';
  nearClip: number;
  farClip: number;
}

// ============================================================================
// Control Image Types
// ============================================================================

export type ControlType =
  | 'depth'
  | 'canny'
  | 'lineart'
  | 'softedge'
  | 'normal'
  | 'scribble'
  | 'seg'
  | 'pose';

export interface ControlExportConfig {
  type: ControlType;
  resolution: number;
  threshold_low?: number;
  threshold_high?: number;
  detect_resolution?: number;
}

// ============================================================================
// Camera Export Formats
// ============================================================================

// MotionCtrl Format
export interface MotionCtrlPose {
  RT: number[][]; // 4x4 camera extrinsic matrix
}

export interface MotionCtrlCameraData {
  camera_poses: MotionCtrlPose[];
}

// MotionCtrl-SVD Presets
export type MotionCtrlSVDPreset =
  | 'zoom_in'
  | 'zoom_out'
  | 'pan_left'
  | 'pan_right'
  | 'pan_up'
  | 'pan_down'
  | 'rotate_cw'
  | 'rotate_ccw'
  | 'static';

export interface MotionCtrlSVDCameraData {
  motion_camera: MotionCtrlSVDPreset;
  camera_poses?: string;
}

// Wan 2.2 Fun Camera
export type Wan22CameraMotion =
  | 'Static'
  | 'Pan Up'
  | 'Pan Down'
  | 'Pan Left'
  | 'Pan Right'
  | 'Zoom In'
  | 'Zoom Out'
  | 'Pan Up + Zoom In'
  | 'Pan Up + Zoom Out'
  | 'Pan Down + Zoom In'
  | 'Pan Down + Zoom Out'
  | 'Pan Left + Zoom In'
  | 'Pan Left + Zoom Out'
  | 'Pan Right + Zoom In'
  | 'Pan Right + Zoom Out'
  | 'Orbital Left'
  | 'Orbital Right';

export interface Wan22FunCameraData {
  camera_motion: Wan22CameraMotion;
}

// Uni3C Camera Trajectory
export interface Uni3CCameraTrajectory {
  zoom: number;
  x_offset: number;
  y_offset: number;
  z_offset: number;
  pitch: number;
  yaw: number;
  roll: number;
}

export type Uni3CTrajType =
  | 'custom'
  | 'free1' | 'free2' | 'free3' | 'free4' | 'free5'
  | 'swing1' | 'swing2'
  | 'orbit';

export interface Uni3CCameraData {
  traj_type: Uni3CTrajType;
  custom_trajectory?: Uni3CCameraTrajectory[];
  keyframes?: Array<{
    frame: number;
    params: Uni3CCameraTrajectory;
    interpolation: 'linear' | 'bezier';
  }>;
}

// AnimateDiff CameraCtrl
export type CameraCtrlMotionType =
  | 'Static'
  | 'Move Forward'
  | 'Move Backward'
  | 'Move Left'
  | 'Move Right'
  | 'Move Up'
  | 'Move Down'
  | 'Rotate Left'
  | 'Rotate Right'
  | 'Rotate Up'
  | 'Rotate Down'
  | 'Roll Left'
  | 'Roll Right';

export interface CameraCtrlPoses {
  motion_type: CameraCtrlMotionType;
  speed: number;
  frame_length: number;
  prev_poses?: number[][];
}

// Full Camera Export (generic format)
export interface FullCameraFrame {
  frame: number;
  timestamp: number;
  view_matrix: number[][];
  projection_matrix: number[][];
  position: [number, number, number];
  rotation: [number, number, number];
  fov: number;
  focal_length: number;
  focus_distance: number;
}

export interface FullCameraExport {
  frames: FullCameraFrame[];
  metadata: {
    width: number;
    height: number;
    fps: number;
    total_frames: number;
    camera_type: string;
    film_size: number;
  };
}

// ============================================================================
// ComfyUI Types
// ============================================================================

export type NodeConnection = [string, number];

export interface ComfyUINode {
  class_type: string;
  inputs: Record<string, any>;
  _meta?: {
    title: string;
  };
}

export interface ComfyUIWorkflow {
  [nodeId: string]: ComfyUINode;
}

export interface ComfyUIPromptResult {
  prompt_id: string;
  number: number;
  node_errors?: Record<string, string>;
}

export interface ComfyUIHistoryEntry {
  prompt: ComfyUIWorkflow;
  outputs: Record<string, {
    images?: Array<{
      filename: string;
      subfolder: string;
      type: string;
    }>;
    gifs?: Array<{
      filename: string;
      subfolder: string;
      type: string;
    }>;
  }>;
  status: {
    status_str: string;
    completed: boolean;
    messages: string[];
  };
}

// ============================================================================
// Video Output Types
// ============================================================================

export type VideoFormat = 'mp4' | 'webm' | 'gif' | 'webp' | 'image_sequence';
export type VideoCodec = 'h264' | 'h265' | 'vp9' | 'av1';

// Frame sequence formats
export type FrameSequenceFormat =
  | 'png'       // Lossless, 8-bit RGBA (browser)
  | 'jpeg'      // Lossy, 8-bit RGB (browser)
  | 'webp'      // Modern format (browser)
  | 'tiff'      // 8/16-bit (backend)
  | 'exr'       // HDR 16/32-bit float (backend)
  | 'dpx';      // Film 10/16-bit (backend)

export interface FrameSequenceOptions {
  format: FrameSequenceFormat;
  quality: number;           // 0-100 for lossy
  filenamePattern: string;   // e.g., "frame_{frame:04d}"
  outputDir: string;
  bitDepth?: 8 | 10 | 16 | 32;
  colorSpace?: 'sRGB' | 'Linear' | 'ACEScg' | 'Rec709';
}

export interface VideoEncoderOptions {
  format: VideoFormat;
  codec?: VideoCodec;
  fps: number;
  quality: number;
  width: number;
  height: number;
  loop?: boolean;
}

// ============================================================================
// Progress Tracking
// ============================================================================

export type ExportStage =
  | 'preparing'
  | 'rendering_frames'
  | 'rendering_depth'
  | 'rendering_control'
  | 'exporting_camera'
  | 'generating_workflow'
  | 'uploading'
  | 'queuing'
  | 'generating'
  | 'downloading'
  | 'complete'
  | 'error';

export interface ExportProgress {
  stage: ExportStage;
  stageProgress: number; // 0-100
  overallProgress: number; // 0-100
  currentFrame?: number;
  totalFrames?: number;
  message: string;
  preview?: string; // Base64 preview image
}

export interface GenerationProgress {
  status: 'queued' | 'executing' | 'completed' | 'error';
  currentNode?: string;
  currentStep?: number;
  totalSteps?: number;
  percentage: number;
  preview?: string;
  eta?: number; // seconds remaining
}
