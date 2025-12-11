/**
 * Export Presets for Different AI Video Generation Models
 */

import type {
  ExportTarget,
  ExportConfig,
  DepthMapFormat,
  DepthExportOptions,
  ControlType,
  VideoFormat
} from '@/types/export';

// ============================================================================
// Export Target Presets
// ============================================================================

export const EXPORT_PRESETS: Record<ExportTarget, Partial<ExportConfig>> = {
  'wan22-i2v': {
    width: 832,
    height: 480,
    frameCount: 81,
    fps: 24,
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: false,
    exportReferenceFrame: true,
    exportLastFrame: false,
    steps: 30,
    cfgScale: 5.0,
  },

  'wan22-t2v': {
    width: 832,
    height: 480,
    frameCount: 81,
    fps: 24,
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: false,
    exportReferenceFrame: false,
    exportLastFrame: false,
    steps: 30,
    cfgScale: 5.0,
  },

  'wan22-fun-camera': {
    width: 832,
    height: 480,
    frameCount: 81,
    fps: 24,
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: true,
    exportReferenceFrame: true,
    exportLastFrame: false,
    steps: 30,
    cfgScale: 5.0,
  },

  'wan22-first-last': {
    width: 832,
    height: 480,
    frameCount: 81,
    fps: 24,
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: false,
    exportReferenceFrame: true,
    exportLastFrame: true,
    steps: 30,
    cfgScale: 5.0,
  },

  'uni3c-camera': {
    width: 832,
    height: 480,
    frameCount: 81,
    fps: 24,
    exportDepthMap: true,
    exportControlImages: false,
    exportCameraData: true,
    exportReferenceFrame: true,
    exportLastFrame: false,
    depthFormat: 'normalized',
    steps: 30,
    cfgScale: 5.0,
  },

  'uni3c-motion': {
    width: 832,
    height: 480,
    frameCount: 81,
    fps: 24,
    exportDepthMap: true,
    exportControlImages: false,
    exportCameraData: true,
    exportReferenceFrame: true,
    exportLastFrame: false,
    depthFormat: 'normalized',
    steps: 30,
    cfgScale: 5.0,
  },

  'motionctrl': {
    width: 576,
    height: 320,
    frameCount: 16,
    fps: 24,
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: true,
    exportReferenceFrame: true,
    exportLastFrame: false,
    steps: 25,
    cfgScale: 7.5,
  },

  'motionctrl-svd': {
    width: 1024,
    height: 576,
    frameCount: 25,
    fps: 24,
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: true,
    exportReferenceFrame: true,
    exportLastFrame: false,
    steps: 25,
    cfgScale: 3.0,
  },

  'cogvideox': {
    width: 720,
    height: 480,
    frameCount: 49,
    fps: 16,
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: false,
    exportReferenceFrame: true,
    exportLastFrame: false,
    steps: 50,
    cfgScale: 6.0,
  },

  'controlnet-depth': {
    width: 1024,
    height: 1024,
    frameCount: 1,
    fps: 24,
    exportDepthMap: true,
    exportControlImages: true,
    exportCameraData: false,
    exportReferenceFrame: true,
    exportLastFrame: false,
    depthFormat: 'midas',
    controlType: 'depth',
    steps: 20,
    cfgScale: 7.5,
  },

  'controlnet-canny': {
    width: 1024,
    height: 1024,
    frameCount: 1,
    fps: 24,
    exportDepthMap: false,
    exportControlImages: true,
    exportCameraData: false,
    exportReferenceFrame: true,
    exportLastFrame: false,
    controlType: 'canny',
    steps: 20,
    cfgScale: 7.5,
  },

  'controlnet-lineart': {
    width: 1024,
    height: 1024,
    frameCount: 1,
    fps: 24,
    exportDepthMap: false,
    exportControlImages: true,
    exportCameraData: false,
    exportReferenceFrame: true,
    exportLastFrame: false,
    controlType: 'lineart',
    steps: 20,
    cfgScale: 7.5,
  },

  'animatediff-cameractrl': {
    width: 512,
    height: 512,
    frameCount: 16,
    fps: 8,
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: true,
    exportReferenceFrame: true,
    exportLastFrame: false,
    steps: 25,
    cfgScale: 7.5,
  },

  'custom-workflow': {
    width: 1024,
    height: 1024,
    frameCount: 81,
    fps: 24,
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: false,
    exportReferenceFrame: true,
    exportLastFrame: false,
    steps: 30,
    cfgScale: 7.0,
  },
};

// ============================================================================
// Depth Format Specifications
// ============================================================================

export const DEPTH_FORMAT_SPECS: Record<DepthMapFormat, DepthExportOptions> = {
  'midas': {
    format: 'midas',
    bitDepth: 8,
    invert: true,
    normalize: true,
    colormap: 'grayscale',
    nearClip: 0.1,
    farClip: 1000,
  },
  'zoe': {
    format: 'zoe',
    bitDepth: 16,
    invert: false,
    normalize: true,
    colormap: 'grayscale',
    nearClip: 0.1,
    farClip: 1000,
  },
  'depth-pro': {
    format: 'depth-pro',
    bitDepth: 16,
    invert: false,
    normalize: false,
    colormap: 'grayscale',
    nearClip: 0.01,
    farClip: 100,
  },
  'normalized': {
    format: 'normalized',
    bitDepth: 8,
    invert: false,
    normalize: true,
    colormap: 'grayscale',
    nearClip: 0.1,
    farClip: 1000,
  },
};

// ============================================================================
// ControlNet Recommendations
// ============================================================================

export const CONTROL_RECOMMENDATIONS: Record<ControlType, {
  preprocessor: string;
  model_sd15: string;
  model_sdxl: string;
  description: string;
}> = {
  'depth': {
    preprocessor: 'Zoe-DepthMapPreprocessor',
    model_sd15: 'control_v11f1p_sd15_depth',
    model_sdxl: 'controlnet-depth-sdxl-1.0',
    description: 'Depth-based structure control',
  },
  'canny': {
    preprocessor: 'CannyEdgePreprocessor',
    model_sd15: 'control_v11p_sd15_canny',
    model_sdxl: 'controlnet-canny-sdxl-1.0',
    description: 'Sharp edge detection',
  },
  'lineart': {
    preprocessor: 'LineArtPreprocessor',
    model_sd15: 'control_v11p_sd15_lineart',
    model_sdxl: 'controlnet-lineart-sdxl-1.0',
    description: 'Clean line art extraction',
  },
  'softedge': {
    preprocessor: 'HEDPreprocessor',
    model_sd15: 'control_v11p_sd15_softedge',
    model_sdxl: 'controlnet-softedge-sdxl-1.0',
    description: 'Soft edge detection (HED/PIDI)',
  },
  'normal': {
    preprocessor: 'BAE-NormalMapPreprocessor',
    model_sd15: 'control_v11p_sd15_normalbae',
    model_sdxl: 'controlnet-normal-sdxl-1.0',
    description: 'Surface normal map',
  },
  'scribble': {
    preprocessor: 'ScribblePreprocessor',
    model_sd15: 'control_v11p_sd15_scribble',
    model_sdxl: 'controlnet-scribble-sdxl-1.0',
    description: 'Scribble/sketch input',
  },
  'seg': {
    preprocessor: 'OneFormer-COCO-SemSegPreprocessor',
    model_sd15: 'control_v11p_sd15_seg',
    model_sdxl: 'controlnet-seg-sdxl-1.0',
    description: 'Semantic segmentation',
  },
  'pose': {
    preprocessor: 'OpenposePreprocessor',
    model_sd15: 'control_v11p_sd15_openpose',
    model_sdxl: 'controlnet-openpose-sdxl-1.0',
    description: 'Human pose skeleton',
  },
};

// ============================================================================
// Video Format Specifications
// ============================================================================

export const VIDEO_FORMAT_SPECS: Record<VideoFormat, {
  extension: string;
  mimeType: string;
  comfyNode: string;
  description: string;
}> = {
  'mp4': {
    extension: '.mp4',
    mimeType: 'video/mp4',
    comfyNode: 'VHS_VideoCombine',
    description: 'H.264/H.265 MP4 video',
  },
  'webm': {
    extension: '.webm',
    mimeType: 'video/webm',
    comfyNode: 'VHS_VideoCombine',
    description: 'VP9/AV1 WebM video',
  },
  'gif': {
    extension: '.gif',
    mimeType: 'image/gif',
    comfyNode: 'VHS_VideoCombine',
    description: 'Animated GIF',
  },
  'webp': {
    extension: '.webp',
    mimeType: 'image/webp',
    comfyNode: 'SaveAnimatedWEBP',
    description: 'Animated WebP',
  },
  'image_sequence': {
    extension: '.png',
    mimeType: 'image/png',
    comfyNode: 'SaveImage',
    description: 'PNG image sequence',
  },
};

// ============================================================================
// Resolution Presets
// ============================================================================

export const RESOLUTION_PRESETS: Array<{
  name: string;
  width: number;
  height: number;
  aspectRatio: string;
  recommended: ExportTarget[];
}> = [
  {
    name: '832x480 (Wan 2.2)',
    width: 832,
    height: 480,
    aspectRatio: '16:9',
    recommended: ['wan22-i2v', 'wan22-t2v', 'wan22-fun-camera', 'wan22-first-last', 'uni3c-camera'],
  },
  {
    name: '1280x720 (HD)',
    width: 1280,
    height: 720,
    aspectRatio: '16:9',
    recommended: ['wan22-i2v', 'wan22-t2v'],
  },
  {
    name: '1024x576 (SVD)',
    width: 1024,
    height: 576,
    aspectRatio: '16:9',
    recommended: ['motionctrl-svd'],
  },
  {
    name: '576x320 (MotionCtrl)',
    width: 576,
    height: 320,
    aspectRatio: '16:9',
    recommended: ['motionctrl'],
  },
  {
    name: '720x480 (CogVideoX)',
    width: 720,
    height: 480,
    aspectRatio: '3:2',
    recommended: ['cogvideox'],
  },
  {
    name: '512x512 (Square)',
    width: 512,
    height: 512,
    aspectRatio: '1:1',
    recommended: ['controlnet-depth', 'controlnet-canny', 'animatediff-cameractrl'],
  },
  {
    name: '1024x1024 (Square HD)',
    width: 1024,
    height: 1024,
    aspectRatio: '1:1',
    recommended: ['controlnet-depth', 'controlnet-canny'],
  },
];

// ============================================================================
// Frame Count Presets
// ============================================================================

export const FRAME_COUNT_PRESETS: Array<{
  name: string;
  frameCount: number;
  duration: string;
  fps: number;
  recommended: ExportTarget[];
}> = [
  {
    name: '16 frames (~0.7s)',
    frameCount: 16,
    duration: '0.67s',
    fps: 24,
    recommended: ['motionctrl', 'animatediff-cameractrl'],
  },
  {
    name: '25 frames (~1s)',
    frameCount: 25,
    duration: '1.04s',
    fps: 24,
    recommended: ['motionctrl-svd'],
  },
  {
    name: '49 frames (~3s)',
    frameCount: 49,
    duration: '3.06s',
    fps: 16,
    recommended: ['cogvideox'],
  },
  {
    name: '81 frames (~3.4s)',
    frameCount: 81,
    duration: '3.38s',
    fps: 24,
    recommended: ['wan22-i2v', 'wan22-t2v', 'wan22-fun-camera', 'uni3c-camera'],
  },
  {
    name: '121 frames (~5s)',
    frameCount: 121,
    duration: '5.04s',
    fps: 24,
    recommended: ['wan22-i2v'],
  },
];

// ============================================================================
// Export Target Metadata
// ============================================================================

export const EXPORT_TARGET_INFO: Record<ExportTarget, {
  name: string;
  description: string;
  requiredInputs: string[];
  optionalInputs: string[];
  outputTypes: string[];
  comfyNodes: string[];
}> = {
  'wan22-i2v': {
    name: 'Wan 2.2 Image-to-Video',
    description: 'Generate video from a reference image with text prompt',
    requiredInputs: ['reference_image', 'prompt'],
    optionalInputs: ['negative_prompt', 'seed'],
    outputTypes: ['video'],
    comfyNodes: ['WanImageToVideo', 'WanModel', 'WanVAE'],
  },
  'wan22-t2v': {
    name: 'Wan 2.2 Text-to-Video',
    description: 'Generate video from text prompt only',
    requiredInputs: ['prompt'],
    optionalInputs: ['negative_prompt', 'seed'],
    outputTypes: ['video'],
    comfyNodes: ['WanTextToVideo', 'WanModel', 'WanVAE'],
  },
  'wan22-fun-camera': {
    name: 'Wan 2.2 Fun Camera',
    description: 'Generate video with camera motion presets',
    requiredInputs: ['reference_image', 'prompt', 'camera_motion'],
    optionalInputs: ['negative_prompt', 'seed'],
    outputTypes: ['video'],
    comfyNodes: ['WanFunCameraToVideo', 'WanModel', 'WanVAE'],
  },
  'wan22-first-last': {
    name: 'Wan 2.2 First+Last Frame',
    description: 'Generate video interpolating between first and last frames',
    requiredInputs: ['first_frame', 'last_frame', 'prompt'],
    optionalInputs: ['negative_prompt', 'seed'],
    outputTypes: ['video'],
    comfyNodes: ['WanFirstLastFrameToVideo', 'WanModel', 'WanVAE'],
  },
  'uni3c-camera': {
    name: 'Uni3C Camera Control',
    description: 'Generate video with precise 3D camera trajectory control',
    requiredInputs: ['reference_image', 'prompt', 'camera_trajectory'],
    optionalInputs: ['depth_map', 'negative_prompt'],
    outputTypes: ['video'],
    comfyNodes: ['Uni3CLoader', 'Uni3CCameraControl'],
  },
  'uni3c-motion': {
    name: 'Uni3C Human Motion + Camera',
    description: 'Generate video with human motion and camera control',
    requiredInputs: ['reference_image', 'prompt', 'camera_trajectory', 'motion_data'],
    optionalInputs: ['depth_map'],
    outputTypes: ['video'],
    comfyNodes: ['Uni3CLoader', 'Uni3CMotionControl'],
  },
  'motionctrl': {
    name: 'MotionCtrl',
    description: 'Camera-controlled video generation using pose matrices',
    requiredInputs: ['reference_image', 'camera_poses'],
    optionalInputs: ['prompt'],
    outputTypes: ['video'],
    comfyNodes: ['MotionCtrlLoader', 'MotionCtrlSample'],
  },
  'motionctrl-svd': {
    name: 'MotionCtrl SVD',
    description: 'MotionCtrl for Stable Video Diffusion',
    requiredInputs: ['reference_image', 'camera_poses'],
    optionalInputs: ['motion_preset'],
    outputTypes: ['video'],
    comfyNodes: ['MotionCtrlSVDLoader', 'MotionCtrlSVDSample'],
  },
  'cogvideox': {
    name: 'CogVideoX',
    description: 'High-quality video generation from CogVideo team',
    requiredInputs: ['reference_image', 'prompt'],
    optionalInputs: ['negative_prompt', 'seed'],
    outputTypes: ['video'],
    comfyNodes: ['CogVideoXLoader', 'CogVideoXSampler'],
  },
  'controlnet-depth': {
    name: 'ControlNet Depth',
    description: 'Depth-guided image generation',
    requiredInputs: ['depth_map', 'prompt'],
    optionalInputs: ['reference_image', 'negative_prompt'],
    outputTypes: ['image'],
    comfyNodes: ['ControlNetLoader', 'ControlNetApply'],
  },
  'controlnet-canny': {
    name: 'ControlNet Canny',
    description: 'Edge-guided image generation',
    requiredInputs: ['canny_image', 'prompt'],
    optionalInputs: ['reference_image', 'negative_prompt'],
    outputTypes: ['image'],
    comfyNodes: ['ControlNetLoader', 'ControlNetApply', 'CannyEdgePreprocessor'],
  },
  'controlnet-lineart': {
    name: 'ControlNet LineArt',
    description: 'Line art guided image generation',
    requiredInputs: ['lineart_image', 'prompt'],
    optionalInputs: ['reference_image', 'negative_prompt'],
    outputTypes: ['image'],
    comfyNodes: ['ControlNetLoader', 'ControlNetApply', 'LineArtPreprocessor'],
  },
  'animatediff-cameractrl': {
    name: 'AnimateDiff CameraCtrl',
    description: 'AnimateDiff with camera control extension',
    requiredInputs: ['reference_image', 'camera_poses', 'prompt'],
    optionalInputs: ['negative_prompt'],
    outputTypes: ['video'],
    comfyNodes: ['AnimateDiffLoader', 'CameraCtrlPoses'],
  },
  'custom-workflow': {
    name: 'Custom Workflow',
    description: 'Use your own ComfyUI workflow template',
    requiredInputs: ['workflow_template'],
    optionalInputs: [],
    outputTypes: ['video', 'image'],
    comfyNodes: [],
  },
};

// ============================================================================
// Helper Functions
// ============================================================================

export function getDefaultConfig(target: ExportTarget): Partial<ExportConfig> {
  return {
    ...EXPORT_PRESETS[target],
    target,
    negativePrompt: 'blurry, low quality, distorted, watermark',
  };
}

export function getRecommendedResolution(target: ExportTarget): { width: number; height: number } {
  const preset = EXPORT_PRESETS[target];
  return {
    width: preset.width || 1024,
    height: preset.height || 1024,
  };
}

export function getRecommendedFrameCount(target: ExportTarget): number {
  return EXPORT_PRESETS[target].frameCount || 81;
}

export function isVideoTarget(target: ExportTarget): boolean {
  const info = EXPORT_TARGET_INFO[target];
  return info.outputTypes.includes('video');
}

export function requiresDepthMap(target: ExportTarget): boolean {
  return EXPORT_PRESETS[target].exportDepthMap === true;
}

export function requiresCameraData(target: ExportTarget): boolean {
  return EXPORT_PRESETS[target].exportCameraData === true;
}
