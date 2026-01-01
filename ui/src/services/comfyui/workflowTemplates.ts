/**
 * ComfyUI Workflow Templates
 * Generates workflow JSON for various AI video generation models
 */

import type {
  ComfyUIWorkflow,
  ComfyUINode,
  NodeConnection,
  ExportTarget,
  Wan22CameraMotion,
  Uni3CTrajType,
  MotionCtrlSVDPreset,
} from '@/types/export';

// ============================================================================
// Types
// ============================================================================

export interface WorkflowParams {
  // Input images
  referenceImage?: string;
  lastFrameImage?: string;
  depthSequence?: string[];
  controlImages?: string[];

  // Camera data
  cameraData?: any;

  // Generation settings
  prompt: string;
  negativePrompt: string;
  width: number;
  height: number;
  frameCount: number;
  fps: number;
  seed?: number;
  steps?: number;
  cfgScale?: number;
  denoise?: number;

  // Model selection
  checkpoint?: string;
  vae?: string;
  controlnetModel?: string;
  loraModel?: string;
  loraStrength?: number;

  // Wan 2.2 specific
  wanModel?: 'i2v_480p' | 'i2v_720p' | 't2v_480p' | 't2v_720p';
  cameraMotion?: Wan22CameraMotion;

  // Uni3C specific
  trajType?: Uni3CTrajType;
  motionData?: any;

  // MotionCtrl specific
  motionPreset?: MotionCtrlSVDPreset;
  cameraPoses?: number[][];

  // Time-to-Move (TTM) specific
  ttmModel?: 'wan' | 'cogvideox' | 'svd';
  ttmLayers?: Array<{
    layerId: string;
    layerName: string;
    motionMask: string; // Base64 PNG or filename
    trajectory: Array<{ frame: number; x: number; y: number }>;
  }>;
  ttmCombinedMask?: string; // Combined motion mask
  ttmTweakIndex?: number;
  ttmTstrongIndex?: number;

  // Output settings
  outputFormat?: 'mp4' | 'webm' | 'gif' | 'images';
  outputFilename?: string;
}

// ============================================================================
// Node Factory Helpers
// ============================================================================

let nodeIdCounter = 1;

function resetNodeIds(): void {
  nodeIdCounter = 1;
}

function nextNodeId(): string {
  return String(nodeIdCounter++);
}

function createNode(classType: string, inputs: Record<string, any>, title?: string): ComfyUINode {
  const node: ComfyUINode = {
    class_type: classType,
    inputs,
  };
  if (title) {
    node._meta = { title };
  }
  return node;
}

function conn(nodeId: string, outputIndex: number = 0): NodeConnection {
  return [nodeId, outputIndex];
}

// ============================================================================
// Common Node Patterns
// ============================================================================

function addCheckpointLoader(
  workflow: ComfyUIWorkflow,
  checkpoint: string
): string {
  const id = nextNodeId();
  workflow[id] = createNode('CheckpointLoaderSimple', {
    ckpt_name: checkpoint,
  }, 'Load Checkpoint');
  return id;
}

function addVAELoader(
  workflow: ComfyUIWorkflow,
  vae: string
): string {
  const id = nextNodeId();
  workflow[id] = createNode('VAELoader', {
    vae_name: vae,
  }, 'Load VAE');
  return id;
}

function addCLIPTextEncode(
  workflow: ComfyUIWorkflow,
  clipConnection: NodeConnection,
  text: string,
  title: string
): string {
  const id = nextNodeId();
  workflow[id] = createNode('CLIPTextEncode', {
    clip: clipConnection,
    text,
  }, title);
  return id;
}

function addLoadImage(
  workflow: ComfyUIWorkflow,
  imageName: string,
  title?: string
): string {
  const id = nextNodeId();
  workflow[id] = createNode('LoadImage', {
    image: imageName,
  }, title || 'Load Image');
  return id;
}

function addImageResize(
  workflow: ComfyUIWorkflow,
  imageConnection: NodeConnection,
  width: number,
  height: number
): string {
  const id = nextNodeId();
  workflow[id] = createNode('ImageResize', {
    image: imageConnection,
    width,
    height,
    interpolation: 'lanczos',
    method: 'fill / crop',
    condition: 'always',
    multiple_of: 8,
  }, 'Resize Image');
  return id;
}

function addVAEEncode(
  workflow: ComfyUIWorkflow,
  imageConnection: NodeConnection,
  vaeConnection: NodeConnection
): string {
  const id = nextNodeId();
  workflow[id] = createNode('VAEEncode', {
    pixels: imageConnection,
    vae: vaeConnection,
  }, 'VAE Encode');
  return id;
}

function addVAEDecode(
  workflow: ComfyUIWorkflow,
  samplesConnection: NodeConnection,
  vaeConnection: NodeConnection
): string {
  const id = nextNodeId();
  workflow[id] = createNode('VAEDecode', {
    samples: samplesConnection,
    vae: vaeConnection,
  }, 'VAE Decode');
  return id;
}

function addKSampler(
  workflow: ComfyUIWorkflow,
  modelConnection: NodeConnection,
  positiveConnection: NodeConnection,
  negativeConnection: NodeConnection,
  latentConnection: NodeConnection,
  params: { seed?: number; steps?: number; cfg?: number; denoise?: number }
): string {
  const id = nextNodeId();
  workflow[id] = createNode('KSampler', {
    model: modelConnection,
    positive: positiveConnection,
    negative: negativeConnection,
    latent_image: latentConnection,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    steps: params.steps ?? 20,
    cfg: params.cfg ?? 7,
    sampler_name: 'euler',
    scheduler: 'normal',
    denoise: params.denoise ?? 1,
  }, 'KSampler');
  return id;
}

function addVideoOutput(
  workflow: ComfyUIWorkflow,
  imagesConnection: NodeConnection,
  params: { fps: number; format?: string; filename?: string }
): string {
  const id = nextNodeId();
  workflow[id] = createNode('VHS_VideoCombine', {
    images: imagesConnection,
    frame_rate: params.fps,
    loop_count: 0,
    filename_prefix: params.filename || 'lattice_output',
    format: params.format || 'video/h264-mp4',
    pingpong: false,
    save_output: true,
    audio: null,
    meta_batch: null,
  }, 'Video Output');
  return id;
}

// ============================================================================
// Wan 2.2 Image-to-Video Workflow
// ============================================================================

export function generateWan22I2VWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  // Model selection based on resolution
  const isHD = params.width > 640 || params.height > 640;
  const wanModel = params.wanModel || (isHD ? 'i2v_720p' : 'i2v_480p');

  // Load Wan model
  const wanLoaderId = nextNodeId();
  workflow[wanLoaderId] = createNode('DownloadAndLoadWan2_1Model', {
    model: `wan2.1_${wanModel}_bf16.safetensors`,
    base_precision: 'bf16',
    quantization: 'disabled',
  }, 'Load Wan Model');

  // Load VAE
  const vaeLoaderId = nextNodeId();
  workflow[vaeLoaderId] = createNode('DownloadAndLoadWanVAE', {
    vae: 'wan_2.1_vae.safetensors',
    precision: 'bf16',
  }, 'Load Wan VAE');

  // Load CLIP
  const clipLoaderId = nextNodeId();
  workflow[clipLoaderId] = createNode('DownloadAndLoadWanTextEncoder', {
    text_encoder: 'umt5-xxl-enc-bf16.safetensors',
    precision: 'bf16',
  }, 'Load Text Encoder');

  // Load reference image
  const imageLoaderId = addLoadImage(workflow, params.referenceImage || 'input.png', 'Reference Image');

  // Resize image
  const resizeId = addImageResize(workflow, conn(imageLoaderId), params.width, params.height);

  // Encode text prompts
  const positiveId = nextNodeId();
  workflow[positiveId] = createNode('WanTextEncode', {
    text_encoder: conn(clipLoaderId),
    prompt: params.prompt,
    force_offload: true,
  }, 'Positive Prompt');

  // Create empty latent
  const latentId = nextNodeId();
  workflow[latentId] = createNode('WanImageToVideo', {
    wan_model: conn(wanLoaderId),
    positive: conn(positiveId),
    image: conn(resizeId),
    vae: conn(vaeLoaderId),
    width: params.width,
    height: params.height,
    length: params.frameCount,
    steps: params.steps || 30,
    cfg: params.cfgScale || 5,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    scheduler: 'DPM++ 2M SDE',
    denoise_strength: params.denoise || 1,
  }, 'I2V Generation');

  // Decode video
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('WanVAEDecode', {
    vae: conn(vaeLoaderId),
    samples: conn(latentId),
    enable_vae_tiling: true,
    tile_sample_min_height: 240,
    tile_sample_min_width: 240,
    tile_overlap_factor_height: 0.2,
    tile_overlap_factor_width: 0.2,
  }, 'VAE Decode');

  // Output video
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || 'wan22_i2v',
  });

  return workflow;
}

// ============================================================================
// Wan 2.2 Fun Camera Workflow
// ============================================================================

export function generateWan22FunCameraWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  // Load Wan Fun Camera model
  const wanLoaderId = nextNodeId();
  workflow[wanLoaderId] = createNode('DownloadAndLoadWan2_1Model', {
    model: 'wan2.1_fun_camera_control_bf16.safetensors',
    base_precision: 'bf16',
    quantization: 'disabled',
  }, 'Load Wan Fun Camera');

  // Load VAE
  const vaeLoaderId = nextNodeId();
  workflow[vaeLoaderId] = createNode('DownloadAndLoadWanVAE', {
    vae: 'wan_2.1_vae.safetensors',
    precision: 'bf16',
  }, 'Load Wan VAE');

  // Load CLIP
  const clipLoaderId = nextNodeId();
  workflow[clipLoaderId] = createNode('DownloadAndLoadWanTextEncoder', {
    text_encoder: 'umt5-xxl-enc-bf16.safetensors',
    precision: 'bf16',
  }, 'Load Text Encoder');

  // Load reference image
  const imageLoaderId = addLoadImage(workflow, params.referenceImage || 'input.png', 'Reference Image');
  const resizeId = addImageResize(workflow, conn(imageLoaderId), params.width, params.height);

  // Encode prompt
  const positiveId = nextNodeId();
  workflow[positiveId] = createNode('WanTextEncode', {
    text_encoder: conn(clipLoaderId),
    prompt: params.prompt,
    force_offload: true,
  }, 'Positive Prompt');

  // Camera control
  const cameraCtrlId = nextNodeId();
  workflow[cameraCtrlId] = createNode('WanFunCameraMotion', {
    motion_type: params.cameraMotion || 'Static',
    length: params.frameCount,
  }, 'Camera Motion');

  // I2V with camera control
  const latentId = nextNodeId();
  workflow[latentId] = createNode('WanFunCameraI2V', {
    wan_model: conn(wanLoaderId),
    positive: conn(positiveId),
    image: conn(resizeId),
    camera_motion: conn(cameraCtrlId),
    vae: conn(vaeLoaderId),
    width: params.width,
    height: params.height,
    length: params.frameCount,
    steps: params.steps || 30,
    cfg: params.cfgScale || 5,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    scheduler: 'DPM++ 2M SDE',
  }, 'Fun Camera I2V');

  // Decode
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('WanVAEDecode', {
    vae: conn(vaeLoaderId),
    samples: conn(latentId),
    enable_vae_tiling: true,
  }, 'VAE Decode');

  // Output
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || 'wan22_fun_camera',
  });

  return workflow;
}

// ============================================================================
// Wan 2.2 First+Last Frame Workflow
// ============================================================================

export function generateWan22FirstLastWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  // Load model
  const wanLoaderId = nextNodeId();
  workflow[wanLoaderId] = createNode('DownloadAndLoadWan2_1Model', {
    model: 'wan2.1_flf2v_720p_bf16.safetensors',
    base_precision: 'bf16',
    quantization: 'disabled',
  }, 'Load Wan FLF2V');

  // Load VAE
  const vaeLoaderId = nextNodeId();
  workflow[vaeLoaderId] = createNode('DownloadAndLoadWanVAE', {
    vae: 'wan_2.1_vae.safetensors',
    precision: 'bf16',
  }, 'Load VAE');

  // Load CLIP
  const clipLoaderId = nextNodeId();
  workflow[clipLoaderId] = createNode('DownloadAndLoadWanTextEncoder', {
    text_encoder: 'umt5-xxl-enc-bf16.safetensors',
    precision: 'bf16',
  }, 'Load Text Encoder');

  // Load first and last images
  const firstImageId = addLoadImage(workflow, params.referenceImage || 'first.png', 'First Frame');
  const lastImageId = addLoadImage(workflow, params.lastFrameImage || 'last.png', 'Last Frame');

  // Resize both
  const resizeFirstId = addImageResize(workflow, conn(firstImageId), params.width, params.height);
  const resizeLastId = addImageResize(workflow, conn(lastImageId), params.width, params.height);

  // Encode prompt
  const positiveId = nextNodeId();
  workflow[positiveId] = createNode('WanTextEncode', {
    text_encoder: conn(clipLoaderId),
    prompt: params.prompt,
    force_offload: true,
  }, 'Positive Prompt');

  // First+Last frame generation
  const latentId = nextNodeId();
  workflow[latentId] = createNode('WanFirstLastFrameToVideo', {
    wan_model: conn(wanLoaderId),
    positive: conn(positiveId),
    first_frame: conn(resizeFirstId),
    last_frame: conn(resizeLastId),
    vae: conn(vaeLoaderId),
    width: params.width,
    height: params.height,
    length: params.frameCount,
    steps: params.steps || 30,
    cfg: params.cfgScale || 5,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    scheduler: 'DPM++ 2M SDE',
  }, 'First+Last I2V');

  // Decode
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('WanVAEDecode', {
    vae: conn(vaeLoaderId),
    samples: conn(latentId),
    enable_vae_tiling: true,
  }, 'VAE Decode');

  // Output
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || 'wan22_flf',
  });

  return workflow;
}

// ============================================================================
// Uni3C Camera Control Workflow
// ============================================================================

export function generateUni3CWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  // Load Uni3C model
  const uni3cLoaderId = nextNodeId();
  workflow[uni3cLoaderId] = createNode('DownloadAndLoadUni3CModel', {
    model: 'uni3c_camera_control.safetensors',
    precision: 'bf16',
  }, 'Load Uni3C');

  // Load base video model (e.g., SVD)
  const baseModelId = nextNodeId();
  workflow[baseModelId] = createNode('ImageOnlyCheckpointLoader', {
    ckpt_name: params.checkpoint || 'svd_xt_1_1.safetensors',
  }, 'Load Base Model');

  // Load reference image
  const imageLoaderId = addLoadImage(workflow, params.referenceImage || 'input.png', 'Reference Image');
  const resizeId = addImageResize(workflow, conn(imageLoaderId), params.width, params.height);

  // Create camera trajectory
  const trajId = nextNodeId();
  if (params.trajType === 'custom' && params.cameraData?.trajectory) {
    workflow[trajId] = createNode('Uni3CCustomTrajectory', {
      trajectory_data: JSON.stringify(params.cameraData.trajectory),
      length: params.frameCount,
    }, 'Custom Trajectory');
  } else {
    workflow[trajId] = createNode('Uni3CPresetTrajectory', {
      traj_type: params.trajType || 'orbit',
      length: params.frameCount,
    }, 'Preset Trajectory');
  }

  // Apply Uni3C control
  const controlId = nextNodeId();
  workflow[controlId] = createNode('ApplyUni3CCameraControl', {
    model: conn(baseModelId),
    uni3c: conn(uni3cLoaderId),
    trajectory: conn(trajId),
    image: conn(resizeId),
    control_strength: 1.0,
  }, 'Apply Camera Control');

  // Encode
  const encodeId = nextNodeId();
  workflow[encodeId] = createNode('SVDEncode', {
    model: conn(controlId),
    image: conn(resizeId),
    vae: conn(baseModelId, 2),
    width: params.width,
    height: params.height,
    video_frames: params.frameCount,
    motion_bucket_id: 127,
    fps: params.fps,
    augmentation_level: 0,
  }, 'SVD Encode');

  // Sample
  const sampleId = addKSampler(
    workflow,
    conn(controlId),
    conn(encodeId, 1),
    conn(encodeId, 2),
    conn(encodeId),
    { seed: params.seed, steps: params.steps || 25, cfg: params.cfgScale || 2.5, denoise: 1 }
  );

  // Decode
  const decodeId = addVAEDecode(workflow, conn(sampleId), conn(baseModelId, 2));

  // Output
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || 'uni3c_output',
  });

  return workflow;
}

// ============================================================================
// MotionCtrl Workflow
// ============================================================================

export function generateMotionCtrlWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  // Load MotionCtrl
  const motionCtrlId = nextNodeId();
  workflow[motionCtrlId] = createNode('LoadMotionCtrl', {
    model: 'motionctrl.pth',
  }, 'Load MotionCtrl');

  // Load base model
  const baseModelId = nextNodeId();
  workflow[baseModelId] = createNode('ImageOnlyCheckpointLoader', {
    ckpt_name: params.checkpoint || 'svd_xt_1_1.safetensors',
  }, 'Load Base Model');

  // Load reference image
  const imageLoaderId = addLoadImage(workflow, params.referenceImage || 'input.png', 'Reference Image');
  const resizeId = addImageResize(workflow, conn(imageLoaderId), params.width, params.height);

  // Create camera poses
  const posesId = nextNodeId();
  if (params.cameraPoses) {
    workflow[posesId] = createNode('MotionCtrlCameraPoses', {
      poses: JSON.stringify(params.cameraPoses),
    }, 'Camera Poses');
  } else {
    workflow[posesId] = createNode('MotionCtrlPresetPoses', {
      preset: params.motionPreset || 'static',
      length: params.frameCount,
    }, 'Preset Poses');
  }

  // Apply MotionCtrl
  const controlId = nextNodeId();
  workflow[controlId] = createNode('ApplyMotionCtrl', {
    model: conn(baseModelId),
    motion_ctrl: conn(motionCtrlId),
    camera_poses: conn(posesId),
    control_strength: 1.0,
  }, 'Apply MotionCtrl');

  // SVD Encode
  const encodeId = nextNodeId();
  workflow[encodeId] = createNode('SVDEncode', {
    model: conn(controlId),
    image: conn(resizeId),
    vae: conn(baseModelId, 2),
    width: params.width,
    height: params.height,
    video_frames: params.frameCount,
    motion_bucket_id: 127,
    fps: params.fps,
    augmentation_level: 0,
  }, 'SVD Encode');

  // Sample
  const sampleId = addKSampler(
    workflow,
    conn(controlId),
    conn(encodeId, 1),
    conn(encodeId, 2),
    conn(encodeId),
    { seed: params.seed, steps: params.steps || 25, cfg: params.cfgScale || 2.5 }
  );

  // Decode
  const decodeId = addVAEDecode(workflow, conn(sampleId), conn(baseModelId, 2));

  // Output
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || 'motionctrl_output',
  });

  return workflow;
}

// ============================================================================
// ControlNet Depth Workflow
// ============================================================================

export function generateControlNetDepthWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  // Load checkpoint
  const checkpointId = addCheckpointLoader(workflow, params.checkpoint || 'sd_xl_base_1.0.safetensors');

  // Load ControlNet
  const controlnetId = nextNodeId();
  workflow[controlnetId] = createNode('ControlNetLoader', {
    control_net_name: params.controlnetModel || 'control_v11f1p_sd15_depth.pth',
  }, 'Load ControlNet Depth');

  // Load depth sequence (as image batch)
  const depthLoaderId = nextNodeId();
  workflow[depthLoaderId] = createNode('VHS_LoadImages', {
    directory: 'depth_sequence',
    image_load_cap: params.frameCount,
    skip_first_images: 0,
    select_every_nth: 1,
  }, 'Load Depth Sequence');

  // Load reference image
  const refImageId = addLoadImage(workflow, params.referenceImage || 'reference.png', 'Reference Image');
  const resizeRefId = addImageResize(workflow, conn(refImageId), params.width, params.height);

  // Encode prompts
  const positiveId = addCLIPTextEncode(workflow, conn(checkpointId, 1), params.prompt, 'Positive');
  const negativeId = addCLIPTextEncode(workflow, conn(checkpointId, 1), params.negativePrompt, 'Negative');

  // Apply ControlNet
  const applyControlId = nextNodeId();
  workflow[applyControlId] = createNode('ControlNetApply', {
    conditioning: conn(positiveId),
    control_net: conn(controlnetId),
    image: conn(depthLoaderId),
    strength: 1.0,
  }, 'Apply ControlNet');

  // VAE Encode reference
  const encodeRefId = addVAEEncode(workflow, conn(resizeRefId), conn(checkpointId, 2));

  // KSampler
  const sampleId = addKSampler(
    workflow,
    conn(checkpointId),
    conn(applyControlId),
    conn(negativeId),
    conn(encodeRefId),
    { seed: params.seed, steps: params.steps || 20, cfg: params.cfgScale || 7, denoise: params.denoise || 0.75 }
  );

  // Decode
  const decodeId = addVAEDecode(workflow, conn(sampleId), conn(checkpointId, 2));

  // Output
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || 'controlnet_depth',
  });

  return workflow;
}

// ============================================================================
// AnimateDiff with CameraCtrl Workflow
// ============================================================================

export function generateAnimateDiffCameraCtrlWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  // Load checkpoint
  const checkpointId = addCheckpointLoader(workflow, params.checkpoint || 'dreamshaper_8.safetensors');

  // Load AnimateDiff
  const animateDiffId = nextNodeId();
  workflow[animateDiffId] = createNode('ADE_LoadAnimateDiffModel', {
    model_name: 'mm_sd_v15_v2.ckpt',
  }, 'Load AnimateDiff');

  // Load CameraCtrl
  const cameraCtrlId = nextNodeId();
  workflow[cameraCtrlId] = createNode('ADE_LoadCameraCtrlModel', {
    model_name: 'cameractrl_v10.ckpt',
  }, 'Load CameraCtrl');

  // Create camera poses
  const posesId = nextNodeId();
  if (params.cameraPoses) {
    workflow[posesId] = createNode('ADE_CameraCtrlPoses', {
      poses: JSON.stringify(params.cameraPoses),
    }, 'Camera Poses');
  } else {
    workflow[posesId] = createNode('ADE_CameraCtrlPreset', {
      motion_type: params.cameraMotion || 'Static',
      speed: 1.0,
      frame_length: params.frameCount,
    }, 'Camera Preset');
  }

  // Apply AnimateDiff + CameraCtrl
  const applyADId = nextNodeId();
  workflow[applyADId] = createNode('ADE_ApplyAnimateDiffModel', {
    model: conn(checkpointId),
    motion_model: conn(animateDiffId),
  }, 'Apply AnimateDiff');

  const applyCamId = nextNodeId();
  workflow[applyCamId] = createNode('ADE_ApplyCameraCtrl', {
    model: conn(applyADId),
    cameractrl: conn(cameraCtrlId),
    poses: conn(posesId),
  }, 'Apply CameraCtrl');

  // Encode prompts
  const positiveId = addCLIPTextEncode(workflow, conn(checkpointId, 1), params.prompt, 'Positive');
  const negativeId = addCLIPTextEncode(workflow, conn(checkpointId, 1), params.negativePrompt, 'Negative');

  // Empty latent batch
  const latentId = nextNodeId();
  workflow[latentId] = createNode('EmptyLatentImage', {
    width: params.width,
    height: params.height,
    batch_size: params.frameCount,
  }, 'Empty Latent');

  // Sample
  const sampleId = addKSampler(
    workflow,
    conn(applyCamId),
    conn(positiveId),
    conn(negativeId),
    conn(latentId),
    { seed: params.seed, steps: params.steps || 20, cfg: params.cfgScale || 7 }
  );

  // Decode
  const decodeId = addVAEDecode(workflow, conn(sampleId), conn(checkpointId, 2));

  // Output
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || 'animatediff_cameractrl',
  });

  return workflow;
}

// ============================================================================
// CogVideoX Workflow
// ============================================================================

export function generateCogVideoXWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  // Load CogVideoX
  const cogVideoId = nextNodeId();
  workflow[cogVideoId] = createNode('DownloadAndLoadCogVideoModel', {
    model: 'CogVideoX-5b-I2V',
    precision: 'bf16',
  }, 'Load CogVideoX');

  // Load T5 encoder
  const t5Id = nextNodeId();
  workflow[t5Id] = createNode('DownloadAndLoadCogVideoTextEncoder', {
    model: 't5-v1_1-xxl-encoder-bf16',
    precision: 'bf16',
  }, 'Load T5 Encoder');

  // Load VAE
  const vaeId = nextNodeId();
  workflow[vaeId] = createNode('DownloadAndLoadCogVideoVAE', {
    model: 'cogvideox_vae',
    precision: 'bf16',
  }, 'Load CogVideo VAE');

  // Load reference image
  const imageLoaderId = addLoadImage(workflow, params.referenceImage || 'input.png', 'Reference Image');
  const resizeId = addImageResize(workflow, conn(imageLoaderId), params.width, params.height);

  // Encode prompt
  const encodePromptId = nextNodeId();
  workflow[encodePromptId] = createNode('CogVideoTextEncode', {
    text_encoder: conn(t5Id),
    prompt: params.prompt,
    force_offload: true,
  }, 'Encode Prompt');

  // Generate
  const generateId = nextNodeId();
  workflow[generateId] = createNode('CogVideoImageToVideo', {
    model: conn(cogVideoId),
    positive: conn(encodePromptId),
    image: conn(resizeId),
    vae: conn(vaeId),
    width: params.width,
    height: params.height,
    num_frames: params.frameCount,
    steps: params.steps || 50,
    cfg: params.cfgScale || 6,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    scheduler: 'CogVideoX DDIM',
  }, 'CogVideoX I2V');

  // Decode
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('CogVideoDecode', {
    vae: conn(vaeId),
    samples: conn(generateId),
    enable_vae_tiling: true,
  }, 'Decode Video');

  // Output
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || 'cogvideox_output',
  });

  return workflow;
}

// ============================================================================
// Time-to-Move (TTM) Workflow
// ============================================================================

/**
 * Generate a Time-to-Move workflow for multi-layer motion-controlled video generation.
 * TTM uses per-layer motion masks and trajectories to control object movement.
 *
 * Reference: https://time-to-move.github.io/
 */
export function generateTTMWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  const ttmModel = params.ttmModel || 'wan';
  const layers = params.ttmLayers || [];

  // Load reference image
  const imageLoaderId = addLoadImage(workflow, params.referenceImage || 'reference.png', 'Reference Image');
  const resizeId = addImageResize(workflow, conn(imageLoaderId), params.width, params.height);

  // Load combined motion mask
  const combinedMaskId = nextNodeId();
  workflow[combinedMaskId] = createNode('LoadImage', {
    image: params.ttmCombinedMask || 'combined_motion_mask.png',
  }, 'Combined Motion Mask');

  // Load per-layer motion masks and create trajectory controls
  const layerMaskIds: string[] = [];
  const trajectoryIds: string[] = [];

  for (let i = 0; i < layers.length; i++) {
    const layer = layers[i];

    // Load layer mask
    const maskId = nextNodeId();
    workflow[maskId] = createNode('LoadImage', {
      image: layer.motionMask,
    }, `Layer ${i + 1} Mask: ${layer.layerName}`);
    layerMaskIds.push(maskId);

    // Create trajectory from keyframe data
    const trajId = nextNodeId();
    workflow[trajId] = createNode('TTM_TrajectoryFromPoints', {
      points: JSON.stringify(layer.trajectory.map(t => [t.x, t.y])),
      frames: JSON.stringify(layer.trajectory.map(t => t.frame)),
      total_frames: params.frameCount,
      interpolation: 'linear',
    }, `Trajectory: ${layer.layerName}`);
    trajectoryIds.push(trajId);
  }

  // Combine all layer masks and trajectories
  let combinedLayerDataId: string | null = null;

  if (layers.length > 0) {
    // Create TTM layer combination node
    combinedLayerDataId = nextNodeId();
    workflow[combinedLayerDataId] = createNode('TTM_CombineLayers', {
      masks: layerMaskIds.map(id => conn(id)),
      trajectories: trajectoryIds.map(id => conn(id)),
      blend_mode: 'additive',
    }, 'Combine Layer Data');
  }

  // Model-specific generation
  if (ttmModel === 'wan') {
    // Load Wan model
    const wanLoaderId = nextNodeId();
    workflow[wanLoaderId] = createNode('DownloadAndLoadWan2_1Model', {
      model: 'wan2.1_i2v_480p_bf16.safetensors',
      base_precision: 'bf16',
      quantization: 'disabled',
    }, 'Load Wan Model');

    // Load VAE
    const vaeLoaderId = nextNodeId();
    workflow[vaeLoaderId] = createNode('DownloadAndLoadWanVAE', {
      vae: 'wan_2.1_vae.safetensors',
      precision: 'bf16',
    }, 'Load Wan VAE');

    // Load CLIP
    const clipLoaderId = nextNodeId();
    workflow[clipLoaderId] = createNode('DownloadAndLoadWanTextEncoder', {
      text_encoder: 'umt5-xxl-enc-bf16.safetensors',
      precision: 'bf16',
    }, 'Load Text Encoder');

    // Encode prompt
    const positiveId = nextNodeId();
    workflow[positiveId] = createNode('WanTextEncode', {
      text_encoder: conn(clipLoaderId),
      prompt: params.prompt,
      force_offload: true,
    }, 'Positive Prompt');

    // Apply TTM motion control
    const ttmControlId = nextNodeId();
    workflow[ttmControlId] = createNode('TTM_ApplyMotionControl', {
      wan_model: conn(wanLoaderId),
      image: conn(resizeId),
      motion_mask: conn(combinedMaskId),
      layer_data: combinedLayerDataId ? conn(combinedLayerDataId) : null,
      tweak_index: params.ttmTweakIndex ?? 0,
      tstrong_index: params.ttmTstrongIndex ?? 0,
    }, 'Apply TTM Motion');

    // Generate
    const latentId = nextNodeId();
    workflow[latentId] = createNode('WanImageToVideo', {
      wan_model: conn(ttmControlId),
      positive: conn(positiveId),
      image: conn(resizeId),
      vae: conn(vaeLoaderId),
      width: params.width,
      height: params.height,
      length: params.frameCount,
      steps: params.steps || 30,
      cfg: params.cfgScale || 5,
      seed: params.seed ?? Math.floor(Math.random() * 2147483647),
      scheduler: 'DPM++ 2M SDE',
      denoise_strength: params.denoise || 1,
    }, 'TTM I2V Generation');

    // Decode
    const decodeId = nextNodeId();
    workflow[decodeId] = createNode('WanVAEDecode', {
      vae: conn(vaeLoaderId),
      samples: conn(latentId),
      enable_vae_tiling: true,
      tile_sample_min_height: 240,
      tile_sample_min_width: 240,
      tile_overlap_factor_height: 0.2,
      tile_overlap_factor_width: 0.2,
    }, 'VAE Decode');

    // Output
    addVideoOutput(workflow, conn(decodeId), {
      fps: params.fps,
      filename: params.outputFilename || 'ttm_output',
    });

  } else if (ttmModel === 'cogvideox') {
    // CogVideoX-based TTM generation
    const cogVideoId = nextNodeId();
    workflow[cogVideoId] = createNode('DownloadAndLoadCogVideoModel', {
      model: 'CogVideoX-5b-I2V',
      precision: 'bf16',
    }, 'Load CogVideoX');

    const t5Id = nextNodeId();
    workflow[t5Id] = createNode('DownloadAndLoadCogVideoTextEncoder', {
      model: 't5-v1_1-xxl-encoder-bf16',
      precision: 'bf16',
    }, 'Load T5 Encoder');

    const vaeId = nextNodeId();
    workflow[vaeId] = createNode('DownloadAndLoadCogVideoVAE', {
      model: 'cogvideox_vae',
      precision: 'bf16',
    }, 'Load CogVideo VAE');

    const encodePromptId = nextNodeId();
    workflow[encodePromptId] = createNode('CogVideoTextEncode', {
      text_encoder: conn(t5Id),
      prompt: params.prompt,
      force_offload: true,
    }, 'Encode Prompt');

    // Apply TTM motion control
    const ttmControlId = nextNodeId();
    workflow[ttmControlId] = createNode('TTM_ApplyMotionControlCogVideo', {
      model: conn(cogVideoId),
      image: conn(resizeId),
      motion_mask: conn(combinedMaskId),
      layer_data: combinedLayerDataId ? conn(combinedLayerDataId) : null,
      tweak_index: params.ttmTweakIndex ?? 0,
      tstrong_index: params.ttmTstrongIndex ?? 0,
    }, 'Apply TTM Motion');

    const generateId = nextNodeId();
    workflow[generateId] = createNode('CogVideoImageToVideo', {
      model: conn(ttmControlId),
      positive: conn(encodePromptId),
      image: conn(resizeId),
      vae: conn(vaeId),
      width: params.width,
      height: params.height,
      num_frames: params.frameCount,
      steps: params.steps || 50,
      cfg: params.cfgScale || 6,
      seed: params.seed ?? Math.floor(Math.random() * 2147483647),
      scheduler: 'CogVideoX DDIM',
    }, 'CogVideoX I2V');

    const decodeId = nextNodeId();
    workflow[decodeId] = createNode('CogVideoDecode', {
      vae: conn(vaeId),
      samples: conn(generateId),
      enable_vae_tiling: true,
    }, 'Decode Video');

    addVideoOutput(workflow, conn(decodeId), {
      fps: params.fps,
      filename: params.outputFilename || 'ttm_cogvideo_output',
    });

  } else {
    // SVD-based TTM generation
    const baseModelId = nextNodeId();
    workflow[baseModelId] = createNode('ImageOnlyCheckpointLoader', {
      ckpt_name: params.checkpoint || 'svd_xt_1_1.safetensors',
    }, 'Load SVD');

    // Apply TTM motion control
    const ttmControlId = nextNodeId();
    workflow[ttmControlId] = createNode('TTM_ApplyMotionControlSVD', {
      model: conn(baseModelId),
      image: conn(resizeId),
      motion_mask: conn(combinedMaskId),
      layer_data: combinedLayerDataId ? conn(combinedLayerDataId) : null,
      tweak_index: params.ttmTweakIndex ?? 0,
      tstrong_index: params.ttmTstrongIndex ?? 0,
    }, 'Apply TTM Motion');

    const encodeId = nextNodeId();
    workflow[encodeId] = createNode('SVDEncode', {
      model: conn(ttmControlId),
      image: conn(resizeId),
      vae: conn(baseModelId, 2),
      width: params.width,
      height: params.height,
      video_frames: params.frameCount,
      motion_bucket_id: 127,
      fps: params.fps,
      augmentation_level: 0,
    }, 'SVD Encode');

    const sampleId = addKSampler(
      workflow,
      conn(ttmControlId),
      conn(encodeId, 1),
      conn(encodeId, 2),
      conn(encodeId),
      { seed: params.seed, steps: params.steps || 25, cfg: params.cfgScale || 2.5, denoise: 1 }
    );

    const decodeId = addVAEDecode(workflow, conn(sampleId), conn(baseModelId, 2));

    addVideoOutput(workflow, conn(decodeId), {
      fps: params.fps,
      filename: params.outputFilename || 'ttm_svd_output',
    });
  }

  return workflow;
}

// ============================================================================
// Generic ControlNet Workflow (Canny, Lineart, etc.)
// ============================================================================

export function generateControlNetWorkflow(
  params: WorkflowParams,
  controlType: 'canny' | 'lineart' | 'softedge' | 'normal' | 'seg'
): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  const controlnetModels: Record<string, string> = {
    canny: 'control_v11p_sd15_canny.pth',
    lineart: 'control_v11p_sd15_lineart.pth',
    softedge: 'control_v11p_sd15_softedge.pth',
    normal: 'control_v11p_sd15_normalbae.pth',
    seg: 'control_v11p_sd15_seg.pth',
  };

  // Load checkpoint
  const checkpointId = addCheckpointLoader(workflow, params.checkpoint || 'v1-5-pruned-emaonly.safetensors');

  // Load ControlNet
  const controlnetId = nextNodeId();
  workflow[controlnetId] = createNode('ControlNetLoader', {
    control_net_name: params.controlnetModel || controlnetModels[controlType],
  }, `Load ControlNet ${controlType}`);

  // Load control images
  const controlLoaderId = nextNodeId();
  workflow[controlLoaderId] = createNode('VHS_LoadImages', {
    directory: 'control_sequence',
    image_load_cap: params.frameCount,
    skip_first_images: 0,
    select_every_nth: 1,
  }, 'Load Control Sequence');

  // Encode prompts
  const positiveId = addCLIPTextEncode(workflow, conn(checkpointId, 1), params.prompt, 'Positive');
  const negativeId = addCLIPTextEncode(workflow, conn(checkpointId, 1), params.negativePrompt, 'Negative');

  // Apply ControlNet
  const applyControlId = nextNodeId();
  workflow[applyControlId] = createNode('ControlNetApply', {
    conditioning: conn(positiveId),
    control_net: conn(controlnetId),
    image: conn(controlLoaderId),
    strength: 1.0,
  }, 'Apply ControlNet');

  // Empty latent batch
  const latentId = nextNodeId();
  workflow[latentId] = createNode('EmptyLatentImage', {
    width: params.width,
    height: params.height,
    batch_size: params.frameCount,
  }, 'Empty Latent');

  // Sample
  const sampleId = addKSampler(
    workflow,
    conn(checkpointId),
    conn(applyControlId),
    conn(negativeId),
    conn(latentId),
    { seed: params.seed, steps: params.steps || 20, cfg: params.cfgScale || 7 }
  );

  // Decode
  const decodeId = addVAEDecode(workflow, conn(sampleId), conn(checkpointId, 2));

  // Output
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || `controlnet_${controlType}`,
  });

  return workflow;
}

// ============================================================================
// Workflow Generator Router
// ============================================================================

export function generateWorkflowForTarget(
  target: ExportTarget,
  params: WorkflowParams
): ComfyUIWorkflow {
  switch (target) {
    case 'wan22-i2v':
      return generateWan22I2VWorkflow(params);

    case 'wan22-t2v':
      // T2V is similar to I2V but without reference image
      return generateWan22I2VWorkflow({ ...params, referenceImage: undefined });

    case 'wan22-fun-camera':
      return generateWan22FunCameraWorkflow(params);

    case 'wan22-first-last':
      return generateWan22FirstLastWorkflow(params);

    case 'uni3c-camera':
    case 'uni3c-motion':
      return generateUni3CWorkflow(params);

    case 'motionctrl':
    case 'motionctrl-svd':
      return generateMotionCtrlWorkflow(params);

    case 'cogvideox':
      return generateCogVideoXWorkflow(params);

    case 'controlnet-depth':
      return generateControlNetDepthWorkflow(params);

    case 'controlnet-canny':
      return generateControlNetWorkflow(params, 'canny');

    case 'controlnet-lineart':
      return generateControlNetWorkflow(params, 'lineart');

    case 'animatediff-cameractrl':
      return generateAnimateDiffCameraCtrlWorkflow(params);

    case 'ttm':
    case 'ttm-wan':
    case 'ttm-cogvideox':
    case 'ttm-svd':
      // Time-to-Move workflow for multi-layer motion control
      return generateTTMWorkflow(params);

    case 'custom-workflow':
      // Return empty workflow for custom - user provides their own
      return {};

    default:
      throw new Error(`Unknown export target: ${target}`);
  }
}

// ============================================================================
// Workflow Utilities
// ============================================================================

export function injectParameters(
  workflow: ComfyUIWorkflow,
  replacements: Record<string, any>
): ComfyUIWorkflow {
  const workflowStr = JSON.stringify(workflow);
  let result = workflowStr;

  for (const [key, value] of Object.entries(replacements)) {
    const placeholder = `{{${key}}}`;
    const replacement = typeof value === 'string' ? value : JSON.stringify(value);
    result = result.replace(new RegExp(placeholder, 'g'), replacement);
  }

  return JSON.parse(result);
}

export function validateWorkflow(workflow: ComfyUIWorkflow): {
  valid: boolean;
  errors: string[];
  warnings: string[];
} {
  const errors: string[] = [];
  const warnings: string[] = [];

  const nodeIds = Object.keys(workflow);

  for (const [nodeId, node] of Object.entries(workflow)) {
    // Check class_type exists
    if (!node.class_type) {
      errors.push(`Node ${nodeId}: missing class_type`);
    }

    // Check connections reference valid nodes
    for (const [inputName, inputValue] of Object.entries(node.inputs)) {
      if (Array.isArray(inputValue) && inputValue.length === 2) {
        const [refNodeId] = inputValue;
        if (typeof refNodeId === 'string' && !nodeIds.includes(refNodeId)) {
          errors.push(`Node ${nodeId}.${inputName}: references non-existent node ${refNodeId}`);
        }
      }
    }
  }

  // Check for output nodes
  const hasOutput = Object.values(workflow).some(
    node => node.class_type.includes('Save') || node.class_type.includes('Output') || node.class_type.includes('Preview')
  );

  if (!hasOutput) {
    warnings.push('Workflow has no output/save nodes');
  }

  return {
    valid: errors.length === 0,
    errors,
    warnings,
  };
}

export function getWorkflowInputNodes(workflow: ComfyUIWorkflow): string[] {
  return Object.entries(workflow)
    .filter(([_, node]) =>
      node.class_type === 'LoadImage' ||
      node.class_type === 'VHS_LoadImages' ||
      node.class_type.includes('LoadImage')
    )
    .map(([id]) => id);
}

export function getWorkflowOutputNodes(workflow: ComfyUIWorkflow): string[] {
  return Object.entries(workflow)
    .filter(([_, node]) =>
      node.class_type.includes('Save') ||
      node.class_type.includes('Output') ||
      node.class_type.includes('Preview') ||
      node.class_type === 'VHS_VideoCombine'
    )
    .map(([id]) => id);
}
