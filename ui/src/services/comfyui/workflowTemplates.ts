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

  // Uni3C specific (camera control via render_latent)
  trajType?: Uni3CTrajType;
  motionData?: any;
  uni3cRenderVideo?: string; // Pre-rendered camera motion video for render_latent
  uni3cStrength?: number; // ControlNet strength (default 1.0)
  uni3cStartPercent?: number; // Start percent (default 0.0)
  uni3cEndPercent?: number; // End percent (default 1.0)

  // MotionCtrl specific
  motionPreset?: MotionCtrlSVDPreset;
  cameraPoses?: number[][];

  // Time-to-Move (TTM) specific
  ttmModel?: 'wan' | 'cogvideox' | 'svd';
  ttmEndFrame?: string; // End frame image (target destination)
  ttmMaskDirectory?: string; // Directory containing PNG mask sequence from SAM3
  ttmMotionVideo?: string; // ⚠️ CRITICAL: Motion signal VIDEO to encode as reference_latents
  ttmMotionVideoDirectory?: string; // Alternative: directory of motion video frames
  ttmLayers?: Array<{
    layerId: string;
    layerName: string;
    motionMask: string; // Base64 PNG or filename
    trajectory: Array<{ frame: number; x: number; y: number }>;
  }>;
  ttmCombinedMask?: string; // Combined motion mask (deprecated - use ttmMaskDirectory)
  ttmStartStep?: number; // Start step for TTM application (default 0)
  ttmEndStep?: number; // End step for TTM application (default 1)

  // Wan-Move specific (point trajectories)
  trackCoords?: string; // JSON string: [[{x,y}, ...], ...] for multiple tracks
  wanMoveStrength?: number; // Track strength (default 1.0)

  // ATI (Any Trajectory Instruction) specific
  atiTemperature?: number; // Temperature for ATI (default 220.0)
  atiTopk?: number; // Top-k for ATI (default 2)
  atiStartPercent?: number; // Start percent (default 0.0)
  atiEndPercent?: number; // End percent (default 1.0)

  // Light-X specific (LoRA-based relighting)
  lightXLora?: string; // Path to Light-X LoRA file
  model?: string; // Base model for workflow

  // SCAIL specific (pose + reference control)
  scailReferenceImage?: string; // Reference image for SCAIL
  scailPoseVideo?: string; // Pose video for SCAIL
  scailPoseDirectory?: string; // Alternative: directory of pose frames
  scailRefStrength?: number; // Reference strength (default 1.0)
  scailRefStartPercent?: number; // Reference start percent (default 0.0)
  scailRefEndPercent?: number; // Reference end percent (default 1.0)
  scailPoseStrength?: number; // Pose strength (default 1.0)
  scailPoseStartPercent?: number; // Pose start percent (default 0.0)
  scailPoseEndPercent?: number; // Pose end percent (default 1.0)

  // CLIP Vision
  clipVision?: string; // Path to CLIP Vision model

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

  // ⚠️ REWRITTEN to use correct Kijai WanVideoWrapper nodes
  // UNI3C_EMBEDS goes to WanVideoSampler.uni3c_embeds (SEPARATE from image_embeds)

  // 1. Load Wan model
  const modelLoaderId = nextNodeId();
  workflow[modelLoaderId] = createNode('WanVideoModelLoader', {
    model: params.model || 'wan2.1_i2v_480p_bf16.safetensors',
    base_precision: 'bf16',
    quantization: 'disabled',
  }, 'Load Wan Model');

  // 2. Load VAE
  const vaeLoaderId = nextNodeId();
  workflow[vaeLoaderId] = createNode('WanVideoVAELoader', {
    vae: params.vae || 'wan_2.1_vae.safetensors',
    precision: 'bf16',
  }, 'Load Wan VAE');

  // 3. Load CLIP Vision
  const clipVisionId = nextNodeId();
  workflow[clipVisionId] = createNode('CLIPVisionLoader', {
    clip_name: params.clipVision || 'sigclip_vision_patch14_384.safetensors',
  }, 'Load CLIP Vision');

  // 4. Load Text Encoder
  const textEncoderId = nextNodeId();
  workflow[textEncoderId] = createNode('LoadWanVideoT5TextEncoder', {
    text_encoder: 'umt5-xxl-enc-bf16.safetensors',
    precision: 'bf16',
  }, 'Load Text Encoder');

  // 5. Load Uni3C ControlNet (correct Kijai node)
  const uni3cLoaderId = nextNodeId();
  workflow[uni3cLoaderId] = createNode('WanVideoUni3C_ControlnetLoader', {
    model: params.controlnetModel || 'uni3c_controlnet.safetensors',
    base_precision: 'fp16',
    quantization: 'disabled',
    load_device: 'offload_device',
    attention_mode: 'sdpa',
  }, 'Load Uni3C ControlNet');

  // 6. Load reference image
  const imageLoaderId = addLoadImage(workflow, params.referenceImage || 'input.png', 'Reference Image');
  const resizeId = addImageResize(workflow, conn(imageLoaderId), params.width, params.height);

  // 7. Load camera motion render (for render_latent)
  // This is the pre-rendered camera motion video that Uni3C uses as guidance
  const renderVideoId = nextNodeId();
  workflow[renderVideoId] = createNode('VHS_LoadVideo', {
    video: params.uni3cRenderVideo || 'camera_render.mp4',
    force_rate: params.fps || 16,
    force_size: 'Disabled',
    frame_load_cap: params.frameCount,
    skip_first_frames: 0,
    select_every_nth: 1,
  }, 'Load Camera Render Video');

  // 8. Encode render video to latents (for render_latent input)
  const renderLatentsId = nextNodeId();
  workflow[renderLatentsId] = createNode('WanVideoEncode', {
    vae: conn(vaeLoaderId),
    image: conn(renderVideoId),
  }, 'Encode Render Video to Latents');

  // 9. Create Uni3C embeds (correct Kijai node)
  // UNI3C_EMBEDS structure: {controlnet, controlnet_weight, start, end, render_latent, ...}
  const uni3cEmbedsId = nextNodeId();
  workflow[uni3cEmbedsId] = createNode('WanVideoUni3C_embeds', {
    controlnet: conn(uni3cLoaderId),
    strength: params.uni3cStrength ?? 1.0,
    start_percent: params.uni3cStartPercent ?? 0.0,
    end_percent: params.uni3cEndPercent ?? 1.0,
    render_latent: conn(renderLatentsId),
    offload: true,
  }, 'Create Uni3C Embeds');

  // 10. Text encoding
  const positiveId = nextNodeId();
  workflow[positiveId] = createNode('WanVideoTextEncode', {
    text_encoder: conn(textEncoderId),
    prompt: params.prompt || '',
    force_offload: true,
  }, 'Positive Prompt');

  const negativeId = nextNodeId();
  workflow[negativeId] = createNode('WanVideoTextEncode', {
    text_encoder: conn(textEncoderId),
    prompt: params.negativePrompt || '',
    force_offload: true,
  }, 'Negative Prompt');

  // 11. Encode reference image to embeddings
  const imageEncoderId = nextNodeId();
  workflow[imageEncoderId] = createNode('WanVideoImageToVideoEncode', {
    vae: conn(vaeLoaderId),
    clip_vision: conn(clipVisionId),
    start_image: conn(resizeId),
    width: params.width,
    height: params.height,
    num_frames: params.frameCount,
    noise_aug_strength: 0,
    start_latent_strength: 1.0,
    end_latent_strength: 1.0,
    force_offload: true,
  }, 'Encode Reference Image');

  // 12. Sample with WanVideoSampler (uni3c_embeds is SEPARATE input!)
  const samplerId = nextNodeId();
  workflow[samplerId] = createNode('WanVideoSampler', {
    model: conn(modelLoaderId),
    positive: conn(positiveId),
    negative: conn(negativeId),
    image_embeds: conn(imageEncoderId),
    uni3c_embeds: conn(uni3cEmbedsId), // ✅ SEPARATE INPUT for Uni3C
    steps: params.steps || 30,
    cfg: params.cfgScale || 5,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    scheduler: 'DPM++ 2M SDE',
    denoise: params.denoise || 1,
  }, 'Uni3C Sampler');

  // 13. Decode
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('WanVideoDecode', {
    vae: conn(vaeLoaderId),
    samples: conn(samplerId),
    enable_vae_tiling: true,
    tile_sample_min_height: 240,
    tile_sample_min_width: 240,
  }, 'VAE Decode');

  // 14. Output
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
 * Generate a Time-to-Move (TTM) workflow for Wan video generation.
 *
 * IMPORTANT: TTM is NOT trajectory-based motion control. It's a frame-to-frame
 * motion transfer system:
 * - User provides START frame + SUBJECT MASK
 * - User provides END frame (where subject should end up)
 * - The model infers the motion path automatically
 *
 * This workflow uses the REAL Kijai node: WanVideoAddTTMLatents
 * NOT fictional nodes like TTM_TrajectoryFromPoints.
 *
 * Required inputs:
 * - Start frame (reference image)
 * - Mask sequence (per-frame subject segmentation)
 * - Reference latents (VAE-encoded reference frames)
 *
 * Reference: https://time-to-move.github.io/
 * Implementation: Kijai's ComfyUI-WanVideoWrapper
 */
export function generateTTMWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  resetNodeIds();
  const workflow: ComfyUIWorkflow = {};

  // TTM only works with Wan models - other models not supported by WanVideoAddTTMLatents
  if (params.ttmModel && params.ttmModel !== 'wan') {
    console.warn(
      '[TTM Workflow] TTM is only supported for Wan models. ' +
      'CogVideoX and SVD do not have TTM support in Kijai\'s wrapper.'
    );
  }

  // 1. Load Wan model
  const wanLoaderId = nextNodeId();
  workflow[wanLoaderId] = createNode('WanVideoModelLoader', {
    model: 'wan2.1_i2v_480p_bf16.safetensors',
    base_precision: 'bf16',
    quantization: 'disabled',
  }, 'Load Wan Model');

  // 2. Load VAE
  const vaeLoaderId = nextNodeId();
  workflow[vaeLoaderId] = createNode('WanVideoVAELoader', {
    vae: 'wan_2.1_vae.safetensors',
    precision: 'bf16',
  }, 'Load Wan VAE');

  // 3. Load CLIP Vision for image encoding
  const clipVisionId = nextNodeId();
  workflow[clipVisionId] = createNode('CLIPVisionLoader', {
    clip_name: 'sigclip_vision_patch14_384.safetensors',
  }, 'Load CLIP Vision');

  // 4. Load Text Encoder
  const textEncoderId = nextNodeId();
  workflow[textEncoderId] = createNode('LoadWanVideoT5TextEncoder', {
    text_encoder: 'umt5-xxl-enc-bf16.safetensors',
    precision: 'bf16',
  }, 'Load Text Encoder');

  // 5. Load start frame (reference image)
  const startFrameId = addLoadImage(workflow, params.referenceImage || 'start_frame.png', 'Start Frame');
  const resizedStartId = addImageResize(workflow, conn(startFrameId), params.width, params.height);

  // 5b. Load end frame (target destination - TTM infers motion between start and end)
  const endFrameId = addLoadImage(workflow, params.ttmEndFrame || 'end_frame.png', 'End Frame');
  const resizedEndId = addImageResize(workflow, conn(endFrameId), params.width, params.height);

  // 6. Load mask sequence (PNG sequence from SAM3 segmentation)
  const maskLoadId = nextNodeId();
  workflow[maskLoadId] = createNode('VHS_LoadImages', {
    directory: params.ttmMaskDirectory || 'masks',
    image_load_cap: params.frameCount,
    skip_first_images: 0,
    select_every_nth: 1,
  }, 'Load Mask Sequence');

  // 7. Convert mask video to mask format (extracts red channel per Kijai's implementation)
  const maskConvertId = nextNodeId();
  workflow[maskConvertId] = createNode('ImageToMask', {
    image: conn(maskLoadId),
    channel: 'red',
  }, 'Convert to Mask');

  // 7b. ⚠️ CRITICAL: Load MOTION SIGNAL VIDEO for reference_latents
  // This is what TTM learns the motion FROM - NOT the start frame!
  const motionVideoLoadId = nextNodeId();
  if (params.ttmMotionVideoDirectory) {
    // Load from image sequence
    workflow[motionVideoLoadId] = createNode('VHS_LoadImages', {
      directory: params.ttmMotionVideoDirectory,
      image_load_cap: params.frameCount,
      skip_first_images: 0,
      select_every_nth: 1,
    }, 'Load Motion Signal Video');
  } else {
    // Load from video file
    workflow[motionVideoLoadId] = createNode('VHS_LoadVideo', {
      video: params.ttmMotionVideo || 'motion_signal.mp4',
      force_rate: params.fps || 16,
      force_size: 'Disabled',
      frame_load_cap: params.frameCount,
      skip_first_frames: 0,
      select_every_nth: 1,
    }, 'Load Motion Signal Video');
  }

  // 8. Encode prompt
  const positiveId = nextNodeId();
  workflow[positiveId] = createNode('WanVideoTextEncode', {
    text_encoder: conn(textEncoderId),
    prompt: params.prompt || '',
    force_offload: true,
  }, 'Positive Prompt');

  const negativeId = nextNodeId();
  workflow[negativeId] = createNode('WanVideoTextEncode', {
    text_encoder: conn(textEncoderId),
    prompt: params.negativePrompt || '',
    force_offload: true,
  }, 'Negative Prompt');

  // 9. Encode start image to embeddings (WanVideoImageToVideoEncode)
  // FIXED: Now includes end_image connection for TTM motion transfer
  const imageEncoderId = nextNodeId();
  workflow[imageEncoderId] = createNode('WanVideoImageToVideoEncode', {
    vae: conn(vaeLoaderId),
    clip_vision: conn(clipVisionId),
    start_image: conn(resizedStartId),
    end_image: conn(resizedEndId), // TTM: end frame shows where subject should move to
    width: params.width,
    height: params.height,
    length: params.frameCount,
    noise_aug_strength: 0,
    start_latent_strength: 1.0,
    end_latent_strength: 1.0,
    force_offload: true,
    fun_or_fl2v_model: true, // Required when using both start and end images
  }, 'Encode Start + End Images');

  // 10. ⚠️ CRITICAL FIX: Encode MOTION VIDEO to latents (not start frame!)
  // TTM learns motion from this video - the reference_latents must be the motion signal
  // Shape: [C, T, H//8, W//8] - VAE encoded video frames
  const referenceLatentsId = nextNodeId();
  workflow[referenceLatentsId] = createNode('WanVideoEncode', {
    vae: conn(vaeLoaderId),
    image: conn(motionVideoLoadId), // ✅ FIXED: Use motion video, NOT start frame
  }, 'Encode Motion Video to Latents');

  // 11. Apply TTM (THE REAL NODE - WanVideoAddTTMLatents)
  // Adds to embeds dict: ttm_reference_latents, ttm_mask, ttm_start_step, ttm_end_step
  const ttmId = nextNodeId();
  workflow[ttmId] = createNode('WanVideoAddTTMLatents', {
    embeds: conn(imageEncoderId),
    reference_latents: conn(referenceLatentsId),
    mask: conn(maskConvertId),
    start_step: params.ttmStartStep ?? 0,  // Default: start at step 0 (per Kijai default)
    end_step: params.ttmEndStep ?? 1,      // Default: end at step 1 (per Kijai default)
  }, 'Apply TTM Motion Transfer');

  // 12. Sample with WanVideoSampler
  const samplerId = nextNodeId();
  workflow[samplerId] = createNode('WanVideoSampler', {
    model: conn(wanLoaderId),
    positive: conn(positiveId),
    negative: conn(negativeId),
    image_embeds: conn(ttmId),
    steps: params.steps || 30,
    cfg: params.cfgScale || 5,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    scheduler: 'DPM++ 2M SDE',
    denoise: params.denoise || 1,
  }, 'TTM Sampler');

  // 13. Decode
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('WanVideoDecode', {
    vae: conn(vaeLoaderId),
    samples: conn(samplerId),
    enable_vae_tiling: true,
    tile_sample_min_height: 240,
    tile_sample_min_width: 240,
    tile_overlap_factor_height: 0.2,
    tile_overlap_factor_width: 0.2,
  }, 'VAE Decode');

  // 14. Output
  addVideoOutput(workflow, conn(decodeId), {
    fps: params.fps,
    filename: params.outputFilename || 'ttm_output',
  });

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
// Wan-Move Workflow (Point Trajectories)
// Uses WanVideoAddWanMoveTracks node with JSON track_coords
// ============================================================================

export function generateWanMoveWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  const workflow: ComfyUIWorkflow = {};
  let nodeIdCounter = 1;
  const nextNodeId = () => String(nodeIdCounter++);

  const createNode = (classType: string, inputs: Record<string, any>, title: string): ComfyUINode => ({
    class_type: classType,
    inputs,
    _meta: { title },
  });

  const conn = (nodeId: string, outputIndex = 0): NodeConnection => [nodeId, outputIndex];

  // 1. Load model (Wan21-WanMove dedicated model, NOT a LoRA)
  const modelLoaderId = nextNodeId();
  workflow[modelLoaderId] = createNode('WanVideoModelLoader', {
    model: params.model || 'Wan21-WanMove_fp8_scaled_e4m3fn_KJ.safetensors',
    base_precision: 'fp8_e4m3fn',
    quantization: 'disabled',
    load_device: 'main_device',
    attention_mode: 'sdpa',
  }, 'Load WanMove Model');

  // 2. Load VAE
  const vaeLoaderId = nextNodeId();
  workflow[vaeLoaderId] = createNode('WanVideoVAELoader', {
    vae: params.vae || 'Wan21_VAE.safetensors',
    precision: 'bf16',
  }, 'Load VAE');

  // 3. Load CLIP Vision
  const clipVisionId = nextNodeId();
  workflow[clipVisionId] = createNode('CLIPVisionLoader', {
    clip_name: params.clipVision || 'sigclip_vision_patch14_384.safetensors',
  }, 'Load CLIP Vision');

  // 4. Load Text Encoders
  const textEncoderId = nextNodeId();
  workflow[textEncoderId] = createNode('DualCLIPLoader', {
    clip_name1: 'umt5_xxl_encoder_q4_K_M.gguf',
    clip_name2: 'clip_l.safetensors',
    type: 'wan',
  }, 'Load Text Encoders');

  // 5. Text encoding
  const positiveTextId = nextNodeId();
  workflow[positiveTextId] = createNode('WanVideoTextEncode', {
    clip: conn(textEncoderId),
    prompt: params.prompt || '',
    force_offload: true,
  }, 'Positive Prompt');

  const negativeTextId = nextNodeId();
  workflow[negativeTextId] = createNode('WanVideoTextEncode', {
    clip: conn(textEncoderId),
    prompt: params.negativePrompt || '',
    force_offload: true,
  }, 'Negative Prompt');

  // 6. Load reference image
  const loadImageId = nextNodeId();
  workflow[loadImageId] = createNode('LoadImage', {
    image: params.referenceImage || 'reference.png',
  }, 'Load Reference Image');

  // 7. Resize image to target dimensions
  const resizeId = nextNodeId();
  workflow[resizeId] = createNode('ImageResize', {
    image: conn(loadImageId),
    width: params.width || 832,
    height: params.height || 480,
    interpolation: 'lanczos',
  }, 'Resize Reference');

  // 8. Encode image to embeddings
  const imageEncoderId = nextNodeId();
  workflow[imageEncoderId] = createNode('WanVideoImageToVideoEncode', {
    vae: conn(vaeLoaderId),
    clip_vision: conn(clipVisionId),
    start_image: conn(resizeId),
    width: params.width || 832,
    height: params.height || 480,
    num_frames: params.frameCount || 81,
    noise_aug_strength: 0,
    start_latent_strength: 1.0,
    end_latent_strength: 1.0,
    force_offload: true,
  }, 'Encode Reference Image');

  // 9. Add WanMove Tracks (THE CORE NODE)
  // track_coords should be JSON string: [{"x": 100, "y": 200}, {"x": 150, "y": 250}, ...]
  const wanMoveTracksId = nextNodeId();
  workflow[wanMoveTracksId] = createNode('WanVideoAddWanMoveTracks', {
    image_embeds: conn(imageEncoderId),
    strength: params.wanMoveStrength ?? 1.0,
    track_coords: params.trackCoords || '[]', // JSON string from FL_PathAnimator or compositor
  }, 'Add WanMove Tracks');

  // 10. Sample
  const samplerId = nextNodeId();
  workflow[samplerId] = createNode('WanVideoSampler', {
    model: conn(modelLoaderId),
    positive: conn(positiveTextId),
    negative: conn(negativeTextId),
    image_embeds: conn(wanMoveTracksId),
    steps: params.steps || 30,
    cfg: params.cfgScale || 5.0,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    shift: 8.0,
    force_offload: true,
  }, 'Sample');

  // 11. Decode
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('WanVideoDecode', {
    samples: conn(samplerId),
    vae: conn(vaeLoaderId),
    enable_vae_tiling: true,
  }, 'Decode');

  // 12. Save output
  const saveId = nextNodeId();
  workflow[saveId] = createNode('VHS_VideoCombine', {
    images: conn(decodeId),
    frame_rate: params.fps || 16,
    format: 'video/h264-mp4',
    filename_prefix: params.outputFilename || 'wanmove_output',
  }, 'Save Video');

  return workflow;
}

// ============================================================================
// ATI (Any Trajectory Instruction) Workflow
// Uses WanVideoATITracks to patch model with trajectory control
// ============================================================================

export function generateATIWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  const workflow: ComfyUIWorkflow = {};
  let nodeIdCounter = 1;
  const nextNodeId = () => String(nodeIdCounter++);

  const createNode = (classType: string, inputs: Record<string, any>, title: string): ComfyUINode => ({
    class_type: classType,
    inputs,
    _meta: { title },
  });

  const conn = (nodeId: string, outputIndex = 0): NodeConnection => [nodeId, outputIndex];

  // 1. Load model
  const modelLoaderId = nextNodeId();
  workflow[modelLoaderId] = createNode('WanVideoModelLoader', {
    model: params.model || 'Wan21-14B-ATI_fp8_scaled_e4m3fn_KJ.safetensors',
    base_precision: 'fp8_e4m3fn',
    quantization: 'disabled',
    load_device: 'main_device',
    attention_mode: 'sdpa',
  }, 'Load ATI Model');

  // 2. Load VAE
  const vaeLoaderId = nextNodeId();
  workflow[vaeLoaderId] = createNode('WanVideoVAELoader', {
    vae: params.vae || 'Wan21_VAE.safetensors',
    precision: 'bf16',
  }, 'Load VAE');

  // 3. Load CLIP Vision
  const clipVisionId = nextNodeId();
  workflow[clipVisionId] = createNode('CLIPVisionLoader', {
    clip_name: params.clipVision || 'sigclip_vision_patch14_384.safetensors',
  }, 'Load CLIP Vision');

  // 4. Load Text Encoders
  const textEncoderId = nextNodeId();
  workflow[textEncoderId] = createNode('DualCLIPLoader', {
    clip_name1: 'umt5_xxl_encoder_q4_K_M.gguf',
    clip_name2: 'clip_l.safetensors',
    type: 'wan',
  }, 'Load Text Encoders');

  // 5. Apply ATI Tracks to Model (THE CORE NODE)
  // tracks should be JSON string: [[{"x": 100, "y": 200}, ...], ...]
  const atiTracksId = nextNodeId();
  workflow[atiTracksId] = createNode('WanVideoATITracks', {
    model: conn(modelLoaderId),
    tracks: params.trackCoords || '[]',
    width: params.width || 832,
    height: params.height || 480,
    temperature: params.atiTemperature ?? 220.0,
    topk: params.atiTopk ?? 2,
    start_percent: params.atiStartPercent ?? 0.0,
    end_percent: params.atiEndPercent ?? 1.0,
  }, 'Apply ATI Tracks');

  // 6. Text encoding
  const positiveTextId = nextNodeId();
  workflow[positiveTextId] = createNode('WanVideoTextEncode', {
    clip: conn(textEncoderId),
    prompt: params.prompt || '',
    force_offload: true,
  }, 'Positive Prompt');

  const negativeTextId = nextNodeId();
  workflow[negativeTextId] = createNode('WanVideoTextEncode', {
    clip: conn(textEncoderId),
    prompt: params.negativePrompt || '',
    force_offload: true,
  }, 'Negative Prompt');

  // 7. Load reference image
  const loadImageId = nextNodeId();
  workflow[loadImageId] = createNode('LoadImage', {
    image: params.referenceImage || 'reference.png',
  }, 'Load Reference Image');

  // 8. Resize image
  const resizeId = nextNodeId();
  workflow[resizeId] = createNode('ImageResize', {
    image: conn(loadImageId),
    width: params.width || 832,
    height: params.height || 480,
    interpolation: 'lanczos',
  }, 'Resize Reference');

  // 9. Encode image
  const imageEncoderId = nextNodeId();
  workflow[imageEncoderId] = createNode('WanVideoImageToVideoEncode', {
    vae: conn(vaeLoaderId),
    clip_vision: conn(clipVisionId),
    start_image: conn(resizeId),
    width: params.width || 832,
    height: params.height || 480,
    num_frames: params.frameCount || 81,
    noise_aug_strength: 0,
    start_latent_strength: 1.0,
    end_latent_strength: 1.0,
    force_offload: true,
  }, 'Encode Reference Image');

  // 10. Sample (using ATI-patched model)
  const samplerId = nextNodeId();
  workflow[samplerId] = createNode('WanVideoSampler', {
    model: conn(atiTracksId), // Note: patched model from ATI node
    positive: conn(positiveTextId),
    negative: conn(negativeTextId),
    image_embeds: conn(imageEncoderId),
    steps: params.steps || 30,
    cfg: params.cfgScale || 5.0,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    shift: 8.0,
    force_offload: true,
  }, 'Sample');

  // 11. Decode
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('WanVideoDecode', {
    samples: conn(samplerId),
    vae: conn(vaeLoaderId),
    enable_vae_tiling: true,
  }, 'Decode');

  // 12. Save output
  const saveId = nextNodeId();
  workflow[saveId] = createNode('VHS_VideoCombine', {
    images: conn(decodeId),
    frame_rate: params.fps || 16,
    format: 'video/h264-mp4',
    filename_prefix: params.outputFilename || 'ati_output',
  }, 'Save Video');

  return workflow;
}

// ============================================================================
// Light-X Workflow (Relighting via LoRA)
// Light-X is a LoRA, not separate nodes - loaded via WanVideoLoraSelect
// ============================================================================

export function generateLightXWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  const workflow: ComfyUIWorkflow = {};
  let nodeIdCounter = 1;
  const nextNodeId = () => String(nodeIdCounter++);

  const createNode = (classType: string, inputs: Record<string, any>, title: string): ComfyUINode => ({
    class_type: classType,
    inputs,
    _meta: { title },
  });

  const conn = (nodeId: string, outputIndex = 0): NodeConnection => [nodeId, outputIndex];

  // 1. Select Light-X LoRA (THE CORE NODE - Light-X is a LoRA, not separate nodes)
  const loraSelectId = nextNodeId();
  workflow[loraSelectId] = createNode('WanVideoLoraSelect', {
    lora: params.lightXLora || 'WAN/lightx2v_I2V_14B_480p_cfg_step_distill_rank64_bf16.safetensors',
    strength: params.loraStrength ?? 1.0,
    merge_loras: true,
  }, 'Select Light-X LoRA');

  // 2. Load model with LoRA applied
  const modelLoaderId = nextNodeId();
  workflow[modelLoaderId] = createNode('WanVideoModelLoader', {
    model: params.model || 'Wan2_2-I2V-A14B-480P_fp8_e4m3fn_scaled_KJ.safetensors',
    base_precision: 'fp8_e4m3fn',
    quantization: 'disabled',
    load_device: 'main_device',
    attention_mode: 'sdpa',
    lora: conn(loraSelectId), // Connect LoRA
  }, 'Load Model with Light-X');

  // 3. Load VAE
  const vaeLoaderId = nextNodeId();
  workflow[vaeLoaderId] = createNode('WanVideoVAELoader', {
    vae: params.vae || 'Wan21_VAE.safetensors',
    precision: 'bf16',
  }, 'Load VAE');

  // 4. Load CLIP Vision
  const clipVisionId = nextNodeId();
  workflow[clipVisionId] = createNode('CLIPVisionLoader', {
    clip_name: params.clipVision || 'sigclip_vision_patch14_384.safetensors',
  }, 'Load CLIP Vision');

  // 5. Load Text Encoders
  const textEncoderId = nextNodeId();
  workflow[textEncoderId] = createNode('DualCLIPLoader', {
    clip_name1: 'umt5_xxl_encoder_q4_K_M.gguf',
    clip_name2: 'clip_l.safetensors',
    type: 'wan',
  }, 'Load Text Encoders');

  // 6. Text encoding
  const positiveTextId = nextNodeId();
  workflow[positiveTextId] = createNode('WanVideoTextEncode', {
    clip: conn(textEncoderId),
    prompt: params.prompt || '',
    force_offload: true,
  }, 'Positive Prompt');

  const negativeTextId = nextNodeId();
  workflow[negativeTextId] = createNode('WanVideoTextEncode', {
    clip: conn(textEncoderId),
    prompt: params.negativePrompt || '',
    force_offload: true,
  }, 'Negative Prompt');

  // 7. Load reference image
  const loadImageId = nextNodeId();
  workflow[loadImageId] = createNode('LoadImage', {
    image: params.referenceImage || 'reference.png',
  }, 'Load Reference Image');

  // 8. Resize image
  const resizeId = nextNodeId();
  workflow[resizeId] = createNode('ImageResize', {
    image: conn(loadImageId),
    width: params.width || 832,
    height: params.height || 480,
    interpolation: 'lanczos',
  }, 'Resize Reference');

  // 9. Encode image
  const imageEncoderId = nextNodeId();
  workflow[imageEncoderId] = createNode('WanVideoImageToVideoEncode', {
    vae: conn(vaeLoaderId),
    clip_vision: conn(clipVisionId),
    start_image: conn(resizeId),
    width: params.width || 832,
    height: params.height || 480,
    num_frames: params.frameCount || 81,
    noise_aug_strength: 0,
    start_latent_strength: 1.0,
    end_latent_strength: 1.0,
    force_offload: true,
  }, 'Encode Reference Image');

  // 10. Sample
  const samplerId = nextNodeId();
  workflow[samplerId] = createNode('WanVideoSampler', {
    model: conn(modelLoaderId),
    positive: conn(positiveTextId),
    negative: conn(negativeTextId),
    image_embeds: conn(imageEncoderId),
    steps: params.steps || 30,
    cfg: params.cfgScale || 5.0,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    shift: 8.0,
    force_offload: true,
  }, 'Sample');

  // 11. Decode
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('WanVideoDecode', {
    samples: conn(samplerId),
    vae: conn(vaeLoaderId),
    enable_vae_tiling: true,
  }, 'Decode');

  // 12. Save output
  const saveId = nextNodeId();
  workflow[saveId] = createNode('VHS_VideoCombine', {
    images: conn(decodeId),
    frame_rate: params.fps || 16,
    format: 'video/h264-mp4',
    filename_prefix: params.outputFilename || 'lightx_output',
  }, 'Save Video');

  return workflow;
}

// ============================================================================
// SCAIL Workflow (Pose + Reference Control)
// Uses WanVideoAddSCAILReferenceEmbeds + WanVideoAddSCAILPoseEmbeds
// Both add to scail_embeds dict within WANVIDIMAGE_EMBEDS
// ============================================================================

export function generateSCAILWorkflow(params: WorkflowParams): ComfyUIWorkflow {
  const workflow: ComfyUIWorkflow = {};
  let nodeIdCounter = 1;
  const nextNodeId = () => String(nodeIdCounter++);

  const createNode = (classType: string, inputs: Record<string, any>, title: string): ComfyUINode => ({
    class_type: classType,
    inputs,
    _meta: { title },
  });

  const conn = (nodeId: string, outputIndex = 0): NodeConnection => [nodeId, outputIndex];

  // 1. Load SCAIL model (dedicated model with pose control patched in)
  const modelLoaderId = nextNodeId();
  workflow[modelLoaderId] = createNode('WanVideoModelLoader', {
    model: params.model || 'Wan21-14B-SCAIL-preview_fp8_e4m3fn_scaled_KJ.safetensors',
    base_precision: 'fp8_e4m3fn',
    quantization: 'disabled',
    load_device: 'main_device',
    attention_mode: 'sdpa',
  }, 'Load SCAIL Model');

  // 2. Load VAE
  const vaeLoaderId = nextNodeId();
  workflow[vaeLoaderId] = createNode('WanVideoVAELoader', {
    vae: params.vae || 'Wan21_VAE.safetensors',
    precision: 'bf16',
  }, 'Load VAE');

  // 3. Load CLIP Vision (for clip_embeds)
  const clipVisionLoaderId = nextNodeId();
  workflow[clipVisionLoaderId] = createNode('CLIPVisionLoader', {
    clip_name: params.clipVision || 'sigclip_vision_patch14_384.safetensors',
  }, 'Load CLIP Vision');

  // 4. Load Text Encoders
  const textEncoderId = nextNodeId();
  workflow[textEncoderId] = createNode('DualCLIPLoader', {
    clip_name1: 'umt5_xxl_encoder_q4_K_M.gguf',
    clip_name2: 'clip_l.safetensors',
    type: 'wan',
  }, 'Load Text Encoders');

  // 5. Text encoding
  const positiveTextId = nextNodeId();
  workflow[positiveTextId] = createNode('WanVideoTextEncode', {
    clip: conn(textEncoderId),
    prompt: params.prompt || '',
    force_offload: true,
  }, 'Positive Prompt');

  const negativeTextId = nextNodeId();
  workflow[negativeTextId] = createNode('WanVideoTextEncode', {
    clip: conn(textEncoderId),
    prompt: params.negativePrompt || '',
    force_offload: true,
  }, 'Negative Prompt');

  // 6. Load reference image for start frame
  const loadImageId = nextNodeId();
  workflow[loadImageId] = createNode('LoadImage', {
    image: params.referenceImage || 'reference.png',
  }, 'Load Reference Image');

  // 7. Resize reference image
  const resizeId = nextNodeId();
  workflow[resizeId] = createNode('ImageResize', {
    image: conn(loadImageId),
    width: params.width || 832,
    height: params.height || 480,
    interpolation: 'lanczos',
  }, 'Resize Reference');

  // 8. Encode reference image to embeddings (base WANVIDIMAGE_EMBEDS)
  const imageEncoderId = nextNodeId();
  workflow[imageEncoderId] = createNode('WanVideoImageToVideoEncode', {
    vae: conn(vaeLoaderId),
    clip_vision: conn(clipVisionLoaderId),
    start_image: conn(resizeId),
    width: params.width || 832,
    height: params.height || 480,
    num_frames: params.frameCount || 81,
    noise_aug_strength: 0,
    start_latent_strength: 1.0,
    end_latent_strength: 1.0,
    force_offload: true,
  }, 'Encode Reference Image');

  // 9. Encode CLIP vision for reference image (for clip_embeds input to SCAIL)
  const clipEncodeId = nextNodeId();
  workflow[clipEncodeId] = createNode('WanVideoClipVisionEncode', {
    clip_vision: conn(clipVisionLoaderId),
    image: conn(resizeId),
  }, 'Encode CLIP Vision');

  // 10. Load SCAIL reference image (can be same or different from start frame)
  const scailRefImageId = nextNodeId();
  workflow[scailRefImageId] = createNode('LoadImage', {
    image: params.scailReferenceImage || params.referenceImage || 'reference.png',
  }, 'Load SCAIL Reference Image');

  const scailRefResizeId = nextNodeId();
  workflow[scailRefResizeId] = createNode('ImageResize', {
    image: conn(scailRefImageId),
    width: params.width || 832,
    height: params.height || 480,
    interpolation: 'lanczos',
  }, 'Resize SCAIL Reference');

  // 11. Add SCAIL Reference Embeds (first part of scail_embeds)
  // Adds: ref_latent_pos, ref_latent_neg, ref_start_percent, ref_end_percent, clip_context
  const scailRefEmbedsId = nextNodeId();
  workflow[scailRefEmbedsId] = createNode('WanVideoAddSCAILReferenceEmbeds', {
    embeds: conn(imageEncoderId),
    vae: conn(vaeLoaderId),
    ref_image: conn(scailRefResizeId),
    strength: params.scailRefStrength ?? 1.0,
    start_percent: params.scailRefStartPercent ?? 0.0,
    end_percent: params.scailRefEndPercent ?? 1.0,
    clip_embeds: conn(clipEncodeId),
  }, 'Add SCAIL Reference Embeds');

  // 12. Load pose video for SCAIL pose control
  const poseVideoId = nextNodeId();
  if (params.scailPoseDirectory) {
    // Load from image sequence
    workflow[poseVideoId] = createNode('VHS_LoadImages', {
      directory: params.scailPoseDirectory,
      image_load_cap: params.frameCount,
      skip_first_images: 0,
      select_every_nth: 1,
    }, 'Load Pose Sequence');
  } else {
    // Load from video file
    workflow[poseVideoId] = createNode('VHS_LoadVideo', {
      video: params.scailPoseVideo || 'pose_video.mp4',
      force_rate: params.fps || 16,
      force_size: 'Disabled',
      frame_load_cap: params.frameCount,
      skip_first_frames: 0,
      select_every_nth: 1,
    }, 'Load Pose Video');
  }

  // 13. Add SCAIL Pose Embeds (second part of scail_embeds)
  // Adds: pose_latent, pose_strength, pose_start_percent, pose_end_percent
  const scailPoseEmbedsId = nextNodeId();
  workflow[scailPoseEmbedsId] = createNode('WanVideoAddSCAILPoseEmbeds', {
    embeds: conn(scailRefEmbedsId), // Chain from reference embeds
    vae: conn(vaeLoaderId),
    pose_images: conn(poseVideoId),
    strength: params.scailPoseStrength ?? 1.0,
    start_percent: params.scailPoseStartPercent ?? 0.0,
    end_percent: params.scailPoseEndPercent ?? 1.0,
  }, 'Add SCAIL Pose Embeds');

  // 14. Sample
  const samplerId = nextNodeId();
  workflow[samplerId] = createNode('WanVideoSampler', {
    model: conn(modelLoaderId),
    positive: conn(positiveTextId),
    negative: conn(negativeTextId),
    image_embeds: conn(scailPoseEmbedsId), // Final embeds with both ref + pose
    steps: params.steps || 30,
    cfg: params.cfgScale || 5.0,
    seed: params.seed ?? Math.floor(Math.random() * 2147483647),
    shift: 8.0,
    force_offload: true,
  }, 'Sample');

  // 15. Decode
  const decodeId = nextNodeId();
  workflow[decodeId] = createNode('WanVideoDecode', {
    samples: conn(samplerId),
    vae: conn(vaeLoaderId),
    enable_vae_tiling: true,
  }, 'Decode');

  // 16. Save output
  const saveId = nextNodeId();
  workflow[saveId] = createNode('VHS_VideoCombine', {
    images: conn(decodeId),
    frame_rate: params.fps || 16,
    format: 'video/h264-mp4',
    filename_prefix: params.outputFilename || 'scail_output',
  }, 'Save Video');

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

    case 'wan-move':
      // Wan-Move point trajectory workflow
      return generateWanMoveWorkflow(params);

    case 'ati':
      // ATI (Any Trajectory Instruction) workflow
      return generateATIWorkflow(params);

    case 'light-x':
      // Light-X relighting via LoRA
      return generateLightXWorkflow(params);

    case 'scail':
      // SCAIL pose + reference control (dual structure)
      return generateSCAILWorkflow(params);

    case 'camera-comfyui':
      // camera-comfyUI 4x4 matrices - uses standard Wan I2V with camera data
      // Camera matrices are exported separately, not embedded in workflow
      return generateWan22I2VWorkflow(params);

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
