/**
 * Preprocessor Service
 *
 * Frontend service for calling ControlNet-style preprocessors via the Python backend.
 *
 * ============================================================================
 *                         OPEN SOURCE ATTRIBUTION
 * ============================================================================
 *
 * This service wraps nodes from the following open-source projects:
 *
 * 1. comfyui_controlnet_aux - ControlNet Auxiliary Preprocessors
 *    Repository: https://github.com/Fannovel16/comfyui_controlnet_aux
 *    Author: Fannovel16 and contributors
 *    License: Apache 2.0
 *
 * 2. NormalCrafter - Video-to-Normal Diffusion Model
 *    Repository: https://github.com/Binyr/NormalCrafter
 *    Wrapper: https://github.com/AIWarper/ComfyUI-NormalCrafterWrapper
 *    Authors: Binyr, AIWarper
 *
 * 3. ComfyUI-WanAnimatePreprocess - Video Animation Preprocessing
 *    Repository: https://github.com/kijai/ComfyUI-WanAnimatePreprocess
 *    Author: Kijai (Jukka Seppänen)
 *
 * We gratefully acknowledge all contributors who make these tools available.
 * ============================================================================
 */

import { useProjectStore } from "@/stores/projectStore";

export interface PreprocessorInfo {
  id: string;
  display_name: string;
  description: string;
  category: string;
  inputs: Record<string, PreprocessorInput>;
  source?: string; // Attribution source
  is_video?: boolean; // For video-specific preprocessors
}

export interface PreprocessorInput {
  type: "combo" | "int" | "float" | "bool" | "string";
  default: string | number | boolean;
  min?: number;
  max?: number;
  step?: number;
  options?: string[];
}

export interface PreprocessorResult {
  success: boolean;
  result_image?: string; // Base64 encoded
  error?: string;
  execution_time?: number;
}

export type PreprocessorCategory =
  | "depth"
  | "normal"
  | "pose"
  | "edge"
  | "lineart"
  | "scribble"
  | "segmentation"
  | "video"
  | "other";

// Map generationType to preprocessor categories
const TYPE_TO_CATEGORY: Record<string, PreprocessorCategory[]> = {
  depth: ["depth"],
  normal: ["normal"],
  edge: ["edge", "lineart", "scribble"],
  segment: ["segmentation"],
  pose: ["pose", "video"], // Include video pose preprocessors
  video: ["video", "normal"], // Video includes NormalCrafter
  custom: [
    "depth",
    "normal",
    "pose",
    "edge",
    "lineart",
    "scribble",
    "segmentation",
    "video",
    "other",
  ],
};

// Default preprocessors for each generation type
const DEFAULT_PREPROCESSORS: Record<string, string> = {
  depth: "depth_anything_v2",
  normal: "normal_bae",
  edge: "canny",
  segment: "oneformer_ade20k",
  pose: "dwpose",
  video: "normalcrafter",
  custom: "depth_anything_v2",
};

// Attribution sources
export const ATTRIBUTION_SOURCES = {
  controlnet_aux: {
    name: "comfyui_controlnet_aux",
    repo: "https://github.com/Fannovel16/comfyui_controlnet_aux",
    author: "Fannovel16",
    license: "Apache 2.0",
  },
  normalcrafter: {
    name: "NormalCrafter / ComfyUI-NormalCrafterWrapper",
    repo: "https://github.com/Binyr/NormalCrafter | https://github.com/AIWarper/ComfyUI-NormalCrafterWrapper",
    author: "Binyr, AIWarper",
    license: "Research / MIT",
  },
  wan_animate: {
    name: "ComfyUI-WanAnimatePreprocess",
    repo: "https://github.com/kijai/ComfyUI-WanAnimatePreprocess",
    author: "Kijai",
    license: "MIT",
  },
};

// All available preprocessors with their metadata (mirrors Python backend)
export const PREPROCESSOR_REGISTRY: Record<string, PreprocessorInfo> = {
  //                                                                    // depth
  depth_anything_v2: {
    id: "depth_anything_v2",
    display_name: "Depth Anything V2",
    description: "State-of-the-art monocular depth estimation",
    category: "depth",
    inputs: {
      ckpt_name: {
        type: "combo",
        options: [
          "depth_anything_v2_vitl.pth",
          "depth_anything_v2_vitb.pth",
          "depth_anything_v2_vits.pth",
        ],
        default: "depth_anything_v2_vitl.pth",
      },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  midas: {
    id: "midas",
    display_name: "MiDaS Depth",
    description: "MiDaS depth estimation with multiple model options",
    category: "depth",
    inputs: {
      a: { type: "float", default: 6.28, min: 0, max: 20 },
      bg_threshold: { type: "float", default: 0.1, min: 0, max: 1, step: 0.01 },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  zoe_depth: {
    id: "zoe_depth",
    display_name: "ZoeDepth",
    description: "Zero-shot depth estimation",
    category: "depth",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  leres: {
    id: "leres",
    display_name: "LeReS Depth",
    description: "Learning to Recover 3D Scene Shape from a Single Image",
    category: "depth",
    inputs: {
      rm_nearest: { type: "float", default: 0.0, min: 0, max: 1, step: 0.01 },
      rm_background: {
        type: "float",
        default: 0.0,
        min: 0,
        max: 1,
        step: 0.01,
      },
      boost: { type: "bool", default: false },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  marigold: {
    id: "marigold",
    display_name: "Marigold Depth",
    description: "Diffusion-based depth estimation",
    category: "depth",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  depth_fm: {
    id: "depth_fm",
    display_name: "DepthFM",
    description: "Fast Monocular Depth Estimation with Flow Matching",
    category: "depth",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },

  //                                                                   // normal
  normal_bae: {
    id: "normal_bae",
    display_name: "Normal BAE",
    description: "Boundary-Aware Normal estimation",
    category: "normal",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  normal_dsine: {
    id: "normal_dsine",
    display_name: "DSINE Normal",
    description: "Rethinking Inductive Biases for Surface Normal Estimation",
    category: "normal",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },

  //                                                                     // pose
  dwpose: {
    id: "dwpose",
    display_name: "DWPose",
    description: "Effective Whole-body Pose Estimation (best quality)",
    category: "pose",
    inputs: {
      detect_hand: { type: "bool", default: true },
      detect_body: { type: "bool", default: true },
      detect_face: { type: "bool", default: true },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  openpose: {
    id: "openpose",
    display_name: "OpenPose",
    description: "Classic pose estimation",
    category: "pose",
    inputs: {
      detect_hand: { type: "bool", default: false },
      detect_body: { type: "bool", default: true },
      detect_face: { type: "bool", default: false },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  animal_pose: {
    id: "animal_pose",
    display_name: "Animal Pose",
    description: "Pose estimation for animals",
    category: "pose",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  mediapipe_face: {
    id: "mediapipe_face",
    display_name: "MediaPipe Face",
    description: "Face mesh detection using MediaPipe",
    category: "pose",
    inputs: {
      max_faces: { type: "int", default: 10, min: 1, max: 20 },
      min_confidence: {
        type: "float",
        default: 0.5,
        min: 0,
        max: 1,
        step: 0.01,
      },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  densepose: {
    id: "densepose",
    display_name: "DensePose",
    description: "Dense human pose estimation",
    category: "pose",
    inputs: {
      cmap: {
        type: "combo",
        options: ["viridis", "parula"],
        default: "viridis",
      },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },

  //                                                        // edge // detection
  canny: {
    id: "canny",
    display_name: "Canny Edge",
    description: "Classic Canny edge detection",
    category: "edge",
    inputs: {
      low_threshold: { type: "int", default: 100, min: 0, max: 255 },
      high_threshold: { type: "int", default: 200, min: 0, max: 255 },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  hed: {
    id: "hed",
    display_name: "HED",
    description: "Holistically-Nested Edge Detection",
    category: "edge",
    inputs: {
      safe: { type: "bool", default: true },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  softedge_hed: {
    id: "softedge_hed",
    display_name: "Soft Edge HED",
    description: "Soft edge variant of HED",
    category: "edge",
    inputs: {
      safe: { type: "bool", default: true },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  pidinet: {
    id: "pidinet",
    display_name: "PidiNet",
    description: "Pixel Difference Networks for edge detection",
    category: "edge",
    inputs: {
      safe: { type: "bool", default: true },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  softedge_pidinet: {
    id: "softedge_pidinet",
    display_name: "Soft Edge PidiNet",
    description: "Soft edge variant of PidiNet",
    category: "edge",
    inputs: {
      safe: { type: "bool", default: true },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  teed: {
    id: "teed",
    display_name: "TEED",
    description: "Tiny and Efficient Edge Detector",
    category: "edge",
    inputs: {
      safe_steps: { type: "int", default: 2, min: 0, max: 10 },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },

  //                                                                  // lineart
  lineart: {
    id: "lineart",
    display_name: "LineArt",
    description: "Realistic lineart extraction",
    category: "lineart",
    inputs: {
      coarse: { type: "bool", default: false },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  lineart_coarse: {
    id: "lineart_coarse",
    display_name: "LineArt Coarse",
    description: "Coarse lineart extraction",
    category: "lineart",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  lineart_anime: {
    id: "lineart_anime",
    display_name: "LineArt Anime",
    description: "Anime-style lineart extraction",
    category: "lineart",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  lineart_manga: {
    id: "lineart_manga",
    display_name: "LineArt Manga",
    description: "Manga-style lineart extraction",
    category: "lineart",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  anime_face_segment: {
    id: "anime_face_segment",
    display_name: "Anime Face Segment",
    description: "Anime face segmentation",
    category: "lineart",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },

  //                                                                 // scribble
  scribble_hed: {
    id: "scribble_hed",
    display_name: "Scribble HED",
    description: "HED-based scribble extraction",
    category: "scribble",
    inputs: {
      safe: { type: "bool", default: true },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  scribble_pidinet: {
    id: "scribble_pidinet",
    display_name: "Scribble PidiNet",
    description: "PidiNet-based scribble extraction",
    category: "scribble",
    inputs: {
      safe: { type: "bool", default: true },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  scribble_xdog: {
    id: "scribble_xdog",
    display_name: "Scribble XDoG",
    description: "Extended Difference of Gaussians scribble",
    category: "scribble",
    inputs: {
      threshold: { type: "int", default: 32, min: 0, max: 255 },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  binary: {
    id: "binary",
    display_name: "Binary",
    description: "Binary threshold conversion",
    category: "scribble",
    inputs: {
      bin_threshold: { type: "int", default: 100, min: 0, max: 255 },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },

  //                                                             // segmentation
  sam: {
    id: "sam",
    display_name: "SAM",
    description: "Segment Anything Model",
    category: "segmentation",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  oneformer_ade20k: {
    id: "oneformer_ade20k",
    display_name: "OneFormer ADE20K",
    description: "OneFormer trained on ADE20K (150 classes)",
    category: "segmentation",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  oneformer_coco: {
    id: "oneformer_coco",
    display_name: "OneFormer COCO",
    description: "OneFormer trained on COCO (133 classes)",
    category: "segmentation",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  uniformer: {
    id: "uniformer",
    display_name: "UniFormer",
    description: "Unified segmentation model",
    category: "segmentation",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  color_shuffle: {
    id: "color_shuffle",
    display_name: "Color Shuffle",
    description: "Shuffle colors for data augmentation",
    category: "segmentation",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },

  //                                                                    // other
  mlsd: {
    id: "mlsd",
    display_name: "M-LSD",
    description: "Mobile Line Segment Detection",
    category: "other",
    inputs: {
      score_thr: { type: "float", default: 0.1, min: 0, max: 1, step: 0.01 },
      dist_thr: { type: "float", default: 0.1, min: 0, max: 1, step: 0.01 },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  tile: {
    id: "tile",
    display_name: "Tile",
    description: "Tile preprocessor for upscaling workflows",
    category: "other",
    inputs: {
      pyrUp_iters: { type: "int", default: 3, min: 0, max: 10 },
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },
  inpaint: {
    id: "inpaint",
    display_name: "Inpaint Preprocessor",
    description: "Prepare mask for inpainting",
    category: "other",
    source: "controlnet_aux",
    inputs: {
      resolution: { type: "int", default: 512, min: 64, max: 2048, step: 8 },
    },
  },

  // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  // NORMALCRAFTER (from Binyr/NormalCrafter + AIWarper/ComfyUI-NormalCrafterWrapper)
  // Video-to-Normal diffusion model - temporally consistent normal sequences
  // ═══════════════════════════════════════════════════════════════════════════
  normalcrafter: {
    id: "normalcrafter",
    display_name: "NormalCrafter (Video)",
    description:
      "Temporally consistent normal maps from video - ICCV 2025 (Binyr)",
    category: "normal",
    source: "normalcrafter",
    is_video: true,
    inputs: {
      seed: { type: "int", default: 42, min: 0, max: 2147483647 },
      max_res_dimension: { type: "int", default: 1024, min: 256, max: 2048 },
      window_size: { type: "int", default: 14, min: 1, max: 32 },
      time_step_size: { type: "int", default: 10, min: 1, max: 20 },
      decode_chunk_size: { type: "int", default: 4, min: 1, max: 16 },
      fps_for_time_ids: { type: "int", default: 7, min: 1, max: 60 },
      motion_bucket_id: { type: "int", default: 127, min: 0, max: 255 },
      noise_aug_strength: { type: "float", default: 0.0, min: 0.0, max: 1.0 },
    },
  },

  // ═══════════════════════════════════════════════════════════════════════════
  // VIDEO POSE (ComfyUI-WanAnimatePreprocess)
  // For Wan 2.2 video animation preprocessing
  // ═══════════════════════════════════════════════════════════════════════════
  vitpose: {
    id: "vitpose",
    display_name: "ViTPose + Face (Video)",
    description: "ViTPose detection with face for video animation",
    category: "video",
    source: "wan_animate",
    is_video: true,
    inputs: {
      width: { type: "int", default: 832, min: 64, max: 2048 },
      height: { type: "int", default: 480, min: 64, max: 2048 },
    },
  },
  vitpose_draw: {
    id: "vitpose_draw",
    display_name: "Draw ViTPose Skeleton",
    description: "Render ViTPose skeleton visualization",
    category: "video",
    source: "wan_animate",
    inputs: {
      width: { type: "int", default: 832, min: 64, max: 2048 },
      height: { type: "int", default: 480, min: 64, max: 2048 },
      retarget_padding: { type: "int", default: 16, min: 0, max: 512 },
      body_stick_width: { type: "int", default: -1, min: -1, max: 20 },
      hand_stick_width: { type: "int", default: -1, min: -1, max: 20 },
      draw_head: { type: "bool", default: true },
    },
  },
  vitpose_one_to_all: {
    id: "vitpose_one_to_all",
    display_name: "Pose One-to-All Animation",
    description: "Transfer single pose to video sequence",
    category: "video",
    source: "wan_animate",
    is_video: true,
    inputs: {
      width: { type: "int", default: 832, min: 64, max: 2048, step: 2 },
      height: { type: "int", default: 480, min: 64, max: 2048, step: 2 },
      align_to: {
        type: "combo",
        options: ["ref", "pose", "none"],
        default: "ref",
      },
      draw_face_points: {
        type: "combo",
        options: ["full", "weak", "none"],
        default: "full",
      },
      draw_head: {
        type: "combo",
        options: ["full", "weak", "none"],
        default: "full",
      },
    },
  },
};

/**
 * Get preprocessors by category
 */
export function getPreprocessorsByCategory(
  category: PreprocessorCategory,
): PreprocessorInfo[] {
  return Object.values(PREPROCESSOR_REGISTRY).filter(
    (p) => p.category === category,
  );
}

/**
 * Get preprocessors matching a generation type
 */
export function getPreprocessorsForType(
  generationType: string,
): PreprocessorInfo[] {
  const categories =
    TYPE_TO_CATEGORY[generationType] || TYPE_TO_CATEGORY.custom;
  return Object.values(PREPROCESSOR_REGISTRY).filter((p) =>
    categories.includes(p.category as PreprocessorCategory),
  );
}

/**
 * Get default preprocessor for a generation type
 */
export function getDefaultPreprocessor(generationType: string): string {
  return DEFAULT_PREPROCESSORS[generationType] || "depth_anything_v2";
}

/**
 * Fetch preprocessor list from backend
 */
export async function fetchPreprocessorList(): Promise<PreprocessorInfo[]> {
  try {
    const response = await fetch("/lattice/preprocessors/list");
    if (!response.ok) {
      throw new Error(`HTTP ${response.status}: ${response.statusText}`);
    }
    const data = await response.json();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
    const preprocessors = data.preprocessors;
    return (preprocessors !== null && preprocessors !== undefined && Array.isArray(preprocessors)) ? preprocessors : [];
  } catch (error) {
    console.warn(
      "[PreprocessorService] Failed to fetch from backend, using local registry:",
      error,
    );
    return Object.values(PREPROCESSOR_REGISTRY);
  }
}

/**
 * Fetch preprocessor info from backend
 */
export async function fetchPreprocessorInfo(
  id: string,
): Promise<PreprocessorInfo | null> {
  try {
    const response = await fetch(`/lattice/preprocessors/${id}/info`);
    if (!response.ok) {
      throw new Error(`HTTP ${response.status}: ${response.statusText}`);
    }
    return await response.json();
  } catch (error) {
    console.warn(
      `[PreprocessorService] Failed to fetch info for ${id}, using local registry:`,
      error,
    );
    return PREPROCESSOR_REGISTRY[id] || null;
  }
}

/**
 * Execute a preprocessor on an image
 *
 * @param preprocessorId - The preprocessor to run (e.g., 'depth_anything_v2')
 * @param imageData - Base64 encoded image data (with or without data: prefix)
 * @param options - Preprocessor-specific options
 * @returns Result with base64 encoded output image
 */
export async function executePreprocessor(
  preprocessorId: string,
  imageData: string,
  options: Record<string, string | number | boolean> = {},
): Promise<PreprocessorResult> {
  const startTime = Date.now();

  try {
    // Strip data: prefix if present
    const base64Data = imageData.replace(/^data:image\/\w+;base64,/, "");

    const response = await fetch(
      `/lattice/preprocessors/${preprocessorId}/execute`,
      {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
        },
        body: JSON.stringify({
          image: base64Data,
          options: options,
        }),
      },
    );

    if (!response.ok) {
      const errorData = await response.json().catch(() => ({}));
      throw new Error(
        errorData.error || `HTTP ${response.status}: ${response.statusText}`,
      );
    }

    const result = await response.json();

    return {
      success: true,
      result_image: result.result_image,
      execution_time: Date.now() - startTime,
    };
  } catch (error) {
    // Re-throw with context - don't silently fail
    const errorMessage = error instanceof Error ? error.message : String(error);
    throw new Error(`[PreprocessorService] Failed to execute preprocessor "${preprocessorId}": ${errorMessage}. Check preprocessor availability and input image format.`);
  }
}

/**
 * Render a layer to an image for preprocessing
 * Uses the compositor's export service to capture the current frame
 */
export async function renderLayerToImage(
  layerId: string,
  frame: number,
  resolution: number = 512,
): Promise<string> {
  try {
    // Get the canvas from the engine (type-safe - Window.__latticeEngine is typed in vite-env.d.ts)
    const engine = window.__latticeEngine;
    if (!engine) {
      throw new Error("[PreprocessorService] Engine not available");
    }

    // TODO: renderLayerToCanvas not yet implemented in LatticeEngine
    // Check if method exists at runtime (future implementation)
    type EngineWithLayerRender = typeof engine & {
      renderLayerToCanvas?: (
        layerId: string,
        frame: number,
        resolution: number
      ) => Promise<HTMLCanvasElement | null>;
    };

    const engineExt = engine as EngineWithLayerRender;
    if (typeof engineExt.renderLayerToCanvas !== "function") {
      throw new Error("[PreprocessorService] renderLayerToCanvas not implemented in LatticeEngine");
    }

    // Render the specific layer
    const canvas = await engineExt.renderLayerToCanvas(layerId, frame, resolution);
    if (!canvas) {
      throw new Error(`[PreprocessorService] Failed to render layer "${layerId}" at frame ${frame}`);
    }

    // Convert to base64
    return canvas.toDataURL("image/png");
  } catch (error) {
    if (error instanceof Error && error.message.startsWith("[PreprocessorService]")) {
      throw error;
    }
    throw new Error(`[PreprocessorService] Error rendering layer: ${error instanceof Error ? error.message : String(error)}`);
  }
}

/**
 * Generate from a source layer and apply to a generated layer
 * This is the main entry point for the GeneratedProperties component
 */
export async function generateFromLayer(
  sourceLayerId: string,
  _targetLayerId: string,
  preprocessorId: string,
  options: Record<string, string | number | boolean> = {},
  frame: number = 0,
  onProgress?: (status: string) => void,
): Promise<{
  success: boolean;
  assetId?: string;
  error?: string;
}> {
  try {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const onProgressCallback = onProgress;
    if (onProgressCallback != null && typeof onProgressCallback === "function") {
      onProgressCallback("Rendering source layer...");
    }

    // Get source layer image
    // Type proof: resolution ∈ string | number | boolean | undefined → number
    const resolutionValue = options.resolution;
    const resolution = typeof resolutionValue === "number" && Number.isFinite(resolutionValue) && resolutionValue > 0 ? resolutionValue : 512;
    const sourceImage = await renderLayerToImage(
      sourceLayerId,
      frame,
      resolution,
    );

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const preprocessorRegistryEntry = (PREPROCESSOR_REGISTRY != null && typeof PREPROCESSOR_REGISTRY === "object" && preprocessorId in PREPROCESSOR_REGISTRY && PREPROCESSOR_REGISTRY[preprocessorId] != null && typeof PREPROCESSOR_REGISTRY[preprocessorId] === "object") ? PREPROCESSOR_REGISTRY[preprocessorId] : undefined;
    const displayName = (preprocessorRegistryEntry != null && typeof preprocessorRegistryEntry === "object" && "display_name" in preprocessorRegistryEntry && typeof preprocessorRegistryEntry.display_name === "string") ? preprocessorRegistryEntry.display_name : undefined;
    const progressMessage = "Processing with " + (displayName != null ? displayName : preprocessorId) + "...";
    if (onProgressCallback != null && typeof onProgressCallback === "function") {
      onProgressCallback(progressMessage);
    }

    // Execute preprocessor
    const result = await executePreprocessor(
      preprocessorId,
      sourceImage,
      options,
    );

    // executePreprocessor now throws on errors instead of returning success: false
    if (!result.result_image) {
      throw new Error(`[PreprocessorService] Preprocessor "${preprocessorId}" returned no result image. Preprocessor execution may have failed silently.`);
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (onProgressCallback != null && typeof onProgressCallback === "function") {
      onProgressCallback("Creating asset...");
    }

    // Create asset from result
    const assetId = await createAssetFromBase64(
      result.result_image,
      `generated_${preprocessorId}_${Date.now()}.png`,
    );

    return { success: true, assetId };
  } catch (error) {
    // Re-throw with context - don't silently fail
    const errorMessage = error instanceof Error ? error.message : String(error);
    throw new Error(`[PreprocessorService] Failed to generate from layer "${sourceLayerId}" using preprocessor "${preprocessorId}": ${errorMessage}.`);
  }
}

/**
 * Create an asset from base64 image data
 */
async function createAssetFromBase64(
  base64Data: string,
  filename: string,
): Promise<string> {
  try {
    const projectStore = useProjectStore();

    // Create a unique asset ID
    const assetId = `generated_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

    // Get image dimensions from the base64 data
    const dimensions = await getImageDimensions(
      `data:image/png;base64,${base64Data}`,
    );

    // Create the asset reference
    const asset = {
      id: assetId,
      type: "image" as const, // Generated images are stored as image assets
      source: "generated" as const,
      width: dimensions.width,
      height: dimensions.height,
      data: `data:image/png;base64,${base64Data}`,
      filename: filename,
    };

    // Store in project assets
    projectStore.project.assets[assetId] = asset;

    return assetId;
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);
    throw new Error(`[PreprocessorService] Cannot create asset from base64 data: ${errorMessage}. Check image data format and project store availability.`);
  }
}

/**
 * Get image dimensions from a data URL
 */
function getImageDimensions(
  dataUrl: string,
): Promise<{ width: number; height: number }> {
  return new Promise((resolve, _reject) => {
    const img = new Image();
    img.onload = () => {
      resolve({ width: img.width, height: img.height });
    };
    img.onerror = () => {
      // Default to 512x512 if we can't load
      resolve({ width: 512, height: 512 });
    };
    img.src = dataUrl;
  });
}

// Export all functions
export default {
  PREPROCESSOR_REGISTRY,
  getPreprocessorsByCategory,
  getPreprocessorsForType,
  getDefaultPreprocessor,
  fetchPreprocessorList,
  fetchPreprocessorInfo,
  executePreprocessor,
  renderLayerToImage,
  generateFromLayer,
};
