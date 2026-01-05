"""
ComfyUI ControlNet & AI Preprocessors - Unified Interface.

This module provides a unified UI wrapper for executing image/video preprocessor
nodes from the open-source ComfyUI community. We are providing a UI integration
layer - the actual preprocessing work is done by these amazing projects:

==============================================================================
                         OPEN SOURCE ATTRIBUTION
==============================================================================

This integration wraps nodes from the following open-source projects:

1. comfyui_controlnet_aux - ControlNet Auxiliary Preprocessors
   Repository: https://github.com/Fannovel16/comfyui_controlnet_aux
   Author: Fannovel16 and contributors
   License: Apache 2.0
   Contains: Depth estimation, normal maps, pose detection, edge detection,
             lineart, scribble, segmentation, and more

2. NormalCrafter - Video-to-Normal Diffusion Model
   Repository: https://github.com/Binyr/NormalCrafter
   Authors: Binyr and research team (ICCV 2025)
   Paper: "NormalCrafter: Learning Surface Normal from Video Diffusion Models"
   Description: Temporally consistent normal maps from video

3. ComfyUI-NormalCrafterWrapper - ComfyUI Integration
   Repository: https://github.com/AIWarper/ComfyUI-NormalCrafterWrapper
   Author: AIWarper
   Description: ComfyUI node wrapper for NormalCrafter

4. ComfyUI-WanAnimatePreprocess - Video Animation Preprocessing
   Repository: https://github.com/kijai/ComfyUI-WanAnimatePreprocess
   Author: Kijai (Jukka Seppänen)
   Description: ViTPose, face detection, and pose retargeting for Wan 2.2

5. Additional Contributors:
   - Lvmin Zhang & Maneesh Agrawala (ControlNet original research)
   - The entire ComfyUI community for building this ecosystem

==============================================================================
                         LICENSE NOTICE
==============================================================================

This wrapper code is part of Lattice Compositor (MIT License).
The underlying preprocessor implementations retain their original licenses:
- comfyui_controlnet_aux: Apache 2.0
- NormalCrafter: Research license (see original repo)
- ComfyUI-NormalCrafterWrapper: MIT
- ComfyUI-WanAnimatePreprocess: MIT

We gratefully acknowledge all contributors to these projects.

==============================================================================
"""

import base64
import json
import logging
import uuid
from enum import Enum
from typing import Any


logger = logging.getLogger("comfyui.preprocessors")

# ============================================================================
# Preprocessor Registry
# ============================================================================


class PreprocessorCategory(str, Enum):
  DEPTH = "depth"
  NORMAL = "normal"
  POSE = "pose"
  EDGE = "edge"
  LINEART = "lineart"
  SCRIBBLE = "scribble"
  SEGMENTATION = "segmentation"
  VIDEO = "video"  # New: Video-specific preprocessors
  OTHER = "other"


# Attribution metadata for each source
SOURCE_ATTRIBUTION = {
  "controlnet_aux": {
    "name": "comfyui_controlnet_aux",
    "repo": "https://github.com/Fannovel16/comfyui_controlnet_aux",
    "author": "Fannovel16",
    "license": "Apache 2.0",
  },
  "normalcrafter": {
    "name": "NormalCrafter / ComfyUI-NormalCrafterWrapper",
    "repo": "https://github.com/Binyr/NormalCrafter | https://github.com/AIWarper/ComfyUI-NormalCrafterWrapper",
    "author": "Binyr, AIWarper",
    "license": "Research / MIT",
  },
  "wan_animate": {
    "name": "ComfyUI-WanAnimatePreprocess",
    "repo": "https://github.com/kijai/ComfyUI-WanAnimatePreprocess",
    "author": "Kijai",
    "license": "MIT",
  },
}


# Complete registry of available preprocessors
PREPROCESSOR_REGISTRY: dict[str, dict[str, Any]] = {
  # ========================================================================
  # DEPTH (from comfyui_controlnet_aux - Fannovel16)
  # ========================================================================
  "depth_anything_v2": {
    "node_class": "DepthAnythingV2Preprocessor",
    "display_name": "Depth Anything V2",
    "category": PreprocessorCategory.DEPTH,
    "source": "controlnet_aux",
    "description": "Best general-purpose depth estimation",
    "inputs": {
      "ckpt_name": {
        "type": "combo",
        "options": [
          "depth_anything_v2_vitl.pth",
          "depth_anything_v2_vitb.pth",
          "depth_anything_v2_vits.pth",
          "depth_anything_v2_vitg.pth",
        ],
        "default": "depth_anything_v2_vitl.pth",
      },
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "midas": {
    "node_class": "MiDaS-DepthMapPreprocessor",
    "display_name": "MiDaS Depth",
    "category": PreprocessorCategory.DEPTH,
    "source": "controlnet_aux",
    "description": "Classic MiDaS depth estimation",
    "inputs": {
      "a": {"type": "float", "default": 6.283185307179586, "min": 0, "max": 12.566},
      "bg_threshold": {"type": "float", "default": 0.1, "min": 0, "max": 1},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "zoe_depth": {
    "node_class": "Zoe-DepthMapPreprocessor",
    "display_name": "ZoeDepth",
    "category": PreprocessorCategory.DEPTH,
    "source": "controlnet_aux",
    "description": "Zero-shot depth estimation",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "leres_depth": {
    "node_class": "LeReS-DepthMapPreprocessor",
    "display_name": "LeReS Depth",
    "category": PreprocessorCategory.DEPTH,
    "source": "controlnet_aux",
    "description": "Learning to recover 3D scene shape",
    "inputs": {
      "rm_nearest": {"type": "float", "default": 0.0, "min": 0, "max": 100},
      "rm_background": {"type": "float", "default": 0.0, "min": 0, "max": 100},
      "boost": {"type": "combo", "options": ["enable", "disable"], "default": "disable"},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "metric3d_depth": {
    "node_class": "Metric3D-DepthMapPreprocessor",
    "display_name": "Metric3D Depth",
    "category": PreprocessorCategory.DEPTH,
    "source": "controlnet_aux",
    "description": "Metric depth estimation",
    "inputs": {
      "backbone": {
        "type": "combo",
        "options": ["vit-small", "vit-large", "vit-giant2"],
        "default": "vit-small",
      },
      "fx": {"type": "int", "default": 1000},
      "fy": {"type": "int", "default": 1000},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  # ========================================================================
  # NORMAL (from comfyui_controlnet_aux - Fannovel16)
  # ========================================================================
  "normal_bae": {
    "node_class": "BAE-NormalMapPreprocessor",
    "display_name": "BAE Normal Map",
    "category": PreprocessorCategory.NORMAL,
    "source": "controlnet_aux",
    "description": "Surface normal estimation using BAE",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "normal_dsine": {
    "node_class": "DSINE-NormalMapPreprocessor",
    "display_name": "DSINE Normal Map",
    "category": PreprocessorCategory.NORMAL,
    "source": "controlnet_aux",
    "description": "DSINE surface normal estimation",
    "inputs": {
      "fov": {"type": "float", "default": 60.0, "min": 0, "max": 180},
      "iterations": {"type": "int", "default": 5, "min": 1, "max": 20},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "metric3d_normal": {
    "node_class": "Metric3D-NormalMapPreprocessor",
    "display_name": "Metric3D Normal",
    "category": PreprocessorCategory.NORMAL,
    "source": "controlnet_aux",
    "description": "Metric3D normal estimation",
    "inputs": {
      "backbone": {
        "type": "combo",
        "options": ["vit-small", "vit-large", "vit-giant2"],
        "default": "vit-small",
      },
      "fx": {"type": "int", "default": 1000},
      "fy": {"type": "int", "default": 1000},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "midas_normal": {
    "node_class": "MiDaS-NormalMapPreprocessor",
    "display_name": "MiDaS Normal",
    "category": PreprocessorCategory.NORMAL,
    "source": "controlnet_aux",
    "description": "Normal map from MiDaS depth",
    "inputs": {
      "a": {"type": "float", "default": 6.283185307179586, "min": 0, "max": 12.566},
      "bg_threshold": {"type": "float", "default": 0.1, "min": 0, "max": 1},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  # ========================================================================
  # NORMALCRAFTER (from Binyr/NormalCrafter + AIWarper/ComfyUI-NormalCrafterWrapper)
  # Video-to-Normal diffusion model - temporally consistent normal sequences
  # ========================================================================
  "normalcrafter": {
    "node_class": "NormalCrafter",
    "display_name": "NormalCrafter (Video)",
    "category": PreprocessorCategory.NORMAL,
    "source": "normalcrafter",
    "description": "Temporally consistent normal maps from video (ICCV 2025)",
    "is_video": True,
    "inputs": {
      "seed": {"type": "int", "default": 42, "min": 0, "max": 2147483647},
      "max_res_dimension": {"type": "int", "default": 1024, "min": 256, "max": 2048},
      "window_size": {"type": "int", "default": 14, "min": 1, "max": 32},
      "time_step_size": {"type": "int", "default": 10, "min": 1, "max": 20},
      "decode_chunk_size": {"type": "int", "default": 4, "min": 1, "max": 16},
      "fps_for_time_ids": {"type": "int", "default": 7, "min": 1, "max": 60},
      "motion_bucket_id": {"type": "int", "default": 127, "min": 0, "max": 255},
      "noise_aug_strength": {"type": "float", "default": 0.0, "min": 0.0, "max": 1.0},
    },
    "outputs": ["IMAGE"],  # Outputs sequence of normal maps
  },
  # ========================================================================
  # POSE (from comfyui_controlnet_aux - Fannovel16)
  # ========================================================================
  "dwpose": {
    "node_class": "DWPreprocessor",
    "display_name": "DWPose",
    "category": PreprocessorCategory.POSE,
    "source": "controlnet_aux",
    "description": "Best pose estimation (body + hands + face)",
    "inputs": {
      "detect_hand": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "detect_body": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "detect_face": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
      "bbox_detector": {
        "type": "combo",
        "options": ["yolox_l.onnx", "yolo_nas_l_fp16.onnx"],
        "default": "yolox_l.onnx",
      },
      "pose_estimator": {
        "type": "combo",
        "options": ["dw-ll_ucoco_384_bs5.torchscript.pt", "dw-ll_ucoco.onnx"],
        "default": "dw-ll_ucoco_384_bs5.torchscript.pt",
      },
    },
    "outputs": ["IMAGE", "POSE_KEYPOINT"],
  },
  "openpose": {
    "node_class": "OpenposePreprocessor",
    "display_name": "OpenPose",
    "category": PreprocessorCategory.POSE,
    "source": "controlnet_aux",
    "description": "Classic OpenPose skeleton detection",
    "inputs": {
      "detect_hand": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "detect_body": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "detect_face": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE", "POSE_KEYPOINT"],
  },
  "animal_pose": {
    "node_class": "AnimalPosePreprocessor",
    "display_name": "Animal Pose",
    "category": PreprocessorCategory.POSE,
    "source": "controlnet_aux",
    "description": "Animal pose estimation",
    "inputs": {
      "bbox_detector": {"type": "combo", "options": ["yolox_l.onnx"], "default": "yolox_l.onnx"},
      "pose_estimator": {
        "type": "combo",
        "options": ["rtmpose-m_ap10k_256_bs5.torchscript.pt"],
        "default": "rtmpose-m_ap10k_256_bs5.torchscript.pt",
      },
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE", "POSE_KEYPOINT"],
  },
  "mediapipe_face": {
    "node_class": "MediaPipe-FaceMeshPreprocessor",
    "display_name": "MediaPipe Face Mesh",
    "category": PreprocessorCategory.POSE,
    "source": "controlnet_aux",
    "description": "Face mesh detection",
    "inputs": {
      "max_faces": {"type": "int", "default": 10, "min": 1, "max": 50},
      "min_confidence": {"type": "float", "default": 0.5, "min": 0.01, "max": 1.0},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "densepose": {
    "node_class": "DensePosePreprocessor",
    "display_name": "DensePose",
    "category": PreprocessorCategory.POSE,
    "source": "controlnet_aux",
    "description": "Dense human pose estimation",
    "inputs": {
      "model": {
        "type": "combo",
        "options": ["densepose_r50_fpn_dl.torchscript", "densepose_r101_fpn_dl.torchscript"],
        "default": "densepose_r50_fpn_dl.torchscript",
      },
      "cmap": {
        "type": "combo",
        "options": ["Viridis", "Parula", "Plasma", "Magma", "Inferno"],
        "default": "Viridis",
      },
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  # ========================================================================
  # VIDEO POSE (from kijai/ComfyUI-WanAnimatePreprocess)
  # For Wan 2.2 video animation preprocessing
  # ========================================================================
  "vitpose": {
    "node_class": "PoseAndFaceDetection",
    "display_name": "ViTPose + Face (Video)",
    "category": PreprocessorCategory.VIDEO,
    "source": "wan_animate",
    "description": "ViTPose pose detection with face for video animation (Kijai)",
    "is_video": True,
    "inputs": {
      "width": {"type": "int", "default": 832, "min": 64, "max": 2048},
      "height": {"type": "int", "default": 480, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE", "POSEDATA"],
  },
  "vitpose_draw": {
    "node_class": "DrawViTPose",
    "display_name": "Draw ViTPose Skeleton",
    "category": PreprocessorCategory.VIDEO,
    "source": "wan_animate",
    "description": "Render ViTPose skeleton visualization (Kijai)",
    "inputs": {
      "width": {"type": "int", "default": 832, "min": 64, "max": 2048},
      "height": {"type": "int", "default": 480, "min": 64, "max": 2048},
      "retarget_padding": {"type": "int", "default": 16, "min": 0, "max": 512},
      "body_stick_width": {"type": "int", "default": -1, "min": -1, "max": 20},
      "hand_stick_width": {"type": "int", "default": -1, "min": -1, "max": 20},
      "draw_head": {"type": "bool", "default": True},
    },
    "outputs": ["IMAGE"],
  },
  "vitpose_one_to_all": {
    "node_class": "PoseDetectionOneToAllAnimation",
    "display_name": "Pose One-to-All Animation",
    "category": PreprocessorCategory.VIDEO,
    "source": "wan_animate",
    "description": "Transfer single pose to video sequence (Kijai)",
    "is_video": True,
    "inputs": {
      "width": {"type": "int", "default": 832, "min": 64, "max": 2048, "step": 2},
      "height": {"type": "int", "default": 480, "min": 64, "max": 2048, "step": 2},
      "align_to": {"type": "combo", "options": ["ref", "pose", "none"], "default": "ref"},
      "draw_face_points": {"type": "combo", "options": ["full", "weak", "none"], "default": "full"},
      "draw_head": {"type": "combo", "options": ["full", "weak", "none"], "default": "full"},
    },
    "outputs": ["IMAGE", "POSEDATA"],
  },
  # ========================================================================
  # EDGE (from comfyui_controlnet_aux - Fannovel16)
  # ========================================================================
  "canny": {
    "node_class": "CannyEdgePreprocessor",
    "display_name": "Canny Edge",
    "category": PreprocessorCategory.EDGE,
    "source": "controlnet_aux",
    "description": "Canny edge detection",
    "inputs": {
      "low_threshold": {"type": "int", "default": 100, "min": 0, "max": 255},
      "high_threshold": {"type": "int", "default": 200, "min": 0, "max": 255},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "hed": {
    "node_class": "HEDPreprocessor",
    "display_name": "HED Soft Edge",
    "category": PreprocessorCategory.EDGE,
    "source": "controlnet_aux",
    "description": "Holistically-nested edge detection",
    "inputs": {
      "safe": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "pidinet": {
    "node_class": "PiDiNetPreprocessor",
    "display_name": "PiDiNet Soft Edge",
    "category": PreprocessorCategory.EDGE,
    "source": "controlnet_aux",
    "description": "Pixel difference network edges",
    "inputs": {
      "safe": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "teed": {
    "node_class": "TEEDPreprocessor",
    "display_name": "TEED Edge",
    "category": PreprocessorCategory.EDGE,
    "source": "controlnet_aux",
    "description": "Tiny and efficient edge detector",
    "inputs": {
      "safe_steps": {"type": "int", "default": 2, "min": 0, "max": 10},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "diffusion_edge": {
    "node_class": "DiffusionEdge_Preprocessor",
    "display_name": "Diffusion Edge",
    "category": PreprocessorCategory.EDGE,
    "source": "controlnet_aux",
    "description": "Diffusion-based edge detection",
    "inputs": {
      "environment": {
        "type": "combo",
        "options": ["indoor", "outdoor", "urban"],
        "default": "indoor",
      },
      "patch_batch_size": {"type": "int", "default": 4, "min": 1, "max": 16},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "binary": {
    "node_class": "BinaryPreprocessor",
    "display_name": "Binary Threshold",
    "category": PreprocessorCategory.EDGE,
    "source": "controlnet_aux",
    "description": "Simple binary thresholding",
    "inputs": {
      "bin_threshold": {"type": "int", "default": 100, "min": 0, "max": 255},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  # ========================================================================
  # LINEART (from comfyui_controlnet_aux - Fannovel16)
  # ========================================================================
  "lineart": {
    "node_class": "LineArtPreprocessor",
    "display_name": "Lineart",
    "category": PreprocessorCategory.LINEART,
    "source": "controlnet_aux",
    "description": "Standard lineart extraction",
    "inputs": {
      "coarse": {"type": "combo", "options": ["enable", "disable"], "default": "disable"},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "lineart_realistic": {
    "node_class": "Realistic_Lineart",
    "display_name": "Realistic Lineart",
    "category": PreprocessorCategory.LINEART,
    "source": "controlnet_aux",
    "description": "Realistic lineart extraction",
    "inputs": {
      "coarse": {"type": "combo", "options": ["enable", "disable"], "default": "disable"},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "lineart_anime": {
    "node_class": "AnimeLineArtPreprocessor",
    "display_name": "Anime Lineart",
    "category": PreprocessorCategory.LINEART,
    "source": "controlnet_aux",
    "description": "Anime-style lineart extraction",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "lineart_manga": {
    "node_class": "Manga2Anime_LineArt_Preprocessor",
    "display_name": "Manga Lineart",
    "category": PreprocessorCategory.LINEART,
    "source": "controlnet_aux",
    "description": "Manga-style line extraction",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "lineart_standard": {
    "node_class": "LineartStandardPreprocessor",
    "display_name": "Standard Lineart",
    "category": PreprocessorCategory.LINEART,
    "source": "controlnet_aux",
    "description": "Standard lineart with Gaussian",
    "inputs": {
      "guassian_sigma": {"type": "float", "default": 6.0, "min": 0.01, "max": 100},
      "intensity_threshold": {"type": "int", "default": 8, "min": 0, "max": 16},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "anyline": {
    "node_class": "AnyLineArtPreprocessor_aux",
    "display_name": "AnyLine",
    "category": PreprocessorCategory.LINEART,
    "source": "controlnet_aux",
    "description": "Universal lineart extraction",
    "inputs": {
      "merge_with_lineart": {
        "type": "combo",
        "options": ["lineart_realistic", "lineart_coarse", "lineart_standard", "none"],
        "default": "lineart_realistic",
      },
      "lineart_lower_bound": {"type": "float", "default": 0, "min": 0, "max": 1},
      "lineart_upper_bound": {"type": "float", "default": 1, "min": 0, "max": 1},
      "resolution": {"type": "int", "default": 1280, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "mlsd": {
    "node_class": "M-LSDPreprocessor",
    "display_name": "M-LSD Lines",
    "category": PreprocessorCategory.LINEART,
    "source": "controlnet_aux",
    "description": "Mobile line segment detection",
    "inputs": {
      "score_threshold": {"type": "float", "default": 0.1, "min": 0.01, "max": 2.0},
      "distance_threshold": {"type": "float", "default": 0.1, "min": 0.01, "max": 20.0},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  # ========================================================================
  # SCRIBBLE (from comfyui_controlnet_aux - Fannovel16)
  # ========================================================================
  "scribble_hed": {
    "node_class": "ScribblePreprocessor",
    "display_name": "Scribble (HED)",
    "category": PreprocessorCategory.SCRIBBLE,
    "source": "controlnet_aux",
    "description": "Scribble-like from HED",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "scribble_pidinet": {
    "node_class": "Scribble_PiDiNet_Preprocessor",
    "display_name": "Scribble (PiDiNet)",
    "category": PreprocessorCategory.SCRIBBLE,
    "source": "controlnet_aux",
    "description": "Scribble-like from PiDiNet",
    "inputs": {
      "safe": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "scribble_xdog": {
    "node_class": "Scribble_XDoG_Preprocessor",
    "display_name": "Scribble (XDoG)",
    "category": PreprocessorCategory.SCRIBBLE,
    "source": "controlnet_aux",
    "description": "XDoG-based scribble",
    "inputs": {
      "threshold": {"type": "int", "default": 32, "min": 1, "max": 64},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "fake_scribble": {
    "node_class": "FakeScribblePreprocessor",
    "display_name": "Fake Scribble",
    "category": PreprocessorCategory.SCRIBBLE,
    "source": "controlnet_aux",
    "description": "Generate fake scribble lines",
    "inputs": {
      "safe": {"type": "combo", "options": ["enable", "disable"], "default": "enable"},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  # ========================================================================
  # SEGMENTATION (from comfyui_controlnet_aux - Fannovel16)
  # ========================================================================
  "sam": {
    "node_class": "SAMPreprocessor",
    "display_name": "Segment Anything (SAM)",
    "category": PreprocessorCategory.SEGMENTATION,
    "source": "controlnet_aux",
    "description": "Segment Anything Model",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "oneformer_coco": {
    "node_class": "OneFormer-COCO-SemSegPreprocessor",
    "display_name": "OneFormer (COCO)",
    "category": PreprocessorCategory.SEGMENTATION,
    "source": "controlnet_aux",
    "description": "COCO semantic segmentation",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "oneformer_ade20k": {
    "node_class": "OneFormer-ADE20K-SemSegPreprocessor",
    "display_name": "OneFormer (ADE20K)",
    "category": PreprocessorCategory.SEGMENTATION,
    "source": "controlnet_aux",
    "description": "ADE20K semantic segmentation",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "uniformer": {
    "node_class": "UniformerSemSegPreprocessor",
    "display_name": "Uniformer Segmentation",
    "category": PreprocessorCategory.SEGMENTATION,
    "source": "controlnet_aux",
    "description": "Uniformer semantic segmentation",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "anime_face_seg": {
    "node_class": "AnimeFace_SemSegPreprocessor",
    "display_name": "Anime Face Segmentation",
    "category": PreprocessorCategory.SEGMENTATION,
    "source": "controlnet_aux",
    "description": "Anime face part segmentation",
    "inputs": {
      "remove_background_using_abg": {
        "type": "combo",
        "options": ["enable", "disable"],
        "default": "enable",
      },
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  # ========================================================================
  # OTHER (from comfyui_controlnet_aux - Fannovel16)
  # ========================================================================
  "color_palette": {
    "node_class": "ColorPreprocessor",
    "display_name": "Color Palette",
    "category": PreprocessorCategory.OTHER,
    "source": "controlnet_aux",
    "description": "Extract color palette",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "shuffle": {
    "node_class": "ShufflePreprocessor",
    "display_name": "Content Shuffle",
    "category": PreprocessorCategory.OTHER,
    "source": "controlnet_aux",
    "description": "Shuffle image content",
    "inputs": {"resolution": {"type": "int", "default": 512, "min": 64, "max": 2048}},
    "outputs": ["IMAGE"],
  },
  "tile": {
    "node_class": "TilePreprocessor",
    "display_name": "Tile",
    "category": PreprocessorCategory.OTHER,
    "source": "controlnet_aux",
    "description": "Tile/upscale preprocessing",
    "inputs": {
      "pyrUp_iters": {"type": "int", "default": 3, "min": 1, "max": 10},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "luminance": {
    "node_class": "ImageLuminanceDetector",
    "display_name": "Luminance",
    "category": PreprocessorCategory.OTHER,
    "source": "controlnet_aux",
    "description": "Extract luminance channel",
    "inputs": {
      "gamma_correction": {"type": "float", "default": 1.0, "min": 0.1, "max": 2.0},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "intensity": {
    "node_class": "ImageIntensityDetector",
    "display_name": "Intensity",
    "category": PreprocessorCategory.OTHER,
    "source": "controlnet_aux",
    "description": "Extract intensity",
    "inputs": {
      "gamma_correction": {"type": "float", "default": 1.0, "min": 0.1, "max": 2.0},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE"],
  },
  "inpaint": {
    "node_class": "InpaintPreprocessor",
    "display_name": "Inpaint Mask",
    "category": PreprocessorCategory.OTHER,
    "source": "controlnet_aux",
    "description": "Inpainting mask preparation",
    "inputs": {},
    "outputs": ["IMAGE", "MASK"],
  },
  "unimatch_flow": {
    "node_class": "Unimatch_OptFlowPreprocessor",
    "display_name": "Optical Flow (UniMatch)",
    "category": PreprocessorCategory.OTHER,
    "source": "controlnet_aux",
    "description": "Optical flow estimation",
    "inputs": {
      "ckpt_name": {
        "type": "combo",
        "options": [
          "gmflow-scale1-mixdata.pth",
          "gmflow-scale2-mixdata.pth",
          "gmflow-scale2-regrefine6-mixdata.pth",
        ],
        "default": "gmflow-scale2-regrefine6-mixdata.pth",
      },
      "backward_flow": {"type": "combo", "options": ["enable", "disable"], "default": "disable"},
      "bidirectional_flow": {
        "type": "combo",
        "options": ["enable", "disable"],
        "default": "disable",
      },
    },
    "outputs": ["IMAGE", "IMAGE"],
  },
  "mesh_graphormer": {
    "node_class": "MeshGraphormer-DepthMapPreprocessor",
    "display_name": "MeshGraphormer Hand Depth",
    "category": PreprocessorCategory.OTHER,
    "source": "controlnet_aux",
    "description": "Hand mesh and depth estimation",
    "inputs": {
      "mask_bbox_padding": {"type": "int", "default": 30, "min": 0, "max": 100},
      "resolution": {"type": "int", "default": 512, "min": 64, "max": 2048},
    },
    "outputs": ["IMAGE", "MASK", "IMAGE"],
  },
}


def get_preprocessor_list() -> list[dict[str, Any]]:
  """Get list of all available preprocessors with metadata for frontend."""
  result = []
  for key, info in PREPROCESSOR_REGISTRY.items():
    source_key = info.get("source", "controlnet_aux")
    source_info = SOURCE_ATTRIBUTION.get(source_key, {})

    result.append(
      {
        "id": key,
        "name": info["display_name"],
        "category": info["category"].value,
        "description": info["description"],
        "inputs": info["inputs"],
        "node_class": info["node_class"],
        "is_video": info.get("is_video", False),
        "source": {
          "name": source_info.get("name", "Unknown"),
          "repo": source_info.get("repo", ""),
          "author": source_info.get("author", "Unknown"),
        },
      }
    )
  return result


def get_preprocessors_by_category() -> dict[str, list[dict[str, Any]]]:
  """Get preprocessors grouped by category for frontend UI."""
  categories = {}
  for key, info in PREPROCESSOR_REGISTRY.items():
    cat = info["category"].value
    if cat not in categories:
      categories[cat] = []

    source_key = info.get("source", "controlnet_aux")
    source_info = SOURCE_ATTRIBUTION.get(source_key, {})

    categories[cat].append(
      {
        "id": key,
        "name": info["display_name"],
        "description": info["description"],
        "inputs": info["inputs"],
        "is_video": info.get("is_video", False),
        "author": source_info.get("author", "Unknown"),
      }
    )
  return categories


def get_attribution() -> dict[str, Any]:
  """Get full attribution information for display."""
  return {
    "message": "This integration wraps nodes from the following open-source projects:",
    "sources": [
      {"name": v["name"], "repo": v["repo"], "author": v["author"], "license": v["license"]}
      for v in SOURCE_ATTRIBUTION.values()
    ],
    "note": "We are grateful to all contributors who make these tools freely available.",
  }


# ============================================================================
# Workflow Execution
# ============================================================================


def _create_preprocessor_workflow(
  preprocessor_id: str, image_path: str, options: dict[str, Any]
) -> dict[str, Any]:
  """
  Create a ComfyUI workflow for running a preprocessor.

  Returns a workflow dict that can be queued via ComfyUI API.
  """
  if preprocessor_id not in PREPROCESSOR_REGISTRY:
    raise ValueError(f"Unknown preprocessor: {preprocessor_id}")

  info = PREPROCESSOR_REGISTRY[preprocessor_id]
  node_class = info["node_class"]
  default_inputs = info.get("inputs", {})

  # Build node inputs
  node_inputs = {}
  for input_name, input_spec in default_inputs.items():
    if input_name in options:
      node_inputs[input_name] = options[input_name]
    else:
      node_inputs[input_name] = input_spec.get("default")

  # Create workflow
  workflow = {
    "1": {"class_type": "LoadImage", "inputs": {"image": image_path}},
    "2": {"class_type": node_class, "inputs": {"image": ["1", 0], **node_inputs}},
    "3": {
      "class_type": "SaveImage",
      "inputs": {"images": ["2", 0], "filename_prefix": f"preprocess_{preprocessor_id}"},
    },
  }

  return workflow


async def execute_preprocessor(
  preprocessor_id: str,
  image_data: bytes,
  options: dict[str, Any] | None = None,
  server_address: str = "127.0.0.1:8188",
) -> dict[str, Any]:
  """
  Execute a preprocessor on an image via ComfyUI API.

  Args:
      preprocessor_id: ID from PREPROCESSOR_REGISTRY
      image_data: Raw image bytes (PNG/JPEG)
      options: Preprocessor-specific options
      server_address: ComfyUI server address

  Returns:
      Dict with status, result image as base64, and metadata
  """
  import aiohttp

  if preprocessor_id not in PREPROCESSOR_REGISTRY:
    return {"status": "error", "message": f"Unknown preprocessor: {preprocessor_id}"}

  options = options or {}
  client_id = str(uuid.uuid4())

  try:
    async with aiohttp.ClientSession() as session:
      # Step 1: Upload image
      upload_url = f"http://{server_address}/upload/image"

      form = aiohttp.FormData()
      form.add_field("image", image_data, filename="input.png", content_type="image/png")
      form.add_field("overwrite", "true")

      async with session.post(upload_url, data=form) as resp:
        if resp.status != 200:
          return {"status": "error", "message": f"Upload failed: {resp.status}"}
        upload_result = await resp.json()
        image_name = upload_result.get("name")
        if not image_name:
          return {"status": "error", "message": "Upload failed: no filename returned"}

      logger.info(f"Uploaded image as: {image_name}")

      # Step 2: Create and queue workflow
      workflow = _create_preprocessor_workflow(preprocessor_id, image_name, options)

      prompt_url = f"http://{server_address}/prompt"
      payload = {"prompt": workflow, "client_id": client_id}

      async with session.post(prompt_url, json=payload) as resp:
        if resp.status != 200:
          error_text = await resp.text()
          return {"status": "error", "message": f"Queue failed: {error_text}"}
        queue_result = await resp.json()
        prompt_id = queue_result.get("prompt_id")

      logger.info(f"Queued workflow: {prompt_id}")

      # Step 3: Wait for completion via WebSocket
      ws_url = f"ws://{server_address}/ws?clientId={client_id}"

      async with session.ws_connect(ws_url) as ws:
        async for msg in ws:
          if msg.type == aiohttp.WSMsgType.TEXT:
            data = json.loads(msg.data)

            if (
              data.get("type") == "executing"
              and data.get("data", {}).get("prompt_id") == prompt_id
              and data.get("data", {}).get("node") is None
            ):
              logger.info("Execution complete")
              break

            elif data.get("type") == "execution_error":
              error_data = data.get("data", {})
              return {
                "status": "error",
                "message": f"Execution error: {error_data.get('exception_message', 'Unknown')}",
              }

      # Step 4: Get output image
      history_url = f"http://{server_address}/history/{prompt_id}"

      async with session.get(history_url) as resp:
        if resp.status != 200:
          return {"status": "error", "message": "Failed to get history"}
        history = await resp.json()

      outputs = history.get(prompt_id, {}).get("outputs", {})
      save_node_output = outputs.get("3", {})
      images = save_node_output.get("images", [])

      if not images:
        return {"status": "error", "message": "No output image generated"}

      output_image = images[0]
      output_filename = output_image.get("filename")
      output_subfolder = output_image.get("subfolder", "")

      # Step 5: Download result image
      view_url = f"http://{server_address}/view"
      params = {"filename": output_filename, "subfolder": output_subfolder, "type": "output"}

      async with session.get(view_url, params=params) as resp:
        if resp.status != 200:
          return {"status": "error", "message": "Failed to download result"}
        result_bytes = await resp.read()

      result_b64 = base64.b64encode(result_bytes).decode("utf-8")

      # Include attribution in response
      source_key = PREPROCESSOR_REGISTRY[preprocessor_id].get("source", "controlnet_aux")
      source_info = SOURCE_ATTRIBUTION.get(source_key, {})

      return {
        "status": "success",
        "image": f"data:image/png;base64,{result_b64}",
        "preprocessor": preprocessor_id,
        "options": options,
        "attribution": {
          "source": source_info.get("name", "Unknown"),
          "author": source_info.get("author", "Unknown"),
          "repo": source_info.get("repo", ""),
        },
      }

  except Exception as e:
    logger.error(f"Preprocessor execution failed: {e}")
    return {"status": "error", "message": str(e)}


# ============================================================================
# ComfyUI Route Registration
# ============================================================================

try:
  from aiohttp import web
  from server import PromptServer

  routes = PromptServer.instance.routes

  @routes.get("/lattice/preprocessors/list")
  async def list_preprocessors(request):
    """Get list of all available preprocessors."""
    return web.json_response(
      {
        "status": "success",
        "preprocessors": get_preprocessor_list(),
        "total": len(PREPROCESSOR_REGISTRY),
      }
    )

  @routes.get("/lattice/preprocessors/categories")
  async def list_preprocessors_by_category(request):
    """Get preprocessors grouped by category."""
    return web.json_response({"status": "success", "categories": get_preprocessors_by_category()})

  @routes.get("/lattice/preprocessors/attribution")
  async def get_attribution_route(request):
    """Get attribution information for all sources."""
    return web.json_response({"status": "success", **get_attribution()})

  @routes.get("/lattice/preprocessors/{preprocessor_id}/info")
  async def get_preprocessor_info(request):
    """Get detailed info for a specific preprocessor."""
    preprocessor_id = request.match_info["preprocessor_id"]

    if preprocessor_id not in PREPROCESSOR_REGISTRY:
      return web.json_response(
        {"status": "error", "message": f"Unknown preprocessor: {preprocessor_id}"}, status=404
      )

    info = PREPROCESSOR_REGISTRY[preprocessor_id]
    source_key = info.get("source", "controlnet_aux")
    source_info = SOURCE_ATTRIBUTION.get(source_key, {})

    return web.json_response(
      {
        "status": "success",
        "preprocessor": {
          "id": preprocessor_id,
          "name": info["display_name"],
          "category": info["category"].value,
          "description": info["description"],
          "node_class": info["node_class"],
          "inputs": info["inputs"],
          "outputs": info["outputs"],
          "is_video": info.get("is_video", False),
          "source": {
            "name": source_info.get("name", "Unknown"),
            "repo": source_info.get("repo", ""),
            "author": source_info.get("author", "Unknown"),
            "license": source_info.get("license", "Unknown"),
          },
        },
      }
    )

  @routes.post("/lattice/preprocessors/{preprocessor_id}/execute")
  async def execute_preprocessor_route(request):
    """Execute a preprocessor on an image."""
    preprocessor_id = request.match_info["preprocessor_id"]

    if preprocessor_id not in PREPROCESSOR_REGISTRY:
      return web.json_response(
        {"status": "error", "message": f"Unknown preprocessor: {preprocessor_id}"}, status=404
      )

    try:
      data = await request.json()

      image_b64 = data.get("image")
      if not image_b64:
        return web.json_response(
          {"status": "error", "message": "Missing 'image' field"}, status=400
        )

      if "," in image_b64:
        image_b64 = image_b64.split(",")[1]

      image_bytes = base64.b64decode(image_b64)
      options = data.get("options", {})

      server_address = f"{request.host}"
      if ":" not in server_address:
        server_address = f"{server_address}:8188"

      result = await execute_preprocessor(preprocessor_id, image_bytes, options, server_address)

      if result["status"] == "error":
        return web.json_response(result, status=500)

      return web.json_response(result)

    except json.JSONDecodeError:
      return web.json_response(
        {"status": "error", "message": "Invalid JSON in request body"}, status=400
      )
    except Exception as e:
      logger.error(f"Preprocessor endpoint error: {e}")
      return web.json_response({"status": "error", "message": f"Internal error: {e!s}"}, status=500)

  logger.info(
    f"ControlNet Preprocessor routes registered ({len(PREPROCESSOR_REGISTRY)} preprocessors)"
  )
  logger.info(
    "Sources: comfyui_controlnet_aux (Fannovel16), NormalCrafter (Binyr/AIWarper), WanAnimatePreprocess (Kijai)"
  )

except ImportError:
  logger.warning("Not running in ComfyUI - routes not registered")


# ============================================================================
# Standalone Testing
# ============================================================================

if __name__ == "__main__":
  import argparse

  logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
  )

  parser = argparse.ArgumentParser(description="ComfyUI Preprocessors")
  parser.add_argument("--list", action="store_true", help="List all preprocessors")
  parser.add_argument("--categories", action="store_true", help="List by category")
  parser.add_argument("--info", type=str, help="Get info for a preprocessor")
  parser.add_argument("--attribution", action="store_true", help="Show attribution")

  args = parser.parse_args()

  if args.list:
    print(json.dumps(get_preprocessor_list(), indent=2))
  elif args.categories:
    print(json.dumps(get_preprocessors_by_category(), indent=2))
  elif args.attribution:
    print(json.dumps(get_attribution(), indent=2))
  elif args.info:
    if args.info in PREPROCESSOR_REGISTRY:
      print(json.dumps(PREPROCESSOR_REGISTRY[args.info], indent=2, default=str))
    else:
      print(f"Unknown preprocessor: {args.info}")
  else:
    print(f"\nTotal preprocessors: {len(PREPROCESSOR_REGISTRY)}")
    print("\nBy category:")
    for cat in PreprocessorCategory:
      count = sum(1 for p in PREPROCESSOR_REGISTRY.values() if p["category"] == cat)
      if count > 0:
        print(f"  {cat.value}: {count}")
    print("\n" + "=" * 60)
    print("ATTRIBUTION:")
    print("=" * 60)
    for source in SOURCE_ATTRIBUTION.values():
      print(f"\n{source['name']}")
      print(f"  Author: {source['author']}")
      print(f"  Repo: {source['repo']}")
      print(f"  License: {source['license']}")
