"""Preprocessor registry part 1: DEPTH, NORMAL, POSE, VIDEO POSE."""

from .types import JSONValue, PreprocessorCategory

# Part 1: DEPTH, NORMAL, POSE, VIDEO POSE
REGISTRY_PART1: dict[str, dict[str, JSONValue]] = {
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  #                                                                     // depth
  # ════════════════════════════════════════════════════════════════════════════
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
  # ════════════════════════════════════════════════════════════════════════════
  #                                                                    // normal
  # ════════════════════════════════════════════════════════════════════════════
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
  # ════════════════════════════════════════════════════════════════════════════
  #                                                             // normalcrafter
  # Video-to-Normal diffusion model - temporally consistent normal sequences
  # ════════════════════════════════════════════════════════════════════════════
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
  # ════════════════════════════════════════════════════════════════════════════
  #                                                                      // pose
  # ════════════════════════════════════════════════════════════════════════════
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
  # ════════════════════════════════════════════════════════════════════════════
  #                                                             // video // pose
  # For Wan 2.2 video animation preprocessing
  # ════════════════════════════════════════════════════════════════════════════
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
}
