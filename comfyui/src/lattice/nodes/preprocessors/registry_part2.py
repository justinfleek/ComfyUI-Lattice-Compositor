"""Preprocessor registry part 2: EDGE, LINEART, SCRIBBLE, SEGMENTATION, OTHER."""

from .types import JSONValue, PreprocessorCategory

# Part 2: EDGE, LINEART, SCRIBBLE, SEGMENTATION, OTHER
REGISTRY_PART2: dict[str, dict[str, JSONValue]] = {
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
