"""ComfyUI node for vectorization."""

import io
import json

from PIL import Image

from .constants import VTRACER_AVAILABLE
from .parsing import parse_svg_to_paths

# Import vtracer if available
if VTRACER_AVAILABLE:
  import vtracer


class LatticeVectorizeImage:
  """
  ComfyUI node for vectorizing images to SVG paths.

  Outputs control points compatible with SplineLayer.
  """

  @classmethod
  def INPUT_TYPES(cls):
    return {
      "required": {
        "image": ("IMAGE",),
        "mode": (["spline", "polygon", "pixel"], {"default": "spline"}),
        "color_mode": (["color", "binary"], {"default": "color"}),
        "filter_speckle": ("INT", {"default": 4, "min": 0, "max": 100}),
        "corner_threshold": ("INT", {"default": 60, "min": 0, "max": 180}),
        "path_precision": ("INT", {"default": 3, "min": 1, "max": 8}),
      }
    }

  RETURN_TYPES = ("STRING", "INT")
  RETURN_NAMES = ("svg_paths_json", "path_count")
  FUNCTION = "vectorize"
  CATEGORY = "Lattice/Vectorization"

  def vectorize(self, image, mode, color_mode, filter_speckle, corner_threshold, path_precision):
    if not VTRACER_AVAILABLE:
      raise RuntimeError("vtracer not installed. Run: pip install vtracer")

    import numpy as np

    # Convert ComfyUI image tensor to PIL
    # ComfyUI images are (B, H, W, C) float32 tensors in range [0, 1]
    img_np = (image[0].cpu().numpy() * 255).astype(np.uint8)
    pil_image = Image.fromarray(img_np)

    width, height = pil_image.size

    # Save to bytes
    img_buffer = io.BytesIO()
    pil_image.save(img_buffer, format="PNG")
    img_bytes = img_buffer.getvalue()

    # Run vtracer
    svg_string = vtracer.convert_raw_image_to_svg(
      img_bytes,
      img_format="png",
      colormode=color_mode,
      mode=mode,
      filter_speckle=filter_speckle,
      corner_threshold=corner_threshold,
      path_precision=path_precision,
    )

    # Parse to paths
    paths = parse_svg_to_paths(svg_string, width, height)

    # Return as JSON string
    result = {
      "paths": paths,
      "width": width,
      "height": height,
    }

    return (json.dumps(result), len(paths))


# Node registration for ComfyUI
NODE_CLASS_MAPPINGS = {
  "LatticeVectorizeImage": LatticeVectorizeImage,
}

NODE_DISPLAY_NAME_MAPPINGS = {
  "LatticeVectorizeImage": "Lattice Vectorize Image",
}
