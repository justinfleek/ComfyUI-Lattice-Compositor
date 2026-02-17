"""Depth estimation routes using DepthAnything V3."""

import base64
import io
from pathlib import Path

import numpy as np
from aiohttp import web
from PIL import Image

from .common import routes

if routes is not None:

  _depth_model = None

  def _load_depth_model(model_name="DA3-LARGE-1.1"):
    """Lazy load Depth Anything V3 model."""
    global _depth_model

    if _depth_model is not None:
      return _depth_model

    try:
      import torch

      # Try loading from depth_anything_3 package (official)
      try:
        from depth_anything_3.api import DepthAnything3

        _depth_model = DepthAnything3.from_pretrained(f"depth-anything/{model_name}")
        device = "cuda" if torch.cuda.is_available() else "cpu"
        _depth_model = _depth_model.to(device=torch.device(device))
        print(f"[Lattice] Loaded DepthAnything V3 ({model_name}) on {device}")
        return _depth_model
      except ImportError:
        pass

      # Try ComfyUI custom nodes path
      try:
        import folder_paths

        da3_path = Path(folder_paths.get_folder_paths("custom_nodes")[0]) / "ComfyUI-DepthAnythingV3"
        if da3_path.exists():
          import sys

          sys.path.insert(0, str(da3_path))
          from depth_anything_v3 import DepthAnythingV3

          _depth_model = DepthAnythingV3(model_name)
          print("[Lattice] Loaded DepthAnything V3 from ComfyUI custom nodes")
          return _depth_model
      except Exception as e:
        print(f"[Lattice] Failed to load from custom nodes: {e}")

      raise ImportError("DepthAnything V3 not available")

    except Exception as e:
      print(f"[Lattice] Failed to load DepthAnything V3: {e}")
      return None

  def _fallback_depth_estimation(pil_image):
    """Fallback depth estimation using grayscale luminance."""
    # Simple fallback: convert to grayscale (not real depth, but placeholder)
    gray = pil_image.convert("L")

    buffer = io.BytesIO()
    gray.save(buffer, format="PNG")
    depth_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

    return web.json_response(
      {
        "status": "success",
        "depth": depth_b64,
        "fallback": True,
        "message": "Using grayscale fallback (DepthAnything V3 not available)",
        "metadata": {"model": "fallback", "width": pil_image.width, "height": pil_image.height},
      }
    )

  @routes.post("/lattice/depth")
  async def generate_depth(request):
    """
    Generate depth map using DepthAnything V3.

    Request body:
    {
        "image": "base64_encoded_png",
        "model": "DA3-LARGE-1.1" | "DA3-GIANT-1.1" | "DA3NESTED-GIANT-LARGE-1.1",
        "return_confidence": false,
        "return_intrinsics": false
    }

    Returns:
    {
        "status": "success",
        "depth": "base64_encoded_png",  // Grayscale depth map
        "confidence": "base64_encoded_png",  // Optional confidence map
        "intrinsics": [[fx, 0, cx], [0, fy, cy], [0, 0, 1]],  // Optional camera intrinsics
        "metadata": {
            "model": "DA3-LARGE-1.1",
            "width": 1024,
            "height": 768
        }
    }
    """
    try:
      data = await request.json()

      # Decode input image
      image_b64 = data.get("image")
      if not image_b64:
        return web.json_response({"status": "error", "message": "No image provided"}, status=400)

      # Decode base64 image
      image_data = base64.b64decode(image_b64)
      pil_image = Image.open(io.BytesIO(image_data)).convert("RGB")

      model_name = data.get("model", "DA3-LARGE-1.1")
      return_confidence = data.get("return_confidence", False)
      return_intrinsics = data.get("return_intrinsics", False)

      # Try to load and run the model
      model = _load_depth_model(model_name)

      if model is not None:
        # Save temp image for inference
        temp_path = "/tmp/lattice_depth_input.png"
        pil_image.save(temp_path)

        # Run inference
        result = model.inference([temp_path])

        # Get depth map
        depth_np = result["depth"][0]  # [H, W] float32

        # Normalize to 0-255 for PNG export
        depth_min = depth_np.min()
        depth_max = depth_np.max()
        depth_normalized = ((depth_np - depth_min) / (depth_max - depth_min + 1e-6) * 255).astype(
          np.uint8
        )

        # Convert to base64
        depth_pil = Image.fromarray(depth_normalized, mode="L")
        buffer = io.BytesIO()
        depth_pil.save(buffer, format="PNG")
        depth_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

        response = {
          "status": "success",
          "depth": depth_b64,
          "metadata": {
            "model": model_name,
            "width": pil_image.width,
            "height": pil_image.height,
            "depth_min": float(depth_min),
            "depth_max": float(depth_max),
          },
        }

        # Optional confidence map
        if return_confidence and "conf" in result:
          conf_np = result["conf"][0]
          conf_normalized = (conf_np * 255).astype(np.uint8)
          conf_pil = Image.fromarray(conf_normalized, mode="L")
          buffer = io.BytesIO()
          conf_pil.save(buffer, format="PNG")
          response["confidence"] = base64.b64encode(buffer.getvalue()).decode("utf-8")

        # Optional camera intrinsics
        if return_intrinsics and "intrinsics" in result:
          response["intrinsics"] = result["intrinsics"][0].tolist()

        return web.json_response(response)

      else:
        # Fallback: Simple MiDaS-style depth estimation
        return _fallback_depth_estimation(pil_image)

    except Exception as e:
      import traceback

      traceback.print_exc()
      return web.json_response({"status": "error", "message": str(e)}, status=500)
