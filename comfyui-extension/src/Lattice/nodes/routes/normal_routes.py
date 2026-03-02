"""Normal map generation routes."""

import base64
import io
from pathlib import Path

import numpy as np
from aiohttp import web
from PIL import Image
from scipy import ndimage

from .common import routes
from .depth_routes import _load_depth_model

if routes is not None:

  _normal_model = None

  def _load_normal_model():
    """Lazy load NormalCrafter model."""
    global _normal_model

    if _normal_model is not None:
      return _normal_model

    try:
      # Try loading NormalCrafter from ComfyUI custom nodes
      import folder_paths

      nc_path = Path(folder_paths.get_folder_paths("custom_nodes")[0]) / "ComfyUI-NormalCrafterWrapper"
      if nc_path.exists():
        import sys

        sys.path.insert(0, str(nc_path))
        # NormalCrafter loading would go here
        print(f"[Lattice] Found NormalCrafter at {nc_path}")
        # For now, we'll use algebraic depth-to-normal
        return None

    except Exception as e:
      print(f"[Lattice] Failed to load NormalCrafter: {e}")

    return None

  def _depth_to_normal_algebraic(depth_np):
    """
    Convert depth map to normal map using Sobel gradients.

    This is a fast algebraic approach that doesn't require a neural network.
    """
    # Normalize depth to 0-1
    depth = depth_np.astype(np.float32)
    if depth.max() > 1:
      depth = depth / 255.0

    # Compute gradients using Sobel filters
    dz_dx = ndimage.sobel(depth, axis=1)  # Horizontal gradient
    dz_dy = ndimage.sobel(depth, axis=0)  # Vertical gradient

    # Construct normal vectors: N = normalize([-dz/dx, -dz/dy, 1])
    normal = np.zeros((*depth.shape, 3), dtype=np.float32)
    normal[..., 0] = -dz_dx
    normal[..., 1] = -dz_dy
    normal[..., 2] = 1.0

    # Normalize
    norm = np.linalg.norm(normal, axis=2, keepdims=True)
    normal = normal / (norm + 1e-6)

    # Convert from [-1, 1] to [0, 255] for PNG
    normal_uint8 = ((normal + 1) * 0.5 * 255).astype(np.uint8)

    return normal_uint8

  @routes.post("/lattice/normal")
  async def generate_normal(request):
    """
    Generate normal map from image or depth map.

    Request body:
    {
        "image": "base64_encoded_png",  // RGB image
        "depth": "base64_encoded_png",  // Optional: pre-computed depth map
        "method": "algebraic" | "normalcrafter",
        "depth_model": "DA3-LARGE-1.1"  // If depth not provided
    }

    Returns:
    {
        "status": "success",
        "normal": "base64_encoded_png",  // RGB normal map
        "depth": "base64_encoded_png",   // Depth map used (if generated)
        "metadata": {...}
    }
    """
    try:
      data = await request.json()

      method = data.get("method", "algebraic")

      # Get or generate depth map
      depth_np = None

      if data.get("depth"):
        # Use provided depth map
        depth_data = base64.b64decode(data["depth"])
        depth_pil = Image.open(io.BytesIO(depth_data)).convert("L")
        depth_np = np.array(depth_pil)

      elif data.get("image"):
        # Generate depth from image
        image_data = base64.b64decode(data["image"])
        pil_image = Image.open(io.BytesIO(image_data)).convert("RGB")

        # Try DepthAnything V3
        model = _load_depth_model(data.get("depth_model", "DA3-LARGE-1.1"))

        if model is not None:
          temp_path = "/tmp/lattice_normal_input.png"
          pil_image.save(temp_path)
          result = model.inference([temp_path])
          depth_np = result["depth"][0]
        else:
          # Fallback to grayscale
          depth_np = np.array(pil_image.convert("L"))

      else:
        return web.json_response(
          {"status": "error", "message": "No image or depth map provided"}, status=400
        )

      # Generate normal map
      if method == "normalcrafter":
        model = _load_normal_model()
        if model is not None:
          # Use NormalCrafter (not yet implemented)
          pass

      # Default: algebraic depth-to-normal
      normal_np = _depth_to_normal_algebraic(depth_np)

      # Convert to base64 PNG
      normal_pil = Image.fromarray(normal_np, mode="RGB")
      buffer = io.BytesIO()
      normal_pil.save(buffer, format="PNG")
      normal_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

      # Also return depth if we generated it
      depth_b64 = None
      if depth_np is not None:
        depth_normalized = depth_np
        if depth_np.max() > 1:
          depth_normalized = depth_np
        else:
          depth_normalized = (depth_np * 255).astype(np.uint8)

        if depth_normalized.dtype != np.uint8:
          depth_normalized = depth_normalized.astype(np.uint8)

        depth_pil = Image.fromarray(depth_normalized, mode="L")
        buffer = io.BytesIO()
        depth_pil.save(buffer, format="PNG")
        depth_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

      return web.json_response(
        {
          "status": "success",
          "normal": normal_b64,
          "depth": depth_b64,
          "method": method,
          "metadata": {"width": normal_np.shape[1], "height": normal_np.shape[0]},
        }
      )

    except Exception as e:
      import traceback

      traceback.print_exc()
      return web.json_response({"status": "error", "message": str(e)}, status=500)
