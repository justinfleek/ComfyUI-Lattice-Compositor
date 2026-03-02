"""Route handlers for decomposition endpoints."""

import base64
import json
import logging
from io import BytesIO

from aiohttp import web
from PIL import Image as PILImage

from .decomposition import decompose_image
from .model_management import (
  download_model,
  get_download_progress,
  get_model_status,
  load_model,
  unload_model,
)
from .model_utils import verify_model_integrity

logger = logging.getLogger("lattice.layer_decomposition")


async def handle_status(request: web.Request) -> web.Response:
  """Get model status for frontend."""
  return web.json_response({"status": "success", "data": get_model_status()})


async def handle_download(request: web.Request) -> web.Response:
  """Download the model (long-running operation)."""
  result = await download_model()
  return web.json_response(result)


async def handle_progress(request: web.Request) -> web.Response:
  """Get current download progress."""
  return web.json_response({"status": "success", "data": get_download_progress()})


async def handle_verify(request: web.Request) -> web.Response:
  """Verify model integrity with hash checks."""
  result = verify_model_integrity(verbose=True)
  return web.json_response(
    {"status": "success" if result["verified"] else "warning", "data": result}
  )


async def handle_load(request: web.Request) -> web.Response:
  """Load model into memory."""
  result = load_model()
  return web.json_response(result)


async def handle_unload(request: web.Request) -> web.Response:
  """Unload model from memory."""
  result = unload_model()
  return web.json_response(result)


async def handle_decompose(request: web.Request) -> web.Response:
  """
  Decompose an image into layers using Qwen-Image-Layered.

  Request body:
  {
      "image": "base64 encoded image",
      "num_layers": 5,
      "true_cfg_scale": 4.0,
      "num_inference_steps": 50,
      "resolution": 640,
      "seed": null
  }

  Response:
  {
      "status": "success",
      "layers": [
          {
              "index": 0,
              "label": "Background",
              "image": "base64 encoded RGBA image"
          },
          ...
      ]
  }
  """
  try:
    data = await request.json()

    # Decode input image
    image_b64 = data.get("image")
    if not image_b64:
      return web.json_response(
        {"status": "error", "message": "Missing 'image' field"}, status=400
      )

    # Handle data URL format
    if "," in image_b64:
      image_b64 = image_b64.split(",")[1]

    image_data = base64.b64decode(image_b64)
    image = PILImage.open(BytesIO(image_data))

    # Get parameters (with backwards compatibility for guidance_scale)
    num_layers = data.get("num_layers", 5)
    true_cfg_scale = data.get("true_cfg_scale", data.get("guidance_scale", 4.0))
    num_inference_steps = data.get("num_inference_steps", 50)
    resolution = data.get("resolution", 640)
    seed = data.get("seed")

    # Run decomposition
    result = decompose_image(
      image,
      num_layers=num_layers,
      true_cfg_scale=true_cfg_scale,
      num_inference_steps=num_inference_steps,
      resolution=resolution,
      seed=seed,
    )

    if result["status"] != "success":
      return web.json_response(result, status=500)

    # Convert layers to base64
    response_layers = []
    for layer_info in result["layers"]:
      layer_img = layer_info["image"]

      # Encode to base64 PNG
      buffer = BytesIO()
      layer_img.save(buffer, format="PNG")
      layer_b64 = base64.b64encode(buffer.getvalue()).decode("utf-8")

      response_layers.append(
        {
          "index": layer_info["index"],
          "label": layer_info["label"],
          "image": f"data:image/png;base64,{layer_b64}",
          "has_alpha": layer_info["has_alpha"],
        }
      )

    return web.json_response(
      {"status": "success", "layers": response_layers, "message": result["message"]}
    )

  except json.JSONDecodeError:
    return web.json_response(
      {"status": "error", "message": "Invalid JSON in request body"}, status=400
    )
  except Exception as e:
    logger.error(f"Decomposition endpoint error: {e}")
    return web.json_response({"status": "error", "message": f"Internal error: {e!s}"}, status=500)
