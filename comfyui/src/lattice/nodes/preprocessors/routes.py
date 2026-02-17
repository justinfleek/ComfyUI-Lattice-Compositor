"""ComfyUI route handlers for preprocessors."""

import base64
import json
import logging

from .attribution import SOURCE_ATTRIBUTION
from .queries import get_attribution, get_preprocessor_list, get_preprocessors_by_category
from .registry import PREPROCESSOR_REGISTRY
from .execution import execute_preprocessor

logger = logging.getLogger("comfyui.preprocessors")

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
