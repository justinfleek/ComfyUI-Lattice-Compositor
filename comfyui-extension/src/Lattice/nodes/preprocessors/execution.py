"""Preprocessor execution functions."""

import base64
import hashlib
import json
import logging
import uuid

from .attribution import SOURCE_ATTRIBUTION
from .registry import PREPROCESSOR_REGISTRY
from .types import JSONValue

logger = logging.getLogger("comfyui.preprocessors")


def _create_preprocessor_workflow(
  preprocessor_id: str, image_path: str, options: dict[str, JSONValue]
) -> dict[str, JSONValue]:
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
  options: dict[str, JSONValue] | None = None,
  server_address: str = "127.0.0.1:8188",
) -> dict[str, JSONValue]:
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
  # Use UUID5 (deterministic) instead of UUID4 (random)
  # Generate deterministic client_id from preprocessor_id and image hash
  image_hash = hashlib.sha256(image_data).hexdigest()[:16]  # Use first 16 chars of hash
  namespace = uuid.UUID('6ba7b810-9dad-11d1-80b4-00c04fd430c8')  # DNS namespace UUID
  name = f"{preprocessor_id}:{image_hash}"
  client_id = str(uuid.uuid5(namespace, name))

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
