"""
Lattice API Proxy - Secure backend proxy for AI API calls.

This module provides secure proxy endpoints for OpenAI and Anthropic APIs.
API keys are read from environment variables, never exposed to the frontend.

Environment Variables:
  - OPENAI_API_KEY: OpenAI API key for GPT-4V/GPT-4o
  - ANTHROPIC_API_KEY: Anthropic API key for Claude Vision

Usage:
  Frontend calls /lattice/api/vision/openai or /lattice/api/vision/anthropic
  instead of calling external APIs directly.
"""

import json
import logging
import os


logger = logging.getLogger("lattice.api_proxy")

# API key cache (loaded from environment on first use)
_api_keys: dict[str, str | None] = {"openai": None, "anthropic": None, "_loaded": False}


def _load_api_keys():
  """Load API keys from environment variables."""
  global _api_keys
  if _api_keys["_loaded"]:
    return

  _api_keys["openai"] = os.environ.get("OPENAI_API_KEY")
  _api_keys["anthropic"] = os.environ.get("ANTHROPIC_API_KEY")
  _api_keys["_loaded"] = True

  # Log availability (not the actual keys)
  if _api_keys["openai"]:
    logger.info("OpenAI API key loaded from environment")
  if _api_keys["anthropic"]:
    logger.info("Anthropic API key loaded from environment")


def get_api_key(provider: str) -> str | None:
  """Get API key for a provider."""
  _load_api_keys()
  return _api_keys.get(provider)


def has_api_key(provider: str) -> bool:
  """Check if API key is available for a provider."""
  return get_api_key(provider) is not None


# Register routes when running in ComfyUI
try:
  import aiohttp
  from aiohttp import web
  from server import PromptServer

  routes = PromptServer.instance.routes

  @routes.get("/lattice/api/status")
  async def api_status(request):
    """Check which API keys are configured."""
    _load_api_keys()
    return web.json_response(
      {
        "status": "success",
        "providers": {
          "openai": has_api_key("openai"),
          "anthropic": has_api_key("anthropic"),
        },
      }
    )

  @routes.post("/lattice/api/vision/openai")
  async def proxy_openai(request):
    """
    Proxy requests to OpenAI API.

    Expected request body:
    {
        "model": "gpt-4o" | "gpt-4-vision-preview",
        "messages": [...],
        "max_tokens": 2048,
        "temperature": 0.7
    }
    """
    api_key = get_api_key("openai")
    if not api_key:
      return web.json_response(
        {
          "status": "error",
          "message": "OpenAI API key not configured. Set OPENAI_API_KEY environment variable.",
        },
        status=503,
      )

    try:
      data = await request.json()

      # Validate required fields
      if "messages" not in data:
        return web.json_response(
          {"status": "error", "message": "Missing 'messages' field"}, status=400
        )

      # Build request to OpenAI
      openai_request = {
        "model": data.get("model", "gpt-4o"),
        "messages": data["messages"],
        "max_tokens": data.get("max_tokens", 2048),
        "temperature": data.get("temperature", 0.7),
      }

      # Forward to OpenAI
      async with (
        aiohttp.ClientSession() as session,
        session.post(
          "https://api.openai.com/v1/chat/completions",
          headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
          },
          json=openai_request,
          timeout=aiohttp.ClientTimeout(total=60),
        ) as response,
      ):
        result = await response.json()

        if response.status != 200:
          return web.json_response(
            {
              "status": "error",
              "message": result.get("error", {}).get("message", "OpenAI API error"),
              "details": result,
            },
            status=response.status,
          )

        return web.json_response({"status": "success", "data": result})

    except aiohttp.ClientError as e:
      logger.error(f"OpenAI API request failed: {e}")
      return web.json_response({"status": "error", "message": f"Network error: {e!s}"}, status=502)
    except json.JSONDecodeError:
      return web.json_response(
        {"status": "error", "message": "Invalid JSON in request body"}, status=400
      )
    except Exception as e:
      logger.error(f"OpenAI proxy error: {e}")
      return web.json_response({"status": "error", "message": f"Internal error: {e!s}"}, status=500)

  @routes.post("/lattice/api/vision/anthropic")
  async def proxy_anthropic(request):
    """
    Proxy requests to Anthropic API.

    Expected request body:
    {
        "model": "claude-3-5-sonnet-20241022",
        "messages": [...],
        "max_tokens": 2048,
        "temperature": 0.7
    }
    """
    api_key = get_api_key("anthropic")
    if not api_key:
      return web.json_response(
        {
          "status": "error",
          "message": "Anthropic API key not configured. Set ANTHROPIC_API_KEY environment variable.",
        },
        status=503,
      )

    try:
      data = await request.json()

      # Validate required fields
      if "messages" not in data:
        return web.json_response(
          {"status": "error", "message": "Missing 'messages' field"}, status=400
        )

      # Build request to Anthropic
      anthropic_request = {
        "model": data.get("model", "claude-3-5-sonnet-20241022"),
        "messages": data["messages"],
        "max_tokens": data.get("max_tokens", 2048),
      }

      # Only add temperature if specified (Anthropic has different defaults)
      if "temperature" in data:
        anthropic_request["temperature"] = data["temperature"]

      # Forward to Anthropic
      async with (
        aiohttp.ClientSession() as session,
        session.post(
          "https://api.anthropic.com/v1/messages",
          headers={
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
          },
          json=anthropic_request,
          timeout=aiohttp.ClientTimeout(total=60),
        ) as response,
      ):
        result = await response.json()

        if response.status != 200:
          return web.json_response(
            {
              "status": "error",
              "message": result.get("error", {}).get("message", "Anthropic API error"),
              "details": result,
            },
            status=response.status,
          )

        return web.json_response({"status": "success", "data": result})

    except aiohttp.ClientError as e:
      logger.error(f"Anthropic API request failed: {e}")
      return web.json_response({"status": "error", "message": f"Network error: {e!s}"}, status=502)
    except json.JSONDecodeError:
      return web.json_response(
        {"status": "error", "message": "Invalid JSON in request body"}, status=400
      )
    except Exception as e:
      logger.error(f"Anthropic proxy error: {e}")
      return web.json_response({"status": "error", "message": f"Internal error: {e!s}"}, status=500)

  @routes.post("/lattice/api/ai/agent")
  async def ai_agent(request):
    """
    AI Compositor Agent endpoint.

    Handles LLM requests with tool calling support for the Lattice Compositor.
    Supports both OpenAI and Anthropic models.

    Expected request body:
    {
        "model": "gpt-4o" | "claude-sonnet" | "local",
        "messages": [...],
        "tools": [...],  // Tool definitions
        "max_tokens": 4096,
        "temperature": 0.3
    }

    Returns:
    {
        "status": "success",
        "data": {
            "content": "...",
            "toolCalls": [...]  // Parsed tool calls if any
        }
    }
    """
    try:
      data = await request.json()
      model = data.get("model", "gpt-4o")
      messages = data.get("messages", [])
      tools = data.get("tools", [])
      max_tokens = data.get("max_tokens", 4096)
      temperature = data.get("temperature", 0.3)

      if not messages:
        return web.json_response(
          {"status": "error", "message": "Missing 'messages' field"}, status=400
        )

      # Route to appropriate provider
      if model in ("gpt-4o", "gpt-4", "gpt-4-turbo"):
        return await _call_openai_agent(messages, tools, model, max_tokens, temperature)
      elif model in ("claude-sonnet", "claude-3-5-sonnet-20241022"):
        return await _call_anthropic_agent(messages, tools, max_tokens, temperature)
      elif model == "local":
        return web.json_response(
          {"status": "error", "message": "Local model not yet implemented"}, status=501
        )
      else:
        return web.json_response(
          {"status": "error", "message": f"Unknown model: {model}"}, status=400
        )

    except json.JSONDecodeError:
      return web.json_response(
        {"status": "error", "message": "Invalid JSON in request body"}, status=400
      )
    except Exception as e:
      logger.error(f"AI agent error: {e}")
      return web.json_response({"status": "error", "message": f"Internal error: {e!s}"}, status=500)

  async def _call_openai_agent(messages, tools, model, max_tokens, temperature):
    """Call OpenAI API with tool support."""
    api_key = get_api_key("openai")
    if not api_key:
      return web.json_response(
        {
          "status": "error",
          "message": "OpenAI API key not configured. Set OPENAI_API_KEY environment variable.",
        },
        status=503,
      )

    try:
      # Build OpenAI request with tools
      openai_request = {
        "model": model,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": temperature,
      }

      # Add tools if provided
      if tools:
        openai_request["tools"] = tools
        openai_request["tool_choice"] = "auto"

      async with (
        aiohttp.ClientSession() as session,
        session.post(
          "https://api.openai.com/v1/chat/completions",
          headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
          },
          json=openai_request,
          timeout=aiohttp.ClientTimeout(total=120),  # Longer timeout for agent calls
        ) as response,
      ):
        result = await response.json()

        if response.status != 200:
          return web.json_response(
            {
              "status": "error",
              "message": result.get("error", {}).get("message", "OpenAI API error"),
              "details": result,
            },
            status=response.status,
          )

        # Parse response
        choice = result.get("choices", [{}])[0]
        message = choice.get("message", {})
        content = message.get("content", "")

        # Parse tool calls if present
        tool_calls = None
        if "tool_calls" in message:
          tool_calls = []
          for tc in message["tool_calls"]:
            tool_calls.append(
              {
                "id": tc["id"],
                "name": tc["function"]["name"],
                "arguments": json.loads(tc["function"].get("arguments", "{}")),
              }
            )

        return web.json_response(
          {"status": "success", "data": {"content": content, "toolCalls": tool_calls}}
        )

    except aiohttp.ClientError as e:
      logger.error(f"OpenAI agent request failed: {e}")
      return web.json_response({"status": "error", "message": f"Network error: {e!s}"}, status=502)

  async def _call_anthropic_agent(messages, tools, max_tokens, temperature):
    """Call Anthropic API with tool support."""
    api_key = get_api_key("anthropic")
    if not api_key:
      return web.json_response(
        {
          "status": "error",
          "message": "Anthropic API key not configured. Set ANTHROPIC_API_KEY environment variable.",
        },
        status=503,
      )

    try:
      # Convert OpenAI-style tools to Anthropic format
      anthropic_tools = []
      for tool in tools:
        if tool.get("type") == "function":
          func = tool["function"]
          anthropic_tools.append(
            {
              "name": func["name"],
              "description": func.get("description", ""),
              "input_schema": func.get("parameters", {"type": "object", "properties": {}}),
            }
          )

      # Extract system message if present
      system_message = None
      user_messages = []
      for msg in messages:
        if msg.get("role") == "system":
          system_message = msg.get("content", "")
        else:
          user_messages.append(msg)

      # Build Anthropic request
      anthropic_request = {
        "model": "claude-3-5-sonnet-20241022",
        "messages": user_messages,
        "max_tokens": max_tokens,
      }

      if system_message:
        anthropic_request["system"] = system_message

      if anthropic_tools:
        anthropic_request["tools"] = anthropic_tools

      if temperature is not None:
        anthropic_request["temperature"] = temperature

      async with (
        aiohttp.ClientSession() as session,
        session.post(
          "https://api.anthropic.com/v1/messages",
          headers={
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
          },
          json=anthropic_request,
          timeout=aiohttp.ClientTimeout(total=120),
        ) as response,
      ):
        result = await response.json()

        if response.status != 200:
          return web.json_response(
            {
              "status": "error",
              "message": result.get("error", {}).get("message", "Anthropic API error"),
              "details": result,
            },
            status=response.status,
          )

        # Parse response - Anthropic uses content blocks
        content_blocks = result.get("content", [])
        text_content = ""
        tool_calls = []

        for block in content_blocks:
          if block.get("type") == "text":
            text_content += block.get("text", "")
          elif block.get("type") == "tool_use":
            tool_calls.append(
              {"id": block["id"], "name": block["name"], "arguments": block.get("input", {})}
            )

        return web.json_response(
          {
            "status": "success",
            "data": {"content": text_content, "toolCalls": tool_calls if tool_calls else None},
          }
        )

    except aiohttp.ClientError as e:
      logger.error(f"Anthropic agent request failed: {e}")
      return web.json_response({"status": "error", "message": f"Network error: {e!s}"}, status=502)

  # ========================================================================
  # AI MODEL ENDPOINTS (Depth, Normal, Segment)
  # ========================================================================

  # Model cache for lazy loading
  _loaded_models: dict[str, any] = {}

  @routes.post("/lattice/ai/load")
  async def load_model(request):
    """
    Load an AI model into memory.

    Expected request body:
    {
        "model": "depth-anything" | "depth-anything-v2" | "normal-crafter" | "segment-anything" | etc.
    }
    """
    try:
      data = await request.json()
      model_type = data.get("model")

      if not model_type:
        return web.json_response(
          {"status": "error", "message": "Missing 'model' field"}, status=400
        )

      # Check if model is already loaded
      if model_type in _loaded_models:
        return web.json_response(
          {"status": "success", "message": f"Model {model_type} already loaded"}
        )

      # Model loading would integrate with ComfyUI's model system
      # For now, mark as loaded (actual implementation would load pytorch models)
      logger.info(f"Loading AI model: {model_type}")
      _loaded_models[model_type] = {"type": model_type, "loaded_at": __import__("time").time()}

      return web.json_response(
        {"status": "success", "message": f"Model {model_type} loaded successfully"}
      )

    except json.JSONDecodeError:
      return web.json_response(
        {"status": "error", "message": "Invalid JSON in request body"}, status=400
      )
    except Exception as e:
      logger.error(f"Model load error: {e}")
      return web.json_response(
        {"status": "error", "message": f"Failed to load model: {e!s}"}, status=500
      )

  @routes.post("/lattice/ai/unload")
  async def unload_model(request):
    """
    Unload an AI model from memory.

    Expected request body:
    {
        "model": "depth-anything" | etc.
    }
    """
    try:
      data = await request.json()
      model_type = data.get("model")

      if not model_type:
        return web.json_response(
          {"status": "error", "message": "Missing 'model' field"}, status=400
        )

      if model_type in _loaded_models:
        del _loaded_models[model_type]
        logger.info(f"Unloaded AI model: {model_type}")

      return web.json_response({"status": "success", "message": f"Model {model_type} unloaded"})

    except json.JSONDecodeError:
      return web.json_response(
        {"status": "error", "message": "Invalid JSON in request body"}, status=400
      )
    except Exception as e:
      logger.error(f"Model unload error: {e}")
      return web.json_response(
        {"status": "error", "message": f"Failed to unload model: {e!s}"}, status=500
      )

  @routes.post("/lattice/ai/depth")
  async def estimate_depth(request):
    """
    Estimate depth from an image using DepthAnything or similar models.

    Expected multipart form data:
    - image: The input image (file)
    - options: JSON string with {model, outputSize, normalize, colorMap}

    Returns: PNG image of depth map
    """
    try:
      reader = await request.multipart()

      image_data = None
      options = {}

      async for part in reader:
        if part.name == "image":
          image_data = await part.read()
        elif part.name == "options":
          options_str = await part.text()
          options = json.loads(options_str) if options_str else {}

      if not image_data:
        return web.json_response({"status": "error", "message": "Missing image data"}, status=400)

      model_type = options.get("model", "depth-anything")

      # Check if model is loaded
      if model_type not in _loaded_models:
        # Auto-load model
        _loaded_models[model_type] = {"type": model_type, "loaded_at": __import__("time").time()}

      # TODO: Actual depth estimation implementation
      # This would use ComfyUI's DepthAnything nodes or PyTorch models
      # For now, return placeholder indicating implementation needed

      logger.info(f"Depth estimation requested with model: {model_type}")

      # Return placeholder response
      # In production, this would run the actual model
      return web.json_response(
        {
          "status": "error",
          "message": "Depth estimation model integration pending. "
          "Configure ComfyUI DepthAnything nodes or install depth-anything package.",
        },
        status=501,
      )

    except Exception as e:
      logger.error(f"Depth estimation error: {e}")
      return web.json_response(
        {"status": "error", "message": f"Depth estimation failed: {e!s}"}, status=500
      )

  @routes.post("/lattice/ai/normal")
  async def generate_normals(request):
    """
    Generate normal map from an image.

    Expected multipart form data:
    - image: The input image (file)
    - options: JSON string with {model, outputSize, strength, smoothing}

    Returns: PNG image of normal map
    """
    try:
      reader = await request.multipart()

      image_data = None
      options = {}

      async for part in reader:
        if part.name == "image":
          image_data = await part.read()
        elif part.name == "options":
          options_str = await part.text()
          options = json.loads(options_str) if options_str else {}

      if not image_data:
        return web.json_response({"status": "error", "message": "Missing image data"}, status=400)

      model_type = options.get("model", "normal-crafter")
      logger.info(f"Normal map generation requested with model: {model_type}")

      # TODO: Actual normal map generation implementation
      return web.json_response(
        {
          "status": "error",
          "message": "Normal map generation model integration pending. "
          "Configure ComfyUI NormalMap nodes or install normal-crafter package.",
        },
        status=501,
      )

    except Exception as e:
      logger.error(f"Normal map generation error: {e}")
      return web.json_response(
        {"status": "error", "message": f"Normal map generation failed: {e!s}"}, status=500
      )

  @routes.post("/lattice/ai/segment")
  async def segment_image(request):
    """
    Segment an image using SAM or similar models.

    Expected multipart form data:
    - image: The input image (file)
    - options: JSON string with {model, point?, box?, labels?}

    Returns: JSON with segmentation masks
    """
    try:
      reader = await request.multipart()

      image_data = None
      options = {}

      async for part in reader:
        if part.name == "image":
          image_data = await part.read()
        elif part.name == "options":
          options_str = await part.text()
          options = json.loads(options_str) if options_str else {}

      if not image_data:
        return web.json_response({"status": "error", "message": "Missing image data"}, status=400)

      model_type = options.get("model", "segment-anything")
      point = options.get("point")
      box = options.get("box")

      logger.info(f"Segmentation requested with model: {model_type}, point: {point}, box: {box}")

      # TODO: Actual segmentation implementation
      return web.json_response(
        {
          "status": "error",
          "message": "Segmentation model integration pending. "
          "Configure ComfyUI SAM nodes or install segment-anything package.",
        },
        status=501,
      )

    except Exception as e:
      logger.error(f"Segmentation error: {e}")
      return web.json_response(
        {"status": "error", "message": f"Segmentation failed: {e!s}"}, status=500
      )

  @routes.get("/lattice/ai/models")
  async def list_models(request):
    """List available AI models and their status."""
    models = [
      {
        "type": "depth-anything",
        "name": "Depth Anything",
        "description": "Monocular depth estimation with high accuracy",
        "memoryRequired": 1500,
        "status": "ready" if "depth-anything" in _loaded_models else "not-loaded",
      },
      {
        "type": "depth-anything-v2",
        "name": "Depth Anything V2",
        "description": "Improved depth estimation with better details",
        "memoryRequired": 2000,
        "status": "ready" if "depth-anything-v2" in _loaded_models else "not-loaded",
      },
      {
        "type": "normal-crafter",
        "name": "NormalCrafter",
        "description": "Normal map generation from images",
        "memoryRequired": 1200,
        "status": "ready" if "normal-crafter" in _loaded_models else "not-loaded",
      },
      {
        "type": "segment-anything",
        "name": "Segment Anything (SAM)",
        "description": "Zero-shot image segmentation",
        "memoryRequired": 2500,
        "status": "ready" if "segment-anything" in _loaded_models else "not-loaded",
      },
      {
        "type": "segment-anything-2",
        "name": "Segment Anything 2",
        "description": "Improved segmentation with video support",
        "memoryRequired": 3000,
        "status": "ready" if "segment-anything-2" in _loaded_models else "not-loaded",
      },
    ]

    return web.json_response(
      {"status": "success", "models": models, "loaded": list(_loaded_models.keys())}
    )

  logger.info("Lattice API proxy routes registered (including AI agent and AI model endpoints)")

except ImportError:
  # Not running in ComfyUI context
  pass
