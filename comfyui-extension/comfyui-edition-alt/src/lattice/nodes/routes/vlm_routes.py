"""Vision Language Model routes for motion intent analysis."""

import base64
import io
import json
import re
from pathlib import Path

import torch
from aiohttp import web
from PIL import Image as PILImage

from .common import routes

if routes is not None:

  _vlm_model = None
  _vlm_processor = None
  _vlm_model_name = None

  # System prompt for motion intent analysis
  VLM_SYSTEM_PROMPT = """You are a motion graphics expert analyzing images for camera movements and animation paths.

Given an image, suggest motion paths and camera trajectories that would create compelling visual effects.

ALWAYS respond in valid JSON format with this structure:
{
  "description": "Brief description of suggested motion",
  "confidence": 0.0-1.0,
  "cameraIntents": [
    {
      "type": "dolly|truck|pedestal|pan|tilt|roll|orbit|drift|handheld|crane|zoom|follow_path",
      "intensity": "very_subtle|subtle|medium|strong|dramatic",
      "axis": "x|y|z|all",
      "durationFrames": 81,
      "suggestedEasing": "linear|easeIn|easeOut|easeInOut|bounce|elastic"
    }
  ],
  "splineIntents": [
    {
      "usage": "camera_path|emitter_path|text_path|layer_path",
      "smoothness": 0.8,
      "complexity": 4,
      "worldSpace": true,
      "suggestedPoints": [
        {"id": "p1", "x": 100, "y": 200, "depth": 0.5, "handleIn": null, "handleOut": null, "type": "smooth"}
      ],
      "closed": false
    }
  ],
  "layerIntents": [
    {
      "motionType": "parallax|float|sway|breathe|drift|noise|pulse|rotate|follow_path",
      "amplitude": 10,
      "frequency": 0.5
    }
  ]
}

Consider:
- Depth information if available (closer = lower depth values)
- Subject positions and focal points
- Natural motion paths that follow scene geometry
- Parallax opportunities based on depth layers
"""

  def _load_vlm_model(model_name="qwen2-vl"):
    """
    Lazy load Qwen-VL model for vision-language tasks.

    Looks for models in:
    1. ComfyUI/models/LLM/Qwen-VL/
    2. ComfyUI custom nodes (ComfyUI-QwenVL or ComfyUI_Qwen3-VL-Instruct)
    3. HuggingFace cache (auto-download)
    """
    global _vlm_model, _vlm_processor, _vlm_model_name

    if _vlm_model is not None and _vlm_model_name == model_name:
      return _vlm_model, _vlm_processor

    try:
      from transformers import AutoModelForVision2Seq, AutoProcessor

      # Determine model path
      model_path = None

      # Check ComfyUI models folder first
      try:
        import folder_paths

        llm_folders = (
          folder_paths.get_folder_paths("LLM") if hasattr(folder_paths, "get_folder_paths") else []
        )

        for folder in llm_folders:
          # Look for Qwen-VL variants
          for variant in ["Qwen2-VL-7B-Instruct", "Qwen2-VL-2B-Instruct", "Qwen-VL", "Qwen3-VL-8B"]:
            check_path = Path(folder) / variant
            if check_path.exists():
              model_path = str(check_path)
              print(f"[Lattice VLM] Found local model at {model_path}")
              break
          if model_path:
            break
      except ImportError:
        pass

      # Check standard model locations
      if not model_path:
        standard_paths = [
          Path.home() / ".cache/huggingface/hub/models--Qwen--Qwen2-VL-7B-Instruct",
          Path("/models/Qwen2-VL-7B-Instruct"),
          Path("../models/LLM/Qwen2-VL-7B-Instruct"),
        ]
        for path in standard_paths:
          if path.exists():
            model_path = str(path)
            break

      # Fall back to HuggingFace model ID (will download)
      if not model_path:
        if model_name in ["qwen2-vl", "qwen2.5-vl"]:
          model_path = "Qwen/Qwen2-VL-7B-Instruct"
        elif model_name == "qwen3-vl":
          model_path = "Qwen/Qwen3-VL-8B"
        else:
          model_path = "Qwen/Qwen2-VL-2B-Instruct"  # Smaller default
        print(f"[Lattice VLM] Using HuggingFace model: {model_path}")

      # Load model and processor
      device = "cuda" if torch.cuda.is_available() else "cpu"
      dtype = torch.float16 if device == "cuda" else torch.float32

      print(f"[Lattice VLM] Loading {model_path} on {device}...")

      #                                                                  // security
      # from downloaded models. If a model requires custom code, it must be
      # audited and added to an allowlist, or use a safe alternative.
      # See AUDIT/SECURITY_ARCHITECTURE.md for details.
      _vlm_processor = AutoProcessor.from_pretrained(model_path, trust_remote_code=False)
      _vlm_model = AutoModelForVision2Seq.from_pretrained(
        model_path,
        torch_dtype=dtype,
        device_map="auto" if device == "cuda" else None,
        trust_remote_code=False,
      )

      if device == "cpu":
        _vlm_model = _vlm_model.to(device)

      _vlm_model_name = model_name
      print("[Lattice VLM] Model loaded successfully")

      return _vlm_model, _vlm_processor

    except Exception as e:
      print(f"[Lattice VLM] Failed to load model: {e}")
      import traceback

      traceback.print_exc()
      return None, None

  @routes.post("/lattice/vlm")
  async def analyze_with_vlm(request):
    """
    Analyze image using Qwen-VL for motion intent suggestions.

    Request body:
    {
        "image": "base64_encoded_png",
        "prompt": "User's motion description or request",
        "model": "qwen2-vl" | "qwen3-vl" | "qwen-vl",
        "max_tokens": 2048,
        "temperature": 0.7
    }

    Returns:
    {
        "status": "success",
        "response": "Raw model response text",
        "parsed": { ... structured intent if JSON parseable ... },
        "model": "qwen2-vl"
    }
    """
    try:
      data = await request.json()

      model_name = data.get("model", "qwen2-vl")
      max_tokens = data.get("max_tokens", 2048)
      temperature = data.get("temperature", 0.7)
      user_prompt = data.get(
        "prompt", "Analyze this image and suggest compelling camera movements and animation paths."
      )

      # Load model
      model, processor = _load_vlm_model(model_name)

      if model is None or processor is None:
        return web.json_response(
          {
            "status": "error",
            "message": "VLM model not available. Please install Qwen-VL or configure model path.",
            "fallback": True,
            "response": None,
          },
          status=503,
        )

      # Decode image if provided
      image = None
      if data.get("image"):
        image_data = base64.b64decode(data["image"])
        image = PILImage.open(io.BytesIO(image_data)).convert("RGB")

      # Construct messages for the model
      messages = []

      if image:
        # Vision + text input
        content = [
          {"type": "image", "image": image},
          {"type": "text", "text": f"{VLM_SYSTEM_PROMPT}\n\nUser request: {user_prompt}"},
        ]
      else:
        # Text-only input
        content = [{"type": "text", "text": f"{VLM_SYSTEM_PROMPT}\n\nUser request: {user_prompt}"}]

      messages.append({"role": "user", "content": content})

      # Process input
      text_input = processor.apply_chat_template(
        messages, tokenize=False, add_generation_prompt=True
      )

      if image:
        inputs = processor(text=[text_input], images=[image], return_tensors="pt", padding=True)
      else:
        inputs = processor(text=[text_input], return_tensors="pt", padding=True)

      # Move to device
      device = next(model.parameters()).device
      inputs = {k: v.to(device) for k, v in inputs.items()}

      # Generate response
      with torch.no_grad():
        outputs = model.generate(
          **inputs,
          max_new_tokens=max_tokens,
          do_sample=temperature > 0,
          temperature=temperature if temperature > 0 else None,
          pad_token_id=processor.tokenizer.pad_token_id,
          eos_token_id=processor.tokenizer.eos_token_id,
        )

      # Decode response
      response_text = processor.decode(outputs[0], skip_special_tokens=True)

      # Try to extract just the assistant response
      if "assistant" in response_text.lower():
        response_text = response_text.split("assistant")[-1].strip()

      # Remove any leading/trailing markers
      response_text = response_text.strip()
      if response_text.startswith(":"):
        response_text = response_text[1:].strip()

      # Try to parse as JSON
      parsed = None
      try:
        # Find JSON in response
        json_match = re.search(r"\{[\s\S]*\}", response_text)
        if json_match:
          parsed = json.loads(json_match.group())
      except (json.JSONDecodeError, AttributeError):
        pass

      return web.json_response(
        {"status": "success", "response": response_text, "parsed": parsed, "model": model_name}
      )

    except Exception as e:
      import traceback

      traceback.print_exc()
      return web.json_response({"status": "error", "message": str(e)}, status=500)

  @routes.get("/lattice/vlm/status")
  async def vlm_status(request):
    """Check VLM model status and available models."""
    try:
      # Check for available models
      available_models = []

      try:
        import folder_paths

        llm_folders = (
          folder_paths.get_folder_paths("LLM") if hasattr(folder_paths, "get_folder_paths") else []
        )

        for folder in llm_folders:
          folder_path = Path(folder)
          if folder_path.exists():
            available_models.extend(
              [
                {"name": item_path.name, "path": str(item_path), "local": True}
                for item_path in folder_path.iterdir()
                if item_path.is_dir() and "qwen" in item_path.name.lower()
              ]
            )
      except ImportError:
        pass

      # Check if transformers is available
      transformers_available = False
      try:
        import transformers

        transformers_available = True
      except ImportError:
        pass

      return web.json_response(
        {
          "status": "success",
          "cuda_available": torch.cuda.is_available(),
          "cuda_device": torch.cuda.get_device_name(0) if torch.cuda.is_available() else None,
          "transformers_available": transformers_available,
          "model_loaded": _vlm_model is not None,
          "current_model": _vlm_model_name,
          "available_models": available_models,
          "huggingface_models": [
            {"name": "Qwen2-VL-2B-Instruct", "id": "Qwen/Qwen2-VL-2B-Instruct", "vram": "~6GB"},
            {"name": "Qwen2-VL-7B-Instruct", "id": "Qwen/Qwen2-VL-7B-Instruct", "vram": "~16GB"},
            {"name": "Qwen3-VL-8B", "id": "Qwen/Qwen3-VL-8B", "vram": "~18GB"},
          ],
        }
      )

    except Exception as e:
      return web.json_response({"status": "error", "message": str(e)}, status=500)
