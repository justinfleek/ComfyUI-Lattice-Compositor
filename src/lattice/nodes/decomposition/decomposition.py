"""Core image decomposition functionality."""

import logging

from .constants import JSONValue, _model_state

logger = logging.getLogger("lattice.layer_decomposition")


def decompose_image(
  image,
  num_layers: int = 5,
  true_cfg_scale: float = 4.0,
  num_inference_steps: int = 50,
  seed: int | None = None,
  resolution: int = 640,
) -> dict[str, JSONValue]:
  """
  Decompose an image into multiple RGBA layers using Qwen-Image-Layered.

  Uses the official QwenImageLayeredPipeline API from diffusers.

  Args:
      image: PIL Image or numpy array
      num_layers: Number of layers to generate (3-8, default 5)
      true_cfg_scale: True CFG scale (default 4.0)
      num_inference_steps: Denoising steps (default 50)
      seed: Random seed for reproducibility
      resolution: Output resolution bucket (640 or 1024, default 640)

  Returns:
      dict with status and layers (list of RGBA PIL Images)
  """
  if not _model_state["loaded"]:
    return {"status": "error", "message": "Model not loaded. Call load_model first."}

  try:
    import numpy as np
    import torch
    from PIL import Image

    pipe = _model_state["pipe"]
    device = _model_state["device"]

    # Convert input to PIL Image if needed
    if isinstance(image, np.ndarray):
      if image.max() <= 1.0:
        image = (image * 255).astype(np.uint8)
      image = Image.fromarray(image)

    # Ensure image is RGBA (required by Qwen-Image-Layered)
    if image.mode != "RGBA":
      image = image.convert("RGBA")

    # Prepare inputs following official API
    inputs = {
      "image": image,
      "true_cfg_scale": true_cfg_scale,
      "negative_prompt": " ",
      "num_inference_steps": num_inference_steps,
      "num_images_per_prompt": 1,
      "layers": num_layers,
      "resolution": resolution,
      "cfg_normalize": True,
      "use_en_prompt": True,
    }

    # Set seed for reproducibility
    if seed is not None:
      inputs["generator"] = torch.Generator(device=device).manual_seed(seed)

    # Run decomposition
    logger.info(f"Decomposing image into {num_layers} layers (resolution={resolution})")

    with torch.inference_mode():
      output = pipe(**inputs)
      # output.images[0] is a list of layer images
      layers = output.images[0] if hasattr(output, "images") else output

    # Convert to list of dicts with metadata
    layer_data = []
    for i, layer in enumerate(layers):
      # Ensure RGBA
      if layer.mode != "RGBA":
        layer = layer.convert("RGBA")

      # Generate semantic label based on position
      label = f"Layer {i + 1}"
      if i == 0:
        label = "Background"
      elif i == len(layers) - 1:
        label = "Foreground"

      layer_data.append(
        {
          "index": i,
          "label": label,
          "image": layer,
          "has_alpha": True,
        }
      )

    logger.info(f"Decomposition complete: {len(layer_data)} layers")
    return {
      "status": "success",
      "layers": layer_data,
      "message": f"Generated {len(layer_data)} layers",
    }

  except Exception as e:
    error_msg = f"Decomposition failed: {e!s}"
    logger.error(error_msg)
    return {"status": "error", "message": error_msg}
