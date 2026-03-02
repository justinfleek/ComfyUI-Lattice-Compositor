"""Route handlers for vectorization endpoints."""

import base64
import io
import traceback
from pathlib import Path

from aiohttp import web
from PIL import Image

from .constants import STARVECTOR_AVAILABLE, STARVECTOR_LOADING, STARVECTOR_MODEL, VTRACER_AVAILABLE
from .parsing import parse_svg_to_paths

# Import vtracer if available
if VTRACER_AVAILABLE:
  import vtracer


async def handle_status(request: web.Request) -> web.Response:
  """Return status of vectorization services."""
  global STARVECTOR_AVAILABLE, STARVECTOR_MODEL, STARVECTOR_LOADING

  # Check if StarVector model exists
  starvector_downloaded = False
  starvector_model_path = ""

  try:
    import folder_paths

    models_dir = folder_paths.models_dir
    starvector_path = f"{models_dir}/starvector/starvector-1b-im2svg"
    starvector_downloaded = Path(starvector_path).exists()
    starvector_model_path = starvector_path
  except Exception:
    pass

  return web.json_response(
    {
      "status": "success",
      "data": {
        "vtracer": {
          "available": VTRACER_AVAILABLE,
          "version": getattr(vtracer, "__version__", "unknown") if VTRACER_AVAILABLE else None,
        },
        "starvector": {
          "available": STARVECTOR_AVAILABLE,
          "downloaded": starvector_downloaded,
          "loaded": STARVECTOR_MODEL is not None,
          "loading": STARVECTOR_LOADING,
          "model_path": starvector_model_path,
          "model_size_gb": 2.5,  # Approximate size of 1B model
        },
      },
    }
  )


async def handle_trace(request: web.Request) -> web.Response:
  """
  Trace a raster image to vector paths using VTracer.

  Request body:
  {
      "image": "data:image/png;base64,...",  // Base64 image
      "mode": "spline",           // "spline" | "polygon" | "pixel"
      "color_mode": "color",      // "color" | "binary"
      "hierarchical": "stacked",  // "stacked" | "cutout"
      "filter_speckle": 4,        // Remove small artifacts (0-100)
      "color_precision": 6,       // Color quantization (1-10)
      "layer_difference": 16,     // Min color difference for layers (1-256)
      "corner_threshold": 60,     // Corner detection (0-180 degrees)
      "length_threshold": 4.0,    // Min path segment length
      "max_iterations": 10,       // Optimization iterations
      "splice_threshold": 45,     // Spline angle threshold
      "path_precision": 3         // Output decimal precision
  }

  Response:
  {
      "status": "success",
      "paths": [...],
      "width": 1920,
      "height": 1080,
      "pathCount": 42
  }
  """
  if not VTRACER_AVAILABLE:
    return web.json_response(
      {"status": "error", "message": "vtracer not installed. Run: pip install vtracer"}, status=503
    )

  try:
    data = await request.json()
    image_data = data.get("image", "")

    # Parse options with defaults
    mode = data.get("mode", "spline")  # spline gives us bezier curves
    color_mode = data.get("color_mode", "color")
    hierarchical = data.get("hierarchical", "stacked")
    filter_speckle = int(data.get("filter_speckle", 4))
    color_precision = int(data.get("color_precision", 6))
    layer_difference = int(data.get("layer_difference", 16))
    corner_threshold = int(data.get("corner_threshold", 60))
    length_threshold = float(data.get("length_threshold", 4.0))
    max_iterations = int(data.get("max_iterations", 10))
    splice_threshold = int(data.get("splice_threshold", 45))
    path_precision = int(data.get("path_precision", 3))

    # Decode image
    if image_data.startswith("data:"):
      # Remove data URL prefix
      image_data = image_data.split(",", 1)[1]

    image_bytes = base64.b64decode(image_data)

    # Load with PIL to get dimensions
    pil_image = Image.open(io.BytesIO(image_bytes))
    width, height = pil_image.size

    # Convert to RGB if needed (vtracer works best with RGB)
    if pil_image.mode == "RGBA":
      # Create white background for alpha
      background = Image.new("RGB", pil_image.size, (255, 255, 255))
      background.paste(pil_image, mask=pil_image.split()[3])
      pil_image = background
    elif pil_image.mode != "RGB":
      pil_image = pil_image.convert("RGB")

    # Save to bytes for vtracer
    img_buffer = io.BytesIO()
    pil_image.save(img_buffer, format="PNG")
    img_bytes = img_buffer.getvalue()

    # Call vtracer
    svg_string = vtracer.convert_raw_image_to_svg(
      img_bytes,
      img_format="png",
      colormode=color_mode,
      hierarchical=hierarchical,
      mode=mode,
      filter_speckle=filter_speckle,
      color_precision=color_precision,
      layer_difference=layer_difference,
      corner_threshold=corner_threshold,
      length_threshold=length_threshold,
      max_iterations=max_iterations,
      splice_threshold=splice_threshold,
      path_precision=path_precision,
    )

    # Parse SVG to extract paths
    paths = parse_svg_to_paths(svg_string, width, height)

    return web.json_response(
      {
        "status": "success",
        "paths": paths,
        "width": width,
        "height": height,
        "pathCount": len(paths),
        "svg": svg_string,  # Include raw SVG for debugging/preview
      }
    )

  except Exception as e:
    traceback.print_exc()
    return web.json_response({"status": "error", "message": str(e)}, status=500)


async def handle_ai_vectorize(request: web.Request) -> web.Response:
  """
  Vectorize an image using StarVector AI.

  Only works for icons/logos/simple graphics.

  Request body:
  {
      "image": "data:image/png;base64,...",
      "max_length": 4000  // Max SVG tokens
  }
  """
  global STARVECTOR_MODEL, STARVECTOR_AVAILABLE

  if not STARVECTOR_AVAILABLE or STARVECTOR_MODEL is None:
    return web.json_response(
      {"status": "error", "message": "StarVector model not loaded. Download and load it first."},
      status=503,
    )

  try:
    data = await request.json()
    image_data = data.get("image", "")
    max_length = int(data.get("max_length", 4000))

    # Decode image
    if image_data.startswith("data:"):
      image_data = image_data.split(",", 1)[1]

    image_bytes = base64.b64decode(image_data)
    pil_image = Image.open(io.BytesIO(image_bytes))
    width, height = pil_image.size

    # Convert to RGB
    if pil_image.mode != "RGB":
      pil_image = pil_image.convert("RGB")

    # Run inference
    from starvector.data.util import process_and_rasterize_svg

    image_tensor = STARVECTOR_MODEL.model.processor(pil_image, return_tensors="pt")["pixel_values"]
    image_tensor = image_tensor.cuda()

    if image_tensor.shape[0] != 1:
      image_tensor = image_tensor.squeeze(0)

    batch = {"image": image_tensor}
    raw_svg = STARVECTOR_MODEL.generate_im2svg(batch, max_length=max_length)[0]

    # Parse SVG to paths
    svg_processed, _ = process_and_rasterize_svg(raw_svg)
    paths = parse_svg_to_paths(svg_processed, width, height)

    return web.json_response(
      {
        "status": "success",
        "paths": paths,
        "width": width,
        "height": height,
        "pathCount": len(paths),
        "svg": svg_processed,
      }
    )

  except Exception as e:
    traceback.print_exc()
    return web.json_response({"status": "error", "message": str(e)}, status=500)


async def handle_download_starvector(request: web.Request) -> web.Response:
  """Download and load StarVector model."""
  global STARVECTOR_MODEL, STARVECTOR_AVAILABLE, STARVECTOR_LOADING

  if STARVECTOR_LOADING:
    return web.json_response(
      {"status": "error", "message": "Model is already being downloaded/loaded"}, status=409
    )

  STARVECTOR_LOADING = True

  try:
    import torch
    from transformers import AutoModelForCausalLM

    model_name = "starvector/starvector-1b-im2svg"

    print(f"[Lattice Vectorize] Downloading StarVector model: {model_name}")

    # Download and load model
    # SECURITY: trust_remote_code=False prevents arbitrary code execution
    # from downloaded models. See AUDIT/SECURITY_ARCHITECTURE.md
    STARVECTOR_MODEL = AutoModelForCausalLM.from_pretrained(
      model_name, torch_dtype=torch.float16, trust_remote_code=False
    )
    STARVECTOR_MODEL.cuda()
    STARVECTOR_MODEL.eval()

    STARVECTOR_AVAILABLE = True
    STARVECTOR_LOADING = False

    print("[Lattice Vectorize] StarVector model loaded successfully")

    return web.json_response(
      {"status": "success", "message": "StarVector model downloaded and loaded"}
    )

  except Exception as e:
    STARVECTOR_LOADING = False
    traceback.print_exc()
    return web.json_response(
      {"status": "error", "message": f"Failed to load StarVector: {e!s}"}, status=500
    )


async def handle_unload_starvector(request: web.Request) -> web.Response:
  """Unload StarVector model to free GPU memory."""
  global STARVECTOR_MODEL, STARVECTOR_AVAILABLE

  if STARVECTOR_MODEL is not None:
    del STARVECTOR_MODEL
    STARVECTOR_MODEL = None
    STARVECTOR_AVAILABLE = False

    # Force garbage collection
    import gc

    gc.collect()

    try:
      import torch

      torch.cuda.empty_cache()
    except Exception:
      pass

    print("[Lattice Vectorize] StarVector model unloaded")

  return web.json_response({"status": "success", "message": "StarVector model unloaded"})
