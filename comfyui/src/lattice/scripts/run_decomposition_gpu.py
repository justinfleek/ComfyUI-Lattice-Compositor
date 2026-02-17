#!/usr/bin/env python3
"""
Lattice Layer Decomposition GPU Test Script.

This script tests the full layer decomposition workflow on GPU:
1. Loads the Qwen-Image-Layered model (~28GB, auto-downloads from HuggingFace)
2. Processes test images from screenshots/
3. Saves decomposed RGBA layers to screenshots/decomp/

Requirements:
    pip install git+https://github.com/huggingface/diffusers
    pip install transformers>=4.51.3 torch pillow

GPU Requirements:
    - NVIDIA GPU with at least 16GB VRAM (recommended: 24GB)
    - CUDA 11.8+ or 12.x

Usage:
    python scripts/run_decomposition_gpu.py
"""

import logging
import sys
import time
from pathlib import Path


# Setup logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


def check_gpu():
  """Check if CUDA GPU is available."""
  try:
    import torch

    if torch.cuda.is_available():
      gpu_name = torch.cuda.get_device_name(0)
      gpu_memory = torch.cuda.get_device_properties(0).total_memory / (1024**3)
      logger.info(f"GPU detected: {gpu_name} ({gpu_memory:.1f} GB VRAM)")
      return True
    else:
      logger.warning("No CUDA GPU detected!")
      return False
  except ImportError:
    logger.error("PyTorch not installed!")
    return False


def check_dependencies():
  """Check if required packages are installed."""
  missing = []

  try:
    import torch

    logger.info(f"PyTorch version: {torch.__version__}")
  except ImportError:
    missing.append("torch")

  try:
    import diffusers

    logger.info(f"Diffusers version: {diffusers.__version__}")
  except ImportError:
    missing.append("diffusers (install from git)")

  try:
    import transformers

    logger.info(f"Transformers version: {transformers.__version__}")
    # Check version
    version = tuple(map(int, transformers.__version__.split(".")[:2]))
    if version < (4, 51):
      logger.warning(f"Transformers version {transformers.__version__} < 4.51.3 - may have issues")
  except ImportError:
    missing.append("transformers>=4.51.3")

  try:
    from PIL import Image

    logger.info("PIL/Pillow: OK")
  except ImportError:
    missing.append("pillow")

  if missing:
    logger.error(f"Missing packages: {', '.join(missing)}")
    logger.error("Install with:")
    logger.error("  pip install git+https://github.com/huggingface/diffusers")
    logger.error("  pip install transformers>=4.51.3 torch pillow")
    return False

  return True


def run_decomposition():
  """Run the full decomposition test."""
  import torch
  from diffusers import QwenImageLayeredPipeline
  from PIL import Image

  # Paths
  project_root = Path(__file__).parent.parent.parent
  screenshots_dir = project_root / "screenshots"
  output_dir = screenshots_dir / "decomp"

  # Test images
  test_images = [
    screenshots_dir / "anime-decomposition-test-2.jpg",
    screenshots_dir / "nature-photo-for-decomp.webp",
  ]

  # Filter to existing files
  test_images = [img for img in test_images if img.exists()]

  if not test_images:
    logger.error(f"No test images found in {screenshots_dir}")
    return False

  logger.info(f"Found {len(test_images)} test images")

  # Create output directory
  output_dir.mkdir(parents=True, exist_ok=True)

  # Load model
  logger.info("Loading Qwen-Image-Layered model (will download ~28GB on first run)...")
  start_time = time.time()

  pipe = QwenImageLayeredPipeline.from_pretrained(
    "Qwen/Qwen-Image-Layered",
    torch_dtype=torch.bfloat16,
  )
  pipe = pipe.to("cuda")
  pipe.set_progress_bar_config(disable=None)

  load_time = time.time() - start_time
  logger.info(f"Model loaded in {load_time:.1f}s")

  # Process each image
  results = []
  for i, image_path in enumerate(test_images):
    logger.info(f"\n{'=' * 60}")
    logger.info(f"Processing {i + 1}/{len(test_images)}: {image_path.name}")
    logger.info(f"{'=' * 60}")

    # Load image
    image = Image.open(image_path).convert("RGBA")
    logger.info(f"Image size: {image.size}")

    # Prepare inputs
    inputs = {
      "image": image,
      "generator": torch.Generator(device="cuda").manual_seed(42 + i),
      "true_cfg_scale": 4.0,
      "negative_prompt": " ",
      "num_inference_steps": 50,
      "num_images_per_prompt": 1,
      "layers": 5,
      "resolution": 640,
      "cfg_normalize": True,
      "use_en_prompt": True,
    }

    # Run inference
    start_time = time.time()
    with torch.inference_mode():
      output = pipe(**inputs)
      layers = output.images[0]

    inference_time = time.time() - start_time
    logger.info(f"Inference completed in {inference_time:.1f}s - generated {len(layers)} layers")

    # Save layers
    input_name = image_path.stem
    layer_paths = []
    for j, layer in enumerate(layers):
      if layer.mode != "RGBA":
        layer = layer.convert("RGBA")

      # Generate label
      if j == 0:
        label = "background"
      elif j == len(layers) - 1:
        label = "foreground"
      else:
        label = f"layer_{j + 1}"

      output_path = output_dir / f"{input_name}_layer_{j:02d}_{label}.png"
      layer.save(output_path, format="PNG")
      layer_paths.append(output_path)
      logger.info(f"  Saved: {output_path.name}")

    results.append(
      {
        "input": str(image_path),
        "layers": len(layers),
        "output_paths": [str(p) for p in layer_paths],
        "inference_time": inference_time,
      }
    )

  # Summary
  logger.info(f"\n{'=' * 60}")
  logger.info("DECOMPOSITION COMPLETE")
  logger.info(f"{'=' * 60}")
  logger.info(f"Processed {len(results)} images")
  logger.info(f"Output saved to: {output_dir}")

  for result in results:
    logger.info(f"\n{Path(result['input']).name}:")
    logger.info(f"  Layers: {result['layers']}")
    logger.info(f"  Time: {result['inference_time']:.1f}s")

  # List output files
  logger.info("\nGenerated files:")
  for png in sorted(output_dir.glob("*.png")):
    size_kb = png.stat().st_size / 1024
    logger.info(f"  {png.name} ({size_kb:.1f} KB)")

  return True


def main():
  print("=" * 60)
  print("Lattice Layer Decomposition GPU Test")
  print("=" * 60)
  print()

  # Check GPU
  if not check_gpu():
    print("\nThis script requires a CUDA GPU.")
    print("For CPU inference (very slow), use:")
    print("  python nodes/lattice_layer_decomposition.py screenshots/ -o screenshots/decomp")
    sys.exit(1)

  print()

  # Check dependencies
  if not check_dependencies():
    sys.exit(1)

  print()

  # Run decomposition
  try:
    success = run_decomposition()
    sys.exit(0 if success else 1)
  except Exception as e:
    logger.error(f"Decomposition failed: {e}")
    import traceback

    traceback.print_exc()
    sys.exit(1)


if __name__ == "__main__":
  main()
