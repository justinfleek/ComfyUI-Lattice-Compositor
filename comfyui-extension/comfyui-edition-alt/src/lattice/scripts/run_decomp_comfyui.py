#!/usr/bin/env python3
"""
Run Qwen-Image-Layered decomposition using ComfyUI's Python environment.

This script runs with GPU acceleration on the RTX 5090.
"""

import os
import sys
import time
from pathlib import Path


# Use D: drive for HuggingFace cache (C: is out of space)
os.environ["HF_HOME"] = r"D:\HuggingFace"
os.environ["HUGGINGFACE_HUB_CACHE"] = r"D:\HuggingFace\hub"
os.environ["TRANSFORMERS_CACHE"] = r"D:\HuggingFace\transformers"

# Use Windows paths since this runs in ComfyUI's Windows Python
PROJECT_ROOT = Path(r"C:\Users\justi\Desktop\Compositor")
SCREENSHOTS_DIR = PROJECT_ROOT / "screenshots"
OUTPUT_DIR = SCREENSHOTS_DIR / "decomp"


def main():
  print("=" * 60)
  print("Qwen-Image-Layered Decomposition Test")
  print("Using ComfyUI Python with RTX 5090 GPU")
  print("=" * 60)
  print()

  # Import after banner
  # Enable better error messages
  import traceback

  import torch
  from PIL import Image

  try:
    from diffusers import QwenImageLayeredPipeline
  except ImportError as e:
    print(f"ERROR importing QwenImageLayeredPipeline: {e}")
    traceback.print_exc()
    sys.exit(1)

  # Check GPU
  print(f"CUDA available: {torch.cuda.is_available()}")
  if torch.cuda.is_available():
    print(f"GPU: {torch.cuda.get_device_name(0)}")
    gpu_mem = torch.cuda.get_device_properties(0).total_memory / (1024**3)
    print(f"VRAM: {gpu_mem:.1f} GB")
  else:
    print("ERROR: No GPU available!")
    sys.exit(1)
  print()

  # Find test images (exclude screenshots and utility images)
  test_images = []
  exclude_patterns = ["current_", "screenshot", "ui_"]
  for item_path in SCREENSHOTS_DIR.iterdir():
    if item_path.is_file() and item_path.suffix.lower() in (".jpg", ".jpeg", ".png", ".webp"):
      # Skip utility images
      if any(p in item_path.name.lower() for p in exclude_patterns):
        continue
      test_images.append(str(item_path))

  if not test_images:
    print(f"ERROR: No test images found in {SCREENSHOTS_DIR}")
    sys.exit(1)

  print(f"Found {len(test_images)} test images:")
  for img in test_images:
    print(f"  - {Path(img).name}")
  print()

  # Create output directory
  OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
  print(f"Output directory: {OUTPUT_DIR}")
  print()

  # Load model
  print("Loading Qwen-Image-Layered model...")
  print("(First run downloads ~28GB from HuggingFace)")
  print()
  start = time.time()

  try:
    # Clear any cached memory first
    torch.cuda.empty_cache()
    import gc

    gc.collect()

    print("Loading model to CPU first, then moving to GPU...")
    print(
      f"Available GPU memory: {torch.cuda.get_device_properties(0).total_memory / 1024**3:.1f} GB"
    )

    # Load to CPU first, then move to GPU
    pipe = QwenImageLayeredPipeline.from_pretrained(
      "Qwen/Qwen-Image-Layered",
      torch_dtype=torch.float16,  # Use float16 instead of bfloat16
    )
    print("Model loaded to CPU, moving to GPU...")
    sys.stdout.flush()

    pipe = pipe.to("cuda")
    pipe.set_progress_bar_config(disable=None)
    print("Model moved to GPU successfully!")

    # Report memory usage
    print(f"GPU memory used: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")
  except Exception as e:
    print(f"ERROR loading model: {e}")
    traceback.print_exc()
    sys.exit(1)

  load_time = time.time() - start
  print(f"Model loaded in {load_time:.1f}s")
  print()

  # Process each image
  for i, image_path in enumerate(test_images):
    print("=" * 60)
    print(f"Processing {i + 1}/{len(test_images)}: {Path(image_path).name}")
    print("=" * 60)

    # Load image
    image = Image.open(image_path).convert("RGBA")
    print(f"Image size: {image.size}")

    # Decomposition parameters
    num_layers = 5
    inputs = {
      "image": image,
      "generator": torch.Generator(device="cuda").manual_seed(42 + i),
      "true_cfg_scale": 4.0,
      "negative_prompt": " ",
      "num_inference_steps": 50,
      "num_images_per_prompt": 1,
      "layers": num_layers,
      "resolution": 640,
      "cfg_normalize": True,
      "use_en_prompt": True,
    }

    # Run decomposition
    print(f"Running decomposition into {num_layers} layers...")
    start = time.time()

    with torch.inference_mode():
      output = pipe(**inputs)
      layers = output.images[0]

    inference_time = time.time() - start
    print(f"Decomposition complete in {inference_time:.1f}s")
    print(f"Generated {len(layers)} layers")

    # Save layers
    input_name = Path(image_path).stem
    print("Saving layers:")
    for j, layer in enumerate(layers):
      if layer.mode != "RGBA":
        layer = layer.convert("RGBA")

      if j == 0:
        label = "background"
      elif j == len(layers) - 1:
        label = "foreground"
      else:
        label = f"layer_{j + 1}"

      output_path = OUTPUT_DIR / f"{input_name}_layer_{j:02d}_{label}.png"
      layer.save(output_path, format="PNG")
      size_kb = output_path.stat().st_size / 1024
      print(f"  [{j + 1}/{len(layers)}] {output_path.name} ({size_kb:.1f} KB)")

    print()

  # Summary
  print("=" * 60)
  print("DECOMPOSITION COMPLETE!")
  print("=" * 60)
  print()
  print(f"Output saved to: {OUTPUT_DIR}")
  print()
  print("Generated files:")
  for path in sorted(OUTPUT_DIR.iterdir()):
    if path.is_file() and path.suffix == ".png":
      size_kb = path.stat().st_size / 1024
      print(f"  {path.name} ({size_kb:.1f} KB)")
  print()
  print("SUCCESS: End-to-end test passed!")


if __name__ == "__main__":
  main()
