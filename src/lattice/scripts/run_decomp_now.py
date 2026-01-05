#!/usr/bin/env python3
"""Run Qwen-Image-Layered decomposition on test images."""

import os
import sys
import time


# Fix library path for NixOS
os.environ["LD_LIBRARY_PATH"] = (
  "/nix/store/y3zv94nnbc2nrrsz2q9hfxflw62ccyhl-user-environment/lib:"
  + os.environ.get("LD_LIBRARY_PATH", "")
)

from pathlib import Path

import torch
from diffusers import QwenImageLayeredPipeline
from PIL import Image


def main():
  print("=" * 60)
  print("Qwen-Image-Layered Decomposition Test")
  print("=" * 60)

  # Paths
  project_root = Path(__file__).parent.parent.parent
  screenshots_dir = project_root / "screenshots"
  output_dir = screenshots_dir / "decomp"

  # Test images - use just one for speed
  test_images = [
    screenshots_dir / "nature-photo-for-decomp.webp",
  ]

  test_images = [img for img in test_images if img.exists()]
  if not test_images:
    print("ERROR: No test images found")
    sys.exit(1)

  print(f"Test image: {test_images[0]}")

  # Create output dir
  output_dir.mkdir(parents=True, exist_ok=True)

  # Device and dtype
  device = "cpu"  # No GPU available
  dtype = torch.float32
  print(f"Device: {device} (no GPU - this will take 10-30 minutes)")
  print()

  # Load model
  print("Loading model from HuggingFace (downloading ~28GB on first run)...")
  print("This may take a while...")
  start = time.time()

  pipe = QwenImageLayeredPipeline.from_pretrained(
    "Qwen/Qwen-Image-Layered",
    torch_dtype=dtype,
  )
  pipe = pipe.to(device)

  load_time = time.time() - start
  print(f"Model loaded in {load_time:.1f}s")
  print()

  # Process image
  image_path = test_images[0]
  print(f"Processing: {image_path.name}")

  image = Image.open(image_path).convert("RGBA")
  print(f"Image size: {image.size}")

  # Run inference
  print("Running decomposition (5 layers)...")
  print("This will take 10-30 minutes on CPU...")
  start = time.time()

  inputs = {
    "image": image,
    "generator": torch.Generator(device=device).manual_seed(42),
    "true_cfg_scale": 4.0,
    "negative_prompt": " ",
    "num_inference_steps": 50,
    "num_images_per_prompt": 1,
    "layers": 5,
    "resolution": 640,
    "cfg_normalize": True,
    "use_en_prompt": True,
  }

  with torch.inference_mode():
    output = pipe(**inputs)
    layers = output.images[0]

  inference_time = time.time() - start
  print(f"Decomposition complete in {inference_time:.1f}s")
  print(f"Generated {len(layers)} layers")
  print()

  # Save layers
  input_name = image_path.stem
  print("Saving layers...")
  for j, layer in enumerate(layers):
    if layer.mode != "RGBA":
      layer = layer.convert("RGBA")

    if j == 0:
      label = "background"
    elif j == len(layers) - 1:
      label = "foreground"
    else:
      label = f"layer_{j + 1}"

    output_path = output_dir / f"{input_name}_layer_{j:02d}_{label}.png"
    layer.save(output_path, format="PNG")
    print(f"  Saved: {output_path.name}")

  print()
  print("=" * 60)
  print("DECOMPOSITION COMPLETE!")
  print(f"Output: {output_dir}")
  print("=" * 60)


if __name__ == "__main__":
  main()
