#!/usr/bin/env python3
"""Direct GPU loading test for Qwen-Image-Layered - NO CPU offloading."""

import os
import sys
from pathlib import Path


# Use D: drive for HuggingFace cache
os.environ["HF_HOME"] = r"D:\HuggingFace"
os.environ["HUGGINGFACE_HUB_CACHE"] = r"D:\HuggingFace\hub"

print("=" * 60)
print("Qwen-Image-Layered DIRECT GPU Loading Test")
print("=" * 60)

import gc

import torch


# Clear any cached memory
torch.cuda.empty_cache()
gc.collect()

print(f"CUDA: {torch.cuda.is_available()}")
print(f"GPU: {torch.cuda.get_device_name(0)}")
print(f"Total VRAM: {torch.cuda.get_device_properties(0).total_memory / 1024**3:.1f} GB")
print(
  f"Free VRAM: {(torch.cuda.get_device_properties(0).total_memory - torch.cuda.memory_allocated()) / 1024**3:.1f} GB"
)
print()

import time

from diffusers import QwenImageLayeredPipeline
from PIL import Image


print("Loading model DIRECTLY to GPU with bfloat16...")
print("(This should use GPU memory, not CPU!)")
sys.stdout.flush()

start = time.time()

# Load directly to GPU as per official documentation
pipe = QwenImageLayeredPipeline.from_pretrained(
  "Qwen/Qwen-Image-Layered",
  torch_dtype=torch.bfloat16,
)
pipe = pipe.to("cuda")
pipe.set_progress_bar_config(disable=None)

load_time = time.time() - start
print(f"Model loaded in {load_time:.1f}s")
print(f"GPU memory used: {torch.cuda.memory_allocated() / 1024**3:.2f} GB")
print()

# Test with a simple image
test_image_path = r"C:\Users\justi\Desktop\Compositor\screenshots\anime-decomposition-test-2.jpg"
print(f"Loading test image: {test_image_path}")
image = Image.open(test_image_path).convert("RGBA")
print(f"Image size: {image.size}")

# Run decomposition
print("Running decomposition (5 layers)...")
sys.stdout.flush()

start = time.time()
inputs = {
  "image": image,
  "generator": torch.Generator(device="cuda").manual_seed(42),
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

# Save layers
output_dir = Path(r"C:\Users\justi\Desktop\Compositor\screenshots\decomp")
output_dir.mkdir(parents=True, exist_ok=True)

print("Saving layers:")
for i, layer in enumerate(layers):
  if i == 0:
    label = "background"
  elif i == len(layers) - 1:
    label = "foreground"
  else:
    label = f"layer_{i + 1}"

  path = output_dir / f"anime_decomp_layer_{i:02d}_{label}.png"
  if layer.mode != "RGBA":
    layer = layer.convert("RGBA")
  layer.save(path)
  print(f"  {path.name}")

print()
print("=" * 60)
print("SUCCESS! Decomposition complete!")
print(f"Output saved to: {output_dir}")
print("=" * 60)
