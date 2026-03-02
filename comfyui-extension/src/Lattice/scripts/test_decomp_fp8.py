#!/usr/bin/env python3
"""Test with FP8 quantized model - smaller and faster."""

import os
import sys
from pathlib import Path


# Use D: drive for HuggingFace cache
os.environ["HF_HOME"] = r"D:\HuggingFace"
os.environ["HUGGINGFACE_HUB_CACHE"] = r"D:\HuggingFace\hub"

print("=" * 60)
print("Qwen-Image-Layered FP8 Test")
print("=" * 60)

import gc

import torch


# Clear any cached memory
torch.cuda.empty_cache()
gc.collect()

print(f"CUDA: {torch.cuda.is_available()}")
print(f"GPU: {torch.cuda.get_device_name(0)}")
print(f"Total VRAM: {torch.cuda.get_device_properties(0).total_memory / 1024**3:.1f} GB")
print()

import time

from diffusers import QwenImageLayeredPipeline
from PIL import Image


# Try loading from FP8 quantized version
model_id = "T5B/Qwen-Image-Layered-FP8"
print(f"Loading FP8 model from: {model_id}")
print("(This will download ~20GB on first run)")
sys.stdout.flush()

start = time.time()

try:
  pipe = QwenImageLayeredPipeline.from_pretrained(
    model_id,
    torch_dtype=torch.bfloat16,
  )
  pipe = pipe.to("cuda")
  pipe.set_progress_bar_config(disable=None)
except Exception as e:
  print(f"FP8 model failed: {e}")
  print("Falling back to original model with variant...")
  pipe = QwenImageLayeredPipeline.from_pretrained(
    "Qwen/Qwen-Image-Layered",
    torch_dtype=torch.float16,
    variant="fp16",
  )
  pipe = pipe.to("cuda")
  pipe.set_progress_bar_config(disable=None)

load_time = time.time() - start
print(f"Model loaded in {load_time:.1f}s")
print(f"GPU memory used: {torch.cuda.memory_allocated() / 1024**3:.2f} GB")
print()

# Test image
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

# Save
output_dir = Path(r"C:\Users\justi\Desktop\Compositor\screenshots\decomp")
output_dir.mkdir(parents=True, exist_ok=True)

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
  print(f"Saved: {path.name}")

print()
print("SUCCESS!")
