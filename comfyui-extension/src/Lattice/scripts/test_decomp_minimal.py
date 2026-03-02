#!/usr/bin/env python3
"""Minimal test script for Qwen-Image-Layered with memory optimization."""

import os
import sys
from pathlib import Path


# Use D: drive for HuggingFace cache
os.environ["HF_HOME"] = r"D:\HuggingFace"
os.environ["HUGGINGFACE_HUB_CACHE"] = r"D:\HuggingFace\hub"

# Memory optimization settings
os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "max_split_size_mb:512"

print("=" * 60)
print("Minimal Qwen-Image-Layered Test")
print("=" * 60)

import gc

import torch


# Clear any cached memory
torch.cuda.empty_cache()
gc.collect()

print(f"CUDA: {torch.cuda.is_available()}")
print(f"GPU: {torch.cuda.get_device_name(0)}")
print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1024**3:.1f} GB")
print()

# Test basic CUDA operations first
print("Testing basic CUDA allocation...")
test_tensor = torch.randn(10000, 10000, device="cuda", dtype=torch.float16)
print(f"Test tensor memory: {test_tensor.element_size() * test_tensor.nelement() / 1024**2:.1f} MB")
del test_tensor
torch.cuda.empty_cache()
print("Basic CUDA test passed!")
print()

# Now try loading the model
print("Loading QwenImageLayeredPipeline...")
from diffusers import QwenImageLayeredPipeline
from PIL import Image


print("Loading model with sequential checkpoint loading...")
sys.stdout.flush()

# Use sequential CPU offload for memory efficiency
pipe = QwenImageLayeredPipeline.from_pretrained(
  "Qwen/Qwen-Image-Layered",
  torch_dtype=torch.float16,
  low_cpu_mem_usage=True,
)

print("Model loaded to CPU successfully!")
print(f"System RAM used: {torch.cuda.memory_allocated() / 1024**3:.2f} GB (should be ~0 on CPU)")

# Enable CPU offload instead of full GPU
print("Enabling sequential CPU offload for memory efficiency...")
pipe.enable_sequential_cpu_offload()
print("CPU offload enabled!")

# Test with a simple image
test_image_path = r"C:\Users\justi\Desktop\Compositor\screenshots\anime-decomposition-test-2.jpg"
print(f"Loading test image: {test_image_path}")
image = Image.open(test_image_path).convert("RGBA")
print(f"Image size: {image.size}")

# Run minimal inference
print("Running decomposition (3 layers, minimal settings)...")
sys.stdout.flush()

inputs = {
  "image": image,
  "generator": torch.Generator(device="cpu").manual_seed(42),
  "true_cfg_scale": 4.0,
  "negative_prompt": " ",
  "num_inference_steps": 20,  # Reduced from 50
  "num_images_per_prompt": 1,
  "layers": 3,  # Minimal layers
  "resolution": 640,
  "cfg_normalize": True,
  "use_en_prompt": True,
}

with torch.inference_mode():
  output = pipe(**inputs)
  layers = output.images[0]

print(f"Generated {len(layers)} layers!")

# Save layers
output_dir = Path(r"C:\Users\justi\Desktop\Compositor\screenshots\decomp")
output_dir.mkdir(parents=True, exist_ok=True)

for i, layer in enumerate(layers):
  path = output_dir / f"test_layer_{i}.png"
  if layer.mode != "RGBA":
    layer = layer.convert("RGBA")
  layer.save(path)
  print(f"Saved: {path}")

print()
print("SUCCESS! Decomposition test passed!")
