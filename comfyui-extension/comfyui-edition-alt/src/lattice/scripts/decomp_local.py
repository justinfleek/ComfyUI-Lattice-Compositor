"""Run Qwen-Image-Layered decomposition using local FP8 model files."""

import os
from pathlib import Path


os.environ["HF_HOME"] = r"D:\HuggingFace"

import torch


print(f"PyTorch: {torch.__version__}")
print(f"CUDA: {torch.cuda.is_available()}")
print(f"GPU: {torch.cuda.get_device_name(0)}")
print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1024**3:.1f} GB")

# Local model paths
MODEL_PATH = (
  r"C:\Users\justi\Desktop\models\diffusion_models\qwen_image_layered_fp8mixed.safetensors"
)
VAE_PATH = r"C:\Users\justi\Desktop\models\vae\qwen_image_layered_vae.safetensors"

print(f"\nModel: {Path(MODEL_PATH).stat().st_size / 1024**3:.2f} GB")
print(f"VAE: {Path(VAE_PATH).stat().st_size / 1024**3:.2f} GB")

import json

from PIL import Image
from safetensors.torch import load_file


# Load model config
config_path = Path(r"D:\HuggingFace\hub\models--Qwen--Qwen-Image-Layered\snapshots\8f0ca708dfff6ba1dd5f2d85d78f8c108a040bcf\transformer\config.json")
with config_path.open() as f:
  transformer_config = json.load(f)
cfg = {k: v for k, v in transformer_config.items() if not k.startswith("_")}

# Create transformer model
from diffusers.models import QwenImageTransformer2DModel


print("\nCreating transformer model on meta device...")
with torch.device("meta"):
  transformer = QwenImageTransformer2DModel(**cfg)
print(f"Model params: {sum(p.numel() for p in transformer.parameters()) / 1e9:.1f}B")

# Load FP8 weights to CPU first (to avoid GPU OOM during conversion)
print("\nLoading FP8 weights to CPU...")
weights = load_file(MODEL_PATH, device="cpu")
print(f"Loaded {len(weights)} tensors")

# Convert FP8 to FP16 on CPU
print("\nConverting FP8 to FP16 on CPU...")
fp8_count = 0
for k, v in weights.items():
  if v.dtype in (torch.float8_e4m3fn, torch.float8_e5m2):
    weights[k] = v.to(torch.float16)
    fp8_count += 1
print(f"Converted {fp8_count} FP8 tensors to FP16")

# Move model to GPU and load converted weights
print("\nMoving model to GPU...")
transformer = transformer.to_empty(device="cuda", dtype=torch.float16)
print(f"Empty model on GPU: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")

print("Loading weights...")
missing, unexpected = transformer.load_state_dict(weights, strict=False)
print(f"Loaded! Missing: {len(missing)}, Unexpected: {len(unexpected)}")
print(f"GPU memory: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")

# Free CPU weights
del weights
import gc


gc.collect()

# Load VAE
print("\nLoading VAE...")
from diffusers import AutoencoderKL


vae = AutoencoderKL.from_pretrained(
  "Qwen/Qwen-Image-Layered",
  subfolder="vae",
  torch_dtype=torch.float16,
).to("cuda")
print(f"VAE loaded! GPU: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")

# Create pipeline
print("\nCreating pipeline...")
from diffusers import QwenImageLayeredPipeline


pipe = QwenImageLayeredPipeline.from_pretrained(
  "Qwen/Qwen-Image-Layered",
  transformer=transformer,
  vae=vae,
  torch_dtype=torch.float16,
)
print("Pipeline created!")

# Process test image
print("\nProcessing test image...")
image = Image.open(
  r"C:\Users\justi\Desktop\Compositor\screenshots\anime-decomposition-test-2.jpg"
).convert("RGBA")
print(f"Image size: {image.size}")

print("Running decomposition (5 layers)...")
output = pipe(
  image=image,
  generator=torch.Generator(device="cuda").manual_seed(42),
  true_cfg_scale=4.0,
  negative_prompt=" ",
  num_inference_steps=50,
  layers=5,
  resolution=640,
  cfg_normalize=True,
  use_en_prompt=True,
)

# Save layers
output_dir = Path(r"C:\Users\justi\Desktop\Compositor\screenshots\decomp")
output_dir.mkdir(parents=True, exist_ok=True)
for i, layer in enumerate(output.images[0]):
  label = (
    "background"
    if i == 0
    else ("foreground" if i == len(output.images[0]) - 1 else f"layer_{i + 1}")
  )
  path = output_dir / f"anime_layer_{i:02d}_{label}.png"
  layer.convert("RGBA").save(path)
  print(f"Saved: {path.name}")

print("\n" + "=" * 60)
print("SUCCESS!")
print("=" * 60)
