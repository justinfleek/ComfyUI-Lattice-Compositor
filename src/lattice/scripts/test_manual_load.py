import os
from pathlib import Path


os.environ["HF_HOME"] = r"D:\HuggingFace"

import json

import torch


print(f"PyTorch: {torch.__version__}")
print(f"CUDA: {torch.cuda.is_available()}")
print(f"GPU: {torch.cuda.get_device_name(0)}")

base_path = r"D:\HuggingFace\hub\models--Qwen--Qwen-Image-Layered\snapshots\8f0ca708dfff6ba1dd5f2d85d78f8c108a040bcf\transformer"

# Load config
print("\nLoading config...")
with (Path(base_path) / "config.json").open() as f:
  config = json.load(f)
print(f"Config: {config}")

# Create model with meta device (no memory)
from diffusers.models import QwenImageTransformer2DModel


print("\nCreating empty model on meta device...")
with torch.device("meta"):
  model = QwenImageTransformer2DModel(**{k: v for k, v in config.items() if not k.startswith("_")})
print("Empty model created!")

# Load weights manually
from safetensors.torch import load_file


print("\nLoading weights to GPU manually...")
state_dict = {}
for i in range(1, 6):
  fname = f"diffusion_pytorch_model-{i:05d}-of-00005.safetensors"
  fpath = Path(base_path) / fname
  print(f"Loading {fname}...")
  shard = load_file(fpath, device="cuda")
  state_dict.update(shard)
  print(f"  Total keys: {len(state_dict)}, GPU: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")

print("\nApplying weights to model...")
# Move model to cuda first
model = model.to_empty(device="cuda", dtype=torch.bfloat16)
model.load_state_dict(state_dict, strict=True)
print("Weights applied!")

print(f"\nFinal GPU memory: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")
print("SUCCESS!")
