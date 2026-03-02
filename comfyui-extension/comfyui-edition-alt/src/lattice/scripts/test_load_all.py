import os
from pathlib import Path


os.environ["HF_HOME"] = r"D:\HuggingFace"

import torch


print(f"PyTorch: {torch.__version__}")
print(f"CUDA: {torch.cuda.is_available()}")


from safetensors.torch import load_file


model_path = r"D:\HuggingFace\hub\models--Qwen--Qwen-Image-Layered\snapshots\8f0ca708dfff6ba1dd5f2d85d78f8c108a040bcf\transformer"

print("\nLoading ALL transformer shards to GPU at once:")
all_tensors = {}
for i in range(1, 6):
  fname = f"diffusion_pytorch_model-{i:05d}-of-00005.safetensors"
  fpath = Path(model_path) / fname
  print(f"Loading {fname}...", flush=True)
  data = load_file(fpath, device="cuda")
  all_tensors.update(data)
  print(
    f"  Total tensors: {len(all_tensors)}, GPU mem: {torch.cuda.memory_allocated() / 1024**3:.1f} GB"
  )

print(f"\nTotal: {len(all_tensors)} tensors")
print(f"GPU memory used: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")
print(f"GPU memory reserved: {torch.cuda.memory_reserved() / 1024**3:.1f} GB")

# Clean up
del all_tensors
torch.cuda.empty_cache()
print("\nCleared GPU memory")
print(f"GPU memory after cleanup: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")
