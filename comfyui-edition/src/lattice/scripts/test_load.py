import os
from pathlib import Path


os.environ["HF_HOME"] = r"D:\HuggingFace"

import torch


print(f"PyTorch: {torch.__version__}")
print(f"CUDA: {torch.cuda.is_available()}")
print(f"cuDNN: {torch.backends.cudnn.version()}")

# Try loading just the transformer component
import gc

from safetensors.torch import load_file


model_path = r"D:\HuggingFace\hub\models--Qwen--Qwen-Image-Layered\snapshots\8f0ca708dfff6ba1dd5f2d85d78f8c108a040bcf\transformer"

print("\nLoading transformer shards one by one:")
for i in range(1, 6):
  fname = f"diffusion_pytorch_model-{i:05d}-of-00005.safetensors"
  fpath = Path(model_path) / fname
  size = fpath.stat().st_size / 1024**3
  print(f"Loading {fname} ({size:.1f} GB)...", end=" ", flush=True)
  try:
    data = load_file(fpath, device="cuda")
    print(f"OK - {len(data)} tensors, {sum(t.numel() for t in data.values()) / 1e9:.1f}B params")
    del data
    torch.cuda.empty_cache()
    gc.collect()
  except Exception as e:
    print(f"FAILED: {e}")

print("\nDone!")
