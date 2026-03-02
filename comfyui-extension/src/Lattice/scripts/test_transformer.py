import os


os.environ["HF_HOME"] = r"D:\HuggingFace"

import torch


print(f"PyTorch: {torch.__version__}")
print(f"CUDA: {torch.cuda.is_available()}")
print(f"GPU: {torch.cuda.get_device_name(0)}")

# Use the correct model class
from diffusers.models import QwenImageTransformer2DModel


model_path = r"D:\HuggingFace\hub\models--Qwen--Qwen-Image-Layered\snapshots\8f0ca708dfff6ba1dd5f2d85d78f8c108a040bcf\transformer"

print("\nLoading QwenImageTransformer2DModel to CPU first...")
print("(This needs ~40GB RAM)")

try:
  transformer = QwenImageTransformer2DModel.from_pretrained(
    model_path,
    torch_dtype=torch.bfloat16,
    low_cpu_mem_usage=True,
  )
  print("Loaded to CPU!")
  print("Moving to GPU...")
  transformer = transformer.to("cuda")
  print(f"Success! GPU memory: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")
except Exception as e:
  print(f"Failed: {e}")
  import traceback

  traceback.print_exc()
