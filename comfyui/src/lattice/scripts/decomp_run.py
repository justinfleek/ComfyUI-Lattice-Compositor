import os
from pathlib import Path


os.environ["HF_HOME"] = r"D:\HuggingFace"
os.environ["HUGGINGFACE_HUB_CACHE"] = r"D:\HuggingFace\hub"

import torch


print(f"PyTorch: {torch.__version__}")
print(f"CUDA: {torch.cuda.is_available()}")
print(f"GPU: {torch.cuda.get_device_name(0)}")
print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1024**3:.1f} GB")

from diffusers import QwenImageLayeredPipeline
from diffusers.quantizers import PipelineQuantizationConfig
from PIL import Image


print("\nLoading model with 8-bit quantization...")
quant_config = PipelineQuantizationConfig(
  quant_backend="bitsandbytes_8bit",
  quant_kwargs={"load_in_8bit": True},
)

pipe = QwenImageLayeredPipeline.from_pretrained(
  "Qwen/Qwen-Image-Layered",
  quantization_config=quant_config,
)

print(f"GPU memory after loading: {torch.cuda.memory_allocated() / 1024**3:.1f} GB")

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
print("SUCCESS! Decomposition complete!")
print("=" * 60)
