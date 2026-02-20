# Lattice Compositor - Model Specifications

## Target Models

### Image Generation Models

| Model | Architecture | Parameters | Precision | HuggingFace ID |
|-------|-------------|------------|-----------|----------------|
| Flux 1 Dev | Rectified Flow DiT | 12B | BF16/FP8 | `black-forest-labs/FLUX.1-dev` |
| Flux 2 Dev | Rectified Flow DiT | 12B | BF16/FP8 | `black-forest-labs/FLUX.2-dev` |
| Z-Image Base | DiT | ~2B | FP16/BF16 | TBD |
| Qwen Image 2512 | DiT + MLLM | ~7B | BF16 | `Qwen/Qwen2.5-VL-7B-Instruct` |
| Qwen Image Edit 2511 | DiT + MLLM | ~7B | BF16 | TBD |

### Video Generation Models

| Model | Architecture | Parameters | Precision | HuggingFace ID |
|-------|-------------|------------|-----------|----------------|
| LTX-Video 2B | DiT | 2B | BF16/FP8 | `Lightricks/LTX-Video` |
| LTX-Video 13B | DiT | 13B | BF16/FP8 | `Lightricks/LTX-Video` |
| HunyuanVideo | Dual→Single DiT | 13B+ | BF16/FP8 | `tencent/HunyuanVideo` |
| Wan 2.1 T2V-1.3B | Flow DiT | 1.3B | BF16 | `Wan-AI/Wan2.1-T2V-1.3B` |
| Wan 2.1 T2V-14B | Flow DiT | 14B | BF16 | `Wan-AI/Wan2.1-T2V-14B` |
| Wan 2.1 I2V-14B | Flow DiT | 14B | BF16 | `Wan-AI/Wan2.1-I2V-14B-720P` |
| Wan 2.1 VACE-1.3B | Flow DiT | 1.3B | BF16 | `Wan-AI/Wan2.1-VACE-1.3B` |
| Wan 2.1 VACE-14B | Flow DiT | 14B | BF16 | `Wan-AI/Wan2.1-VACE-14B` |

### 3D Generation Models

| Model | Architecture | Parameters | Precision | HuggingFace ID |
|-------|-------------|------------|-----------|----------------|
| TRELLIS Large | Rectified Flow on SLAT | 1.1B | FP16 | `microsoft/TRELLIS-image-large` |
| Hunyuan3D-2 | Flow DiT + Paint | 1.1B-3B | FP16 | `tencent/Hunyuan3D-2` |

---

## Architecture Details

### 1. FLUX (Image)

**Components:**
- Text Encoder: T5-XXL (4096 dim) + CLIP (768 dim)
- Transformer: Rectified Flow DiT, 12B params
- VAE: 16-channel latent autoencoder

**Tensor Shapes:**
```
T5 Text Encoder:
  input:  [batch, 512] int64
  output: [batch, 512, 4096] bf16

CLIP Text Encoder:
  input:  [batch, 77] int64  
  output: [batch, 768] bf16

DiT Transformer:
  latent:    [batch, 16, H/8, W/8] bf16
  timestep:  [batch] float32
  text_cond: [batch, 512, 4096] bf16
  output:    [batch, 16, H/8, W/8] bf16

VAE Decoder:
  input:  [batch, 16, H/8, W/8] bf16
  output: [batch, 3, H, W] bf16
```

**ONNX Export:**
- Use `optimum-cli export onnx` for text encoders
- Custom export for flow transformer
- NVIDIA pre-exported ONNX available at HuggingFace

---

### 2. LTX-Video (Video)

**Components:**
- Text Encoder: T5
- Transformer: DiT with 3D attention
- VAE: 3D Causal VAE (8x spatial, 8x temporal compression)

**Tensor Shapes:**
```
T5 Text Encoder:
  input:  [batch, seq_len] int64
  output: [batch, seq_len, hidden_dim] bf16

DiT Transformer:
  latent:    [batch, 16, T/8, H/8, W/8] bf16
  timestep:  [batch] float32
  text_cond: [batch, seq_len, hidden_dim] bf16
  output:    [batch, 16, T/8, H/8, W/8] bf16

3D VAE Decoder:
  input:  [batch, 16, T/8, H/8, W/8] bf16
  output: [batch, 3, T, H, W] bf16
```

**Resolution:** 720p (1280x720), up to 4K
**FPS:** 24-30
**Duration:** Up to 60 seconds

---

### 3. HunyuanVideo (Video)

**Components:**
- Text Encoder: MLLM (Decoder-Only) + Bidirectional Refiner
- Transformer: Dual-stream → Single-stream DiT
- VAE: 3D Causal VAE (4x temporal, 8x spatial, 16x channel)

**Tensor Shapes:**
```
MLLM Text Encoder:
  input:  [batch, seq_len] int64
  output: [batch, seq_len, hidden_dim] bf16

Token Refiner:
  input:  [batch, seq_len, hidden_dim] bf16
  output: [batch, seq_len, hidden_dim] bf16

DiT Transformer:
  video_latent: [batch, 16, T/4, H/8, W/8] bf16
  text_tokens:  [batch, text_len, hidden_dim] bf16
  timestep:     [batch] float32
  output:       [batch, 16, T/4, H/8, W/8] bf16

3D VAE Decoder:
  input:  [batch, 16, T/4, H/8, W/8] bf16
  output: [batch, 3, T, H, W] bf16
```

**Memory Requirements:**
- 720p 129f: 60GB VRAM
- 540p 129f: 45GB VRAM
- FP8 saves ~10GB

---

### 4. Wan 2.1/2.2 (Video)

**Components:**
- Text Encoder: T5 (multilingual)
- Transformer: Flow Matching DiT
- VAE: Wan-VAE (3D Causal, 4x temporal, 8x spatial)

**Model Variants:**

| Model | Dimension | FFN Dim | Heads | Layers |
|-------|-----------|---------|-------|--------|
| 1.3B  | 1536      | 8960    | 12    | 30     |
| 14B   | 5120      | 13824   | 40    | 40     |

**Tensor Shapes:**
```
T5 Text Encoder:
  input:  [batch, seq_len] int64
  output: [batch, seq_len, dim] bf16  # dim=1536 or 5120

DiT Transformer (14B):
  latent:    [batch, 16, T, H/8, W/8] bf16
  timestep:  [batch] float32
  text_cond: [batch, seq_len, 5120] bf16
  output:    [batch, 16, T, H/8, W/8] bf16

Wan-VAE Decoder:
  input:  [batch, 16, T, H/8, W/8] bf16
  output: [batch, 3, T*4, H, W] bf16
```

**Resolutions:**
- 480P: 832x480
- 720P: 1280x720

---

### 5. TRELLIS (3D)

**Components:**
- Image Encoder: DINOv2
- Sparse Structure VAE
- SLAT VAE (Gaussian/RF/Mesh decoders)
- Flow Transformers (SS + SLAT)

**Output Formats:**
- 3D Gaussians (for splatting)
- Radiance Fields (NeRF-style)
- Triangle Meshes

**Special Requirements:**
- Sparse convolution ops (spconv)
- Custom rasterizer (diffoctreerast)
- kaolin, nvdiffrast dependencies

---

### 6. Hunyuan3D-2 (3D)

**Components:**
- Hunyuan3D-DiT: Shape generation (Flow-based)
- Hunyuan3D-Paint: Texture synthesis (Diffusion)
- Hunyuan3D-Delight: Image preprocessing

**Variants:**
- DiT-v2-0: 1.1B (Image to Shape)
- DiT-v2-mini: 0.6B (Mini Shape)
- DiT-v2-1: 3.0B (Latest)
- Paint-v2-0: 1.3B (Texture)

**Memory:**
- Shape only: 6GB
- Shape + Texture: 16GB

---

## TensorRT Export Strategy

### Component-wise Export

Each model should be exported as separate ONNX files:

1. **Text Encoder(s)** - Usually straightforward
2. **Transformer/DiT** - Main denoising network, largest component
3. **VAE Decoder** - Latent to pixel space
4. **VAE Encoder** - (Optional, for img2img/vid2vid)

### Dynamic Shapes

Configure optimization profiles for:
- Batch size: 1-4
- Resolution: Multiple presets (480p, 720p, 1080p)
- Sequence length: Variable text length
- Frame count: Variable for video (divisible by 8+1)

### Precision Strategy

| GPU Generation | Recommended |
|----------------|-------------|
| Ampere (A100)  | FP16, INT8  |
| Ada (RTX 4090) | FP16, FP8   |
| Hopper (H100)  | BF16, FP8   |
| Blackwell     | BF16, FP4   |

---

## Directory Structure

```
src/inference/
├── MODELS.md                 # This file
├── CMakeLists.txt           # Build configuration
├── include/
│   ├── safetensors.hpp      # Safetensors loader
│   ├── tensorrt_engine.hpp  # TRT engine wrapper
│   ├── scheduler.hpp        # Diffusion schedulers
│   └── models/
│       ├── flux.hpp
│       ├── ltx_video.hpp
│       ├── hunyuan_video.hpp
│       ├── wan.hpp
│       ├── trellis.hpp
│       └── hunyuan3d.hpp
├── src/
│   ├── safetensors.cpp
│   ├── tensorrt_engine.cpp
│   ├── scheduler.cpp
│   ├── server.cpp           # HTTP API server
│   └── models/
│       └── *.cpp
└── onnx/                    # ONNX export utilities
    ├── export_flux.py
    ├── export_ltx.py
    └── ...
```
