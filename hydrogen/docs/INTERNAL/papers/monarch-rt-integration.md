# MonarchRT: Integration

**Parent:** [monarch-rt-real-time-video.md](monarch-rt-real-time-video.md)

---

## 6. Performance

### 6.1 Latency Results

| Configuration | Hardware | Latency | FPS | vs Dense |
|--------------|----------|---------|-----|----------|
| Dense FlashAttn | RTX 5090 | 125ms/frame | 8 | 1.0× |
| MonarchRT (TF) | RTX 5090 | 60ms/frame | 16.7 | 2.1× |
| MonarchRT (FT) | RTX 5090 | 36ms/frame | 27.8 | 3.5× |
| Dense FlashAttn | RTX 4090 | 180ms/frame | 5.5 | 1.0× |
| MonarchRT (FT) | RTX 4090 | 65ms/frame | 15.4 | 2.8× |

TF = Training-Free, FT = Fine-Tuned

### 6.2 Quality Metrics (VBench)

| Model | VBench Total | Subject | Background | Motion | Temporal |
|-------|-------------|---------|------------|--------|----------|
| Wan2.1-1.3B (Dense) | 82.3 | 96.2 | 97.1 | 78.4 | 95.8 |
| + Self-Forcing DMD | 81.9 | 95.8 | 96.9 | 78.1 | 95.2 |
| + MonarchRT (TF) | 81.4 | 95.1 | 96.4 | 77.8 | 94.9 |
| + MonarchRT (FT) | 81.8 | 95.7 | 96.8 | 78.0 | 95.1 |

### 6.3 Memory Usage

| Configuration | Attention Memory | Total VRAM | Batch Size |
|--------------|------------------|------------|------------|
| Dense | 12.4 GB | 22.1 GB | 1 |
| MonarchRT | 2.1 GB | 11.8 GB | 1 |
| MonarchRT | 4.2 GB | 13.9 GB | 2 |

### 6.4 Scaling Analysis

```
Dense Attention:     O(N²) memory, O(N²d) compute
MonarchRT (b=√N):    O(N√N) memory, O(N^{3/2}d) compute

For N = 32,760:
  Dense:    ~1.07 billion attention entries
  Monarch:  ~5.9 million effective entries (181× reduction)
```

### 6.5 First Inference Overhead

| Phase | Time | Notes |
|-------|------|-------|
| Kernel compilation | ~2 min | First run only, cached |
| Autotune evaluation | ~30 sec | Per unique config |
| Subsequent runs | 0 | Cached kernels used |

---

## 7. Relation to Lattice

### 7.1 Lattice Video Generation Pipeline

```
┌─────────────────────────────────────────────────────────────────┐
│                     LATTICE PIPELINE                            │
├─────────────────────────────────────────────────────────────────┤
│  User Input ──► Hydrogen UI ──► State × Msg → State × [Cmd]    │
│       │                              │                          │
│       ▼                              ▼                          │
│  Text Prompt              Generation Request                    │
│       │                              │                          │
│       └──────────────┬───────────────┘                          │
│                      ▼                                          │
│              ┌──────────────┐                                   │
│              │  MonarchRT   │  ◄── Real-time preview            │
│              │  DiT Engine  │      16 FPS on RTX 5090           │
│              └──────────────┘                                   │
│                      │                                          │
│                      ▼                                          │
│              ┌──────────────┐                                   │
│              │  VAE Decode  │                                   │
│              └──────────────┘                                   │
│                      │                                          │
│                      ▼                                          │
│              Final Video (480×832, 21 frames)                   │
└─────────────────────────────────────────────────────────────────┘
```

### 7.2 Hydrogen State Management

```purescript
data VideoMsg
  = RequestGeneration TextPrompt
  | GenerationProgress Float
  | GenerationComplete VideoLatents
  | GenerationError String

type VideoState =
  { prompt :: Maybe TextPrompt
  , status :: GenerationStatus
  , preview :: Maybe VideoFrame
  , latents :: Maybe VideoLatents
  }

data VideoCmd
  = StartMonarchGeneration TextPrompt
  | CancelGeneration
  | DecodeLatents VideoLatents
```

### 7.3 libevring Event Pattern

```
State × Event → State × [Operation]

For MonarchRT:
  GeneratorState × ChunkRequest → GeneratorState × [LatentChunk]

Each 21-frame chunk:
  1. Receive ChunkRequest with conditioning
  2. Run 4-step DMD denoising with Monarch attention
  3. Emit LatentChunk operation
  4. Update state with new context
```

### 7.4 Deployment Considerations

**Consumer Hardware:**
- RTX 4090 / 5090: Full real-time generation
- RTX 4080 / 3090: Near real-time (~10 FPS)

**Memory Budget:**
- 12 GB VRAM: Single video generation
- 24 GB VRAM: Batch generation or longer videos

**Determinism:** Same seed + prompt = identical frames

---

## 8. Bibliography

[1] Agarwal et al. "MonarchRT: Efficient Attention for Real-Time Video Generation." arXiv:2602.12271, 2026.

[2] Dao et al. "FlashAttention: Fast and Memory-Efficient Exact Attention." NeurIPS, 2022.

[3] Dao et al. "Monarch: Expressive Structured Matrices for Efficient Training." ICML, 2022.

[4] Chen et al. "Self-Forcing: Bridging Train-Test Gap in Autoregressive Video Diffusion." arXiv, 2026.

[5] Yin et al. "One-step Diffusion with Distribution Matching Distillation." CVPR, 2024.

[6] Wan AI. "Wan2.1: Open Video Generation Models." GitHub, 2025.

[7] Peebles, Xie. "Scalable Diffusion Models with Transformers." ICCV, 2023.

[8] Hafner et al. "Dreamer 4: Training Agents Inside of Scalable World Models." arXiv:2509.24527, 2025.

---

## Appendix: Full Kernel Signatures

```python
# Stage 1 Forward
monarch_rt.al_cl_y_fwd(b, h, a, f, q_frame_start, kv_frame_start,
    curr_q_frames, curr_kv_frames, q, k, v, aL, cL, y, al_cl_y_lse,
    sm_scale_sqrt, Q_FRAME_CHUNK, KV_FRAME_CHUNK, block_b1, block_b2, d,
    CAUSAL_BLOCK_SIZE)

# Stage 2 Forward  
monarch_rt.z_fwd(b, h, a, f, q_frame_start, kv_frame_start,
    curr_q_frames, curr_kv_frames, aL, cL, q, y, z, z_lse, sm_scale_sqrt,
    Q_FRAME_CHUNK, KV_FRAME_CHUNK, block_b1, block_b2, d, IS_FIRST_ITER,
    OUTPUT_FULL_LSE, OUTPUT_PARTIAL_LSE, CAUSAL_BLOCK_SIZE)
```

---

*Part of MonarchRT paper synthesis.*
*Generated: 2026-03-02*
