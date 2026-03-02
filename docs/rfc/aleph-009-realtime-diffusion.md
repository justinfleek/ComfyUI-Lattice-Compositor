# ℵ-009: Real-Time Diffusion Pipeline

| Field | Value |
|-------|-------|
| RFC | ℵ-009 |
| Title | Real-Time Diffusion Pipeline |
| Author | Straylight |
| Status | Draft |
| Created | 2026-03-02 |

## Abstract

This RFC specifies the **Real-Time Diffusion Pipeline** for Lattice — an architecture enabling
interactive video generation at 16+ FPS on consumer GPUs. The pipeline combines MonarchRT's
efficient attention with shortcut forcing objectives to achieve quality/speed tradeoffs
configurable at inference time. Users see immediate visual feedback while editing, with
progressive refinement to final quality.

## Motivation

Current video diffusion models require 50-100 denoising steps, taking 10-60 seconds per
generation on high-end GPUs. This latency destroys creative flow:

1. **Broken feedback loop** — Users cannot iterate quickly on prompts or parameters
2. **Batch-oriented workflow** — Generate many, pick one, repeat (wasteful)
3. **No interactive editing** — Cannot adjust mid-generation
4. **GPU monopolization** — One generation blocks all other work

Real-time preview changes the paradigm:

1. **Continuous feedback** — See results as parameters change
2. **Interactive refinement** — Adjust brush strokes, camera paths live
3. **Progressive quality** — Coarse preview instantly, refine in background
4. **Efficient exploration** — Try ideas at preview quality, commit to full generation

MonarchRT demonstrates 16 FPS video DiT inference. Combined with shortcut forcing (Dreamer 4),
we can build a pipeline that scales from instant preview (K=2 steps) to production quality
(K=64 steps) with the same model weights.

## Specification

### 1. Pipeline Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    REAL-TIME DIFFUSION PIPELINE                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────────┐   │
│  │   Hydrogen   │────▶│   ComfyUI    │────▶│  Shortcut DiT Model  │   │
│  │   Frontend   │     │   Backend    │     │  (MonarchRT Attn)    │   │
│  └──────────────┘     └──────────────┘     └──────────────────────┘   │
│         │                    │                        │                │
│         │ WebSocket          │ Queue API              │ K steps        │
│         │ (preview stream)   │ (job mgmt)             │ (2,4,8,16...)  │
│         ▼                    ▼                        ▼                │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────────┐   │
│  │   Preview    │◀────│   Frame      │◀────│   VAE Decoder        │   │
│  │   Canvas     │     │   Buffer     │     │   (per-frame)        │   │
│  └──────────────┘     └──────────────┘     └──────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2. Quality Tiers

| Tier | Steps (K) | FPS (H100) | FPS (4090) | Use Case |
|------|-----------|------------|------------|----------|
| Scrub | 2 | 60+ | 30+ | Timeline scrubbing |
| Preview | 4 | 30 | 16 | Interactive editing |
| Draft | 8 | 16 | 8 | Review before export |
| Quality | 16 | 8 | 4 | Near-final preview |
| Production | 64 | 2 | 0.5 | Final export |

Users select tier via UI control. Pipeline automatically adjusts K parameter.

### 3. Shortcut Model Interface

```python
class ShortcutDiT(Protocol):
    """
    Diffusion transformer with step-size conditioning.
    
    The model is trained to accept arbitrary step sizes d ∈ {1/K_max, ..., 1}
    and produce valid outputs at each granularity.
    """
    
    def forward(
        self,
        x_noisy: Tensor,           # [B, T, C, H, W] noisy latents
        timestep: Tensor,          # [B] or [B, T] signal level τ
        step_size: Tensor,         # [B] or [B, T] step size d
        context: dict[str, Tensor] # Conditioning (text, image, camera)
    ) -> Tensor:
        """
        Predict denoised output (x-prediction, not v-prediction).
        
        x-prediction prevents error accumulation in long rollouts.
        """
        ...
    
    def generate(
        self,
        shape: tuple[int, ...],
        context: dict[str, Tensor],
        k: int = 4,
        guidance_scale: float = 7.5,
    ) -> Tensor:
        """
        Generate video with K denoising steps.
        
        Args:
            shape: Output shape [B, T, C, H, W]
            context: Conditioning inputs
            k: Number of steps (2, 4, 8, 16, 32, 64)
            guidance_scale: Classifier-free guidance strength
        """
        d = 1 / k
        x = torch.randn(shape, device=self.device)
        
        for step in range(k):
            tau = step * d
            x = self.forward(x, tau, d, context)
        
        return x
```

### 4. MonarchRT Attention Integration

MonarchRT replaces standard attention with Monarch matrix decomposition:

```
Standard: O(n²) attention
MonarchRT: O(n log n) via Monarch matrices

Speedup: 4-8× for typical video resolutions
Memory: 2-3× reduction in KV cache
```

Integration points:

1. **DiT blocks** — Replace `nn.MultiheadAttention` with `MonarchAttention`
2. **Causal masking** — Maintain temporal causality for autoregressive generation
3. **Flash attention fallback** — Use FlashAttention-2 when Monarch not beneficial

### 5. Streaming Protocol

WebSocket messages for real-time preview:

```typescript
// Client → Server
interface GenerateRequest {
  type: "generate";
  params: {
    prompt: string;
    reference_image?: string;  // base64
    camera_path?: CameraKeyframe[];
    quality_tier: "scrub" | "preview" | "draft" | "quality" | "production";
    frame_range: [number, number];
  };
}

// Server → Client  
interface FrameUpdate {
  type: "frame";
  frame_index: number;
  data: string;        // base64 JPEG
  latent?: string;     // base64 latent (for refinement)
  quality_tier: string;
  generation_id: string;
}

interface GenerationComplete {
  type: "complete";
  generation_id: string;
  total_frames: number;
  output_path: string;
}
```

### 6. Progressive Refinement

When user commits to higher quality:

1. **Reuse latents** — Previous generation provides initialization
2. **Targeted refinement** — Only re-generate changed regions
3. **Background processing** — Queue refinement, show preview immediately

```python
def progressive_refine(
    coarse_latents: Tensor,     # From K=4 generation
    target_k: int,              # e.g., 64
    changed_mask: Tensor,       # Binary mask of edited regions
) -> Tensor:
    """
    Refine coarse generation to higher quality.
    
    Uses coarse latents as initialization, only fully regenerating
    regions marked as changed.
    """
    # Start from coarse result (not pure noise)
    x = add_noise(coarse_latents, tau=0.3)  # Light noise
    
    # Refinement steps
    for step in range(target_k // 4):  # Fewer steps needed
        tau = 0.3 + step * (0.7 / (target_k // 4))
        x = model.forward(x, tau, 1/target_k, context)
    
    # Blend unchanged regions from coarse
    x = x * changed_mask + coarse_latents * (1 - changed_mask)
    
    return x
```

### 7. Forbidden Patterns

| Pattern | Reason |
|---------|--------|
| Synchronous generation in UI thread | Blocks all interaction |
| Unbounded frame buffers | Memory exhaustion |
| Polling for updates | Inefficient, use WebSocket |
| Full regeneration on parameter change | Wasteful, use progressive refinement |
| GPU memory allocation per frame | Preallocate buffers |

## Implementation

### Phase 1: Wire Existing Infrastructure (Q2 2026)

**Goal:** Connect VisualGenerator stub to actual generation.

Files to modify:

| File | Change |
|------|--------|
| `comfyui-extension/src/Lattice/engines/content/visual_generation.py` | Wire `generate_video()` to workflow execution |
| `comfyui-extension/src/Lattice/nodes/lattice_video_generation.py` | New ComfyUI node for video DiT |
| `hydrogen/ui/src/services/comfyui/workflowTemplates.ts` | Add MonarchRT workflow template |

### Phase 2: Streaming Preview (Q2 2026)

**Goal:** WebSocket frame streaming from ComfyUI to Hydrogen.

New routes:

```python
# In lattice_video_generation.py

@routes.websocket("/lattice/video/stream")
async def video_stream(request, ws):
    """
    Stream video frames as they generate.
    
    Protocol:
    1. Client sends GenerateRequest
    2. Server streams FrameUpdate messages
    3. Server sends GenerationComplete when done
    """
    async for msg in ws:
        request = json.loads(msg.data)
        
        async for frame in generate_streaming(request):
            await ws.send_json({
                "type": "frame",
                "frame_index": frame.index,
                "data": base64.b64encode(frame.jpeg).decode(),
                "quality_tier": request["quality_tier"],
            })
        
        await ws.send_json({
            "type": "complete",
            "generation_id": request["generation_id"],
        })
```

### Phase 3: Shortcut Model Training (Q3-Q4 2026)

**Goal:** Train shortcut-conditioned video DiT.

Training configuration:

| Parameter | Value |
|-----------|-------|
| Base model | Wan 2.2 or CogVideoX |
| K_max | 64 |
| Step sizes | {1, 2, 4, 8, 16, 32, 64} |
| Bootstrap loss | Distill 2 half-steps → 1 full step |
| Attention | MonarchRT replacement |

### Phase 4: MonarchRT Kernel Integration (Q3 2026)

**Goal:** Integrate Triton kernels for Monarch attention.

Source: `newfeatures/MonarchRT/wan/modules/monarch_attn.py`

Integration:

```python
# In lattice/models/attention.py

from MonarchRT.wan.modules.monarch_attn import MonarchMixedBlockSparseAttention

class LatticeVideoAttention(nn.Module):
    """
    Attention module with MonarchRT acceleration.
    
    Falls back to FlashAttention-2 when:
    - Sequence length < 1024 (Monarch overhead not worth it)
    - Non-CUDA device
    """
    
    def __init__(self, dim: int, heads: int, use_monarch: bool = True):
        super().__init__()
        self.use_monarch = use_monarch and torch.cuda.is_available()
        
        if self.use_monarch:
            self.attn = MonarchMixedBlockSparseAttention(dim, heads)
        else:
            self.attn = nn.MultiheadAttention(dim, heads)
```

## Conformance

A video generation implementation is **ℵ-009 conformant** if it:

1. Supports at least 3 quality tiers (preview, draft, production)
2. Achieves ≥16 FPS at preview tier on H100
3. Streams frames via WebSocket as they generate
4. Supports progressive refinement from coarse to fine
5. Uses preallocated GPU memory buffers
6. Integrates with existing VisualGenerator API

## Drawbacks

1. **Training complexity** — Shortcut models require careful curriculum
2. **Quality gap** — K=2 preview will be noticeably lower quality than K=64
3. **Model size** — MonarchRT kernels add compilation overhead
4. **Memory** — Streaming requires frame buffers in GPU memory

## Alternatives Considered

1. **LCM-LoRA** — Faster but lower quality ceiling
2. **Consistency models** — Require separate training, harder to tune
3. **Server-side rendering only** — No local preview capability
4. **Polling instead of WebSocket** — Higher latency, more overhead

## References

- [ADR 0002: World Model Architecture](../decisions/0002-world-model-architecture.md)
- [MonarchRT Paper Synthesis](../../hydrogen/docs/INTERNAL/papers/monarch-rt-real-time-video.md)
- [Dreamer 4 Paper Synthesis](../../hydrogen/docs/INTERNAL/papers/dreamer4-world-models.md)
- [Shortcut Models (Frans et al. 2024)](https://arxiv.org/abs/2410.12557)

## Authority

This RFC is maintained by the Lattice video infrastructure team. Implementation
proceeds in phases as specified. Deviations require RFC amendment.
