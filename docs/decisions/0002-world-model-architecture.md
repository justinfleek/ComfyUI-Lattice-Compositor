# ADR 0002: World Model Architecture

## Status

**Proposed** - March 2026

## Context

Lattice needs world model capabilities for:
1. **Predictive preview** - Show users what their video will look like before expensive generation
2. **Interactive editing** - Allow real-time manipulation of generated content
3. **Simulation** - Train policies and test scenarios in imagination
4. **Game-like interactivity** - Enable YUME-style world generation

We have synthesized research on multiple world model architectures:
- **Dreamer 4** (2B params, real-time on single GPU, 9.6s context)
- **GAIA-2** (8.4B params, multi-view driving simulation)
- **GameFactory** (interactive video generation for games)
- **PAN** (world model with GLP + Causal Swin-DPM)

The question: Which architecture pattern should Lattice adopt, and how does it integrate with existing video infrastructure?

## Decision

### 1. Adopt Shortcut Forcing for Real-Time Preview

**Rationale:** Dreamer 4's shortcut forcing achieves K=4 sampling steps (vs. 64+ typical) while maintaining quality. This enables:
- Real-time preview at 20+ FPS on single GPU
- Interactive editing without waiting for full generation
- Progressive refinement (show coarse result immediately, refine in background)

**Implementation:**

```python
# Integration point: VisualGenerator.generate_video()
# Current stub returns placeholder; wire to shortcut model

class ShortcutWorldModel:
    """
    World model with step-size conditioning for real-time inference.
    
    Based on: Dreamer 4 shortcut forcing objective
    """
    
    def generate_frame(
        self,
        context_latents: list[Tensor],  # Previous frames in latent space
        action: Action,                  # User input or policy output
        k: int = 4,                      # Sampling steps (2, 4, 8, 16...)
        tau_ctx: float = 0.1,            # Context noise for robustness
    ) -> Tensor:
        """
        Generate next frame with K denoising steps.
        
        Shortcut model conditions on step size d = 1/K, allowing
        quality/speed tradeoff at inference time.
        """
        d = 1 / k
        z_t = torch.randn_like(context_latents[-1])
        
        for step in range(k):
            tau = step * d
            z_t = self.dynamics(
                context_latents + [z_t],
                tau=[tau_ctx] * len(context_latents) + [tau],
                d=[0] * len(context_latents) + [d],
                action=action
            )
        
        return z_t
```

### 2. Latent Space Design

**Decision:** Use GAIA-2's compression ratios as baseline:

| Parameter | Value | Rationale |
|-----------|-------|-----------|
| Spatial compression | 32× | Balance quality vs. computation |
| Temporal compression | 8× | 24 frames → 3 latents (smooth motion) |
| Latent dimension | 64 | Sufficient capacity for reconstruction |
| Total compression | ~400× | Enables real-time processing |

**Tokenizer training:**
- L1 + L2 reconstruction loss
- LPIPS perceptual loss
- DINO v2 distillation (semantic alignment)
- KL regularization to unit Gaussian
- GAN fine-tuning for sharpness

### 3. Conditioning Architecture

**Decision:** Support rich structured conditioning via multiple mechanisms:

| Input Type | Encoding | Integration | Priority |
|------------|----------|-------------|----------|
| Camera motion | 6-DOF trajectory → MLP | Adaptive LayerNorm | P0 |
| User brush strokes | Spatial embedding | Cross-attention | P0 |
| Text prompts | CLIP embedding | Cross-attention | P1 |
| Reference frames | Tokenizer encoding | Concatenation | P0 |
| Scene metadata | Learned embeddings | Cross-attention | P2 |

### 4. Integration with Existing Infrastructure

**Wire VisualGenerator to ShortcutWorldModel:**

```
┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
│  Hydrogen UI    │────▶│  VisualGenerator │────▶│ ShortcutWorld   │
│  (TypeScript)   │     │  (Python API)    │     │ Model (PyTorch) │
└─────────────────┘     └──────────────────┘     └─────────────────┘
        │                        │                        │
        │ POST /lattice/api/     │ generate_video()       │ forward()
        │ content/generate-video │ currently stub →       │ K=4 steps
        │                        │ wire to model          │
        ▼                        ▼                        ▼
┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
│  Export Presets │────▶│ Workflow         │────▶│ ComfyUI Queue   │
│  (UI config)    │     │ Templates        │     │ (execution)     │
└─────────────────┘     └──────────────────┘     └─────────────────┘
```

### 5. Model Variants

| Variant | Parameters | Use Case | FPS (H100) |
|---------|------------|----------|------------|
| Preview | 500M | Real-time preview while editing | 30+ |
| Quality | 2B | Final generation | 20 |
| Ultra | 8B+ | Cinematic output | 5 |

**Default workflow:**
1. User edits with Preview model (instant feedback)
2. Export triggers Quality or Ultra model
3. Progressive enhancement shows results incrementally

## Architecture Diagram

```
                    ┌─────────────────────────────────────────────┐
                    │              LATTICE WORLD MODEL             │
                    ├─────────────────────────────────────────────┤
                    │                                             │
Input Layer         │  ┌───────────┐  ┌───────────┐  ┌─────────┐ │
                    │  │ Reference │  │   Text    │  │ Camera  │ │
                    │  │  Frames   │  │  Prompt   │  │  Path   │ │
                    │  └─────┬─────┘  └─────┬─────┘  └────┬────┘ │
                    │        │              │             │       │
                    │        ▼              ▼             ▼       │
Encoding            │  ┌───────────┐  ┌───────────┐  ┌─────────┐ │
                    │  │ Tokenizer │  │   CLIP    │  │ 6-DOF   │ │
                    │  │  Encoder  │  │  Encoder  │  │  MLP    │ │
                    │  └─────┬─────┘  └─────┬─────┘  └────┬────┘ │
                    │        │              │             │       │
                    │        └──────────────┼─────────────┘       │
                    │                       ▼                     │
                    │            ┌──────────────────┐             │
Dynamics            │            │  Shortcut World  │             │
                    │            │      Model       │             │
                    │            │   (DiT + Flow)   │             │
                    │            └────────┬─────────┘             │
                    │                     │                       │
                    │                     ▼                       │
                    │            ┌──────────────────┐             │
Decoding            │            │    Tokenizer     │             │
                    │            │     Decoder      │             │
                    │            └────────┬─────────┘             │
                    │                     │                       │
                    │                     ▼                       │
Output              │            ┌──────────────────┐             │
                    │            │   Video Frames   │             │
                    │            │   [T, C, H, W]   │             │
                    │            └──────────────────┘             │
                    │                                             │
                    └─────────────────────────────────────────────┘
```

## Consequences

### Positive

1. **Real-time preview** - Users see results immediately while editing
2. **Unified architecture** - Same model handles preview, generation, and simulation
3. **Progressive refinement** - Show coarse result fast, refine in background
4. **Action conditioning** - Enables interactive world generation (YUME-style)
5. **Offline training** - Can train policies in imagination without environment

### Negative

1. **Model size** - Even Preview model (500M) requires GPU
2. **Training complexity** - Shortcut forcing requires careful curriculum
3. **Tokenizer quality** - ~400× compression may lose fine details
4. **Memory** - Long context (192 frames) requires efficient attention

### Mitigations

1. **Tiered deployment** - Cloud for Ultra, local for Preview
2. **Curriculum learning** - Start with short sequences, extend gradually
3. **Multi-scale tokenizer** - Higher resolution for important regions
4. **Sliding window** - Process long videos in chunks with overlap

## Implementation Phases

| Phase | Scope | Target |
|-------|-------|--------|
| 1 | Wire VisualGenerator stub to MonarchRT inference | Q2 2026 |
| 2 | Add shortcut conditioning to existing models | Q2 2026 |
| 3 | Train custom tokenizer on Lattice data | Q3 2026 |
| 4 | Full shortcut world model training | Q4 2026 |

## References

- [Dreamer 4](../hydrogen/docs/INTERNAL/papers/dreamer4-world-models.md)
- [GAIA-2](../hydrogen/docs/INTERNAL/research/gaia2-world-model.md)
- [MonarchRT](../hydrogen/docs/INTERNAL/papers/monarch-rt-real-time-video.md)
- [ADR 0001: Research Integration Roadmap](0001-research-integration-roadmap.md)
