# Wan-Animate: Unified Character Animation and Replacement with Holistic Replication

**arXiv:** 2509.14055  
**Authors:** HumanAIGC Team, Tongyi Lab, Alibaba  
**Date:** September 17, 2025  
**Domain:** Computer Vision / Video Generation / Character Animation

---

## Abstract

Wan-Animate provides a **unified framework** for character animation and replacement, built upon the Wan video generation model.

**Two Core Functionalities:**
1. **Animation Mode:** Replicate expressions and movements from reference video to animate static character image
2. **Replacement Mode:** Integrate animated character into reference video, replacing original subject with proper lighting/color tone

**Key Innovation:** Modified input paradigm that unifies reference image injection, temporal frame guidance, and dual-mode selection into common symbolic representation.

---

## 1. Problem: Character Animation Gaps

### 1.1 Previous Limitations

| Issue | Description |
|-------|-------------|
| **No holistic solution** | Existing methods handle motion OR expression, not both |
| **UNet-based weakness** | Most open-source uses SD/SVD, quality behind DiT |
| **Missing environment integration** | No open-source method for character replacement |
| **Temporal discontinuity** | Frame-to-frame consistency issues |

### 1.2 Wan-Animate Solution

```
┌─────────────────────────────────────────────────────────────┐
│                  Wan-Animate Architecture                    │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Source Image ──────► ReferenceNet ──────┐                  │
│                                           │                  │
│  Reference Video ──► Skeleton Extractor ─┼─► DiT Blocks    │
│                        │                  │                  │
│                        ▼                  │                  │
│                   Face Encoder ────────────┤                  │
│                                           │                  │
│  Optional: Background Image ───────────────┤                  │
│                                           │                  │
│                        ┌──────────────────┘                  │
│                        │                                       │
│                        ▼                                       │
│  ┌─────────────────────────────────────────┐                │
│  │         Relighting LoRA (optional)        │                │
│  │   (for Replacement Mode environmental   │                │
│  │          lighting integration)            │                │
│  └────────────────────┬────────────────────┘                │
│                       ▼                                      │
│              High-Fidelity Character Video                    │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## 2. Methodology

### 2.1 Input Formulation

**Modified Wan-I2V Inputs:**

| Component | Animation Mode | Replacement Mode |
|----------|--------------|-----------------|
| Reference latent | Concatenated to conditional | Concatenated to conditional |
| Temporal latents | First few target frames | First few target frames |
| Environment | Zero-filled | Segmented from ref video |
| Binary mask | 1 for reference | 1 for environment regions |

### 2.2 Body Control: Skeleton-Based

- **Spatially-aligned skeleton signals**
- Added to initial noise latents
- Robust for non-humanoid characters

### 2.3 Face Control: Implicit Features

```
Face Images → VAE Encoder → Frame-wise Latents → Temporal Alignment 
                                                       ↓
                                              Cross-Attention → DiT
```

- Preserves maximum detail
- Disentangles expression from identity
- Temporally compressed to align with video latents

### 2.4 Relighting LoRA (Replacement Mode)

- Trained specifically for environmental integration
- Applies appropriate lighting and color tone
- Seamless character-environment fusion

---

## 3. Training

### 3.1 Foundation

- Built on Wan2.1 (DiT-based video generation)
- Preserves pre-trained knowledge

### 3.2 Dual-Mode Training

| Mode | Input | Output |
|------|-------|--------|
| Animation | Source image + Reference video | Character video (source background) |
| Replacement | Source image + Reference video + Segmentation | Video with replaced character |

### 3.3 Inference

- 50 denoising steps
- CFG guidance
- Probabilistic temporal latent sampling

---

## 4. Results

### 4.1 Capabilities

- ✓ Animates portraits, half-body, full-body
- ✓ Character replacement with lighting transfer
- ✓ Long video generation via temporal guidance
- ✓ State-of-the-art quality vs open-source

### 4.2 Comparison

Outperforms:
- Animate Anyone (UNet-based)
- ComfyUI workflows
- Various closed-source products

---

## 5. Relation to Hydrogen

### 5.1 Video Generation for UI

For **billion-agent swarms:**

| Need | Wan-Animate Solution |
|------|---------------------|
| **Character animation** | Skeleton + face control |
| **Video synthesis** | DiT-based quality |
| **Environment integration** | Relighting LoRA |

### 5.2 Complementary Papers

- **BindWeave**: Subject-consistent video generation (MLLM reasoning)
- **AnchorWeave**: World-consistent generation (local memories)
- **Wan (foundation)**: DiT video generation

---

## 6. References

1. Wan (Video DiT foundation)
2. DiT (Diffusion Transformer)
3. Animate Anyone
4. Stable Diffusion
5. SMPL (3D body model)
6. Rectified Flow

---

## 7. Citation

```bibtex
@misc{alibaba2025wananimate,
  title={Wan-Animate: Unified Character Animation and Replacement with Holistic Replication},
  author={HumanAIGC Team, Tongyi Lab, Alibaba},
  year={2025},
  eprint={2509.14055},
  archivePrefix={arXiv},
  primaryClass={cs.CV}
}
```

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
