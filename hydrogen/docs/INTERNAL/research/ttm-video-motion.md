# Time-to-Move (TTM): Training-Free Motion Controlled Video Generation

**arXiv:** 2511.08633  
**Authors:** Assaf Singer, Noam Rotstein, Amir Mann, Ron Kimmel, Or Litany  
**Institution:** Technion – Israel Institute of Technology, NVIDIA  
**Date:** November 9, 2025  
**Domain:** Computer Vision / Video Generation / Motion Control

---

## Abstract

Time-to-Move (TTM) is a training-free, plug-and-play framework for motion- and appearance-controlled video generation via image-to-video (I2V) diffusion models. The key innovation is using crude reference animations (from cut-and-drag or depth-based reprojection) as motion proxies, combined with a novel dual-clock denoising strategy that enforces strong alignment in user-specified regions while allowing flexibility elsewhere.

**Key Contributions:**
- Training-free motion control using crude animations
- Region-dependent dual-clock denoising
- Joint motion-appearance control

---

## 1. Problem: Motion Control in Video Generation

### 1.1 The Gap

Diffusion-based video generators achieve remarkable visual quality, but:

| Limitation | Description |
|------------|-------------|
| **Motion control** | Prompt-driven, unreliable, coarse |
| **Fine-grained control** | Missing for interactive use |
| **Training requirements** | Model-specific fine-tuning is expensive |

### 1.2 Existing Approaches

| Method | Approach | Limitation |
|--------|----------|------------|
| Trajectory-conditioned | Learn motion representation | Requires fine-tuning |
| Optical flow guidance | Warp noise to align motion | Model-specific |
| Point tracks | ATI encodes Gaussian-weighted features | Training required |

### 1.3 The Goal

Provide an interface that defines:
1. **What moves** — which object/region
2. **Where it moves** — trajectory/path
3. **How it looks** — appearance preservation

---

## 2. Methodology: TTM Framework

### 2.1 Overview

```
Input Image I          Motion Control (drag/trajectory)
       │                        │
       ▼                        ▼
   Encoder              Generate Motion Signal Vw
       │                        │
       │                        ▼
       │              Binary Mask M (regions)
       │                        │
       ▼                        ▼
Image Conditioning ◄──── Dual-Clock Denoising
       │
       ▼
Output Video
```

### 2.2 Motion Signal Generation

**Input:** Single image I ∈ ℝ^(3×H×W)

**User Interaction:**
1. Select region in first frame → binary mask M₀
2. Drag region along trajectory → sequence M
3. Forward warp I according to displacement field

**Warping:**
```
Vw = forward_warp(I, M, trajectory)
```

**Disocclusion Handling:** Simple nearest-neighbor inpainting for holes

### 2.3 SDEdit Adaptation for Motion Injection

**Key Insight:** SDEdit shows coarse structure can be imposed by adding noise at the timestep where layout is determined.

**Adaptation to Video:**
1. Noise warped reference Vw to timestep t* → xt* ~ q(xt* | Vw)
2. Use I2V model (preserves first frame appearance)
3. Sample: x₀ ~ pθ(x₀ | xt*, I)

**Why I2V instead of T2V?** Text-only conditioning loses appearance fidelity.

### 2.4 Dual-Clock Denoising

**The Problem:** Single timestep t* creates trade-off:

| t* Value | Masked Regions | Unmasked Regions |
|----------|----------------|-------------------|
| Small | Close following, but artifacts | Frozen, unrealistic |
| Large | Realistic but drifts from motion | Natural but irrelevant |

**Solution:** Different noise levels per region:

```
tweak ≥ t ≥ tstrong:  Override masked region with warpedised to t- reference no1
t < tstrong:          Standard sampling for all regions
```

**Update Rule:**
```
xt-1 ← (1 - M) ⊙ x̂t-1(xt, t, I) + M ⊙ xw,t-1
```

Where:
- M = binary mask
- x̂t-1 = denoiser prediction
- xw,t-1 = warped reference at timestep t-1

### 2.5 Joint Motion-Appearance Control

Conditioning on full reference frames (not just trajectories) enables:
- Dictate appearance attributes (color, shape, style) in masked regions
- Simultaneous motion + appearance control
- Without text ambiguity

---

## 3. Technical Details

### 3.1 Algorithm: Dual-Clock Denoising

```python
def ttm_denoise(I, Vw, M, tweak, tstrong):
    # Initialize from noised warped reference
    xt = noise(Vw, tweak)
    
    for t in range(tweak, 0, -1):
        # Standard denoising step
        x_pred = denoiser(xt, t, I)
        
        # Override masked region with warped reference
        if t >= tstrong:
            xw_tm1 = noise(Vw, t-1)
            xtm1 = (1 - M) * x_pred + M * xw_tm1
        else:
            xtm1 = x_pred
            
        xt = xtm1
        
    return x0
```

### 3.2 Parameter Guidelines

| Parameter | Recommended | Effect |
|-----------|-------------|--------|
| tweak | 0.7-0.9 (high noise) | Background realism |
| tstrong | 0.3-0.5 (low noise) | Motion adherence |
| Mask | Binary, per-frame | Control regions |

### 3.3 Backbone Compatibility

TTM works with any image-to-video diffusion model:

| Backbone | Type | Parameters |
|----------|------|------------|
| SVD | Hybrid Conv/Attention | ~1.5B |
| CogVideoX | Diffusion Transformer | 5B |
| WAN 2.2 | Diffusion Transformer | 14B |

---

## 4. Experimental Results

### 4.1 Object Motion Control (MC-Bench)

| Method | Training-Free | CTD ↓ | BG-Obj CTD ↓ | Subject Cons ↑ |
|--------|--------------|-------|--------------|----------------|
| DragAnything | ✗ | 10.645 | 50.885 | 0.956 |
| SG-I2V | ✓ | 5.796 | 12.042 | 0.976 |
| MotionPro | ✗ | 8.685 | 24.485 | 0.975 |
| **TTM (SVD)** | ✓ | **7.967** | 35.340 | **0.979** |

### 4.2 Camera Motion Control (DL3DV)

| Method | MSE ↓ | FID ↓ | LPIPS ↓ | SSIM ↑ | Flow MSE ↓ |
|--------|-------|-------|---------|--------|------------|
| GWTF (γ=0.5) | 0.033 | 25.990 | 0.371 | 0.526 | 76.714 |
| Warped Ref | 0.025 | 33.443 | 0.339 | 0.560 | 65.494 |
| **TTM** | **0.022** | **21.966** | **0.332** | **0.586** | **60.558** |

### 4.3 Key Findings

1. **Best motion adherence** (lowest CoTracker distance)
2. **Highest quality** (VBench metrics)
3. **Plug-and-play** across multiple backbones
4. **No training required** — matches training-based methods

---

## 5. Relation to Hydrogen

### 5.1 Animation System

TTM directly maps to Hydrogen's animation primitives:

| TTM Concept | Hydrogen Equivalent |
|-------------|-------------------|
| Motion signal | Animation trajectory |
| Dual-clock denoising | Animation interpolation |
| Mask regions | Element hierarchy |
| Appearance preservation | Style persistence |

### 5.2 Schema Integration

```purescript
-- TTM-style animation in Hydrogen
animateElement :: 
     Element msg 
  -> Trajectory 
  -> AnimationMask 
  -> Element msg
```

Where:
- `Trajectory`: User-specified motion path
- `AnimationMask`: Regions receiving strong control

### 5.3 Real-Time Animation

TTM's training-free approach enables:

| Hydrogen Need | TTM Solution |
|---------------|--------------|
| Interactive animation | No retraining for new motions |
| Dynamic regions | Dual-clock per-region control |
| Style preservation | Image conditioning |
| Performance | No extra computation cost |

### 5.4 UI Animation Pipeline

```
User Input (drag/gesture)
        │
        ▼
Hydrogen Animation System
        │
        ▼
TTM Motion Signal Generation
        │
        ▼
Dual-Clock Interpolation
        │
        ▼
Element Frame Sequence
        │
        ▼
WebGPU/Canvas Render
```

---

## 6. Comparison to Prior Work

### 6.1 Training-Based Methods

| Method | Fine-tuning | Quality | Motion Control |
|--------|-------------|---------|----------------|
| DragAnything | Required | High | Good |
| MotionPro | Required | High | Good |
| GWTF | Required | High | Good |
| **TTM** | **None** | **High** | **Best** |

### 6.2 Training-Free Methods

| Method | Backbone | Motion Adherence | Quality |
|--------|----------|------------------|---------|
| SG-I2V | SVD | Good | Medium |
| FreeTraj | T2V | Limited | Medium |
| **TTM** | Any I2V | **Best** | **High** |

### 6.3 Unique Capabilities

TTM enables:
- **Joint motion-appearance control** — unique among all methods
- **Camera motion control** — without explicit depth estimation
- **Object insertion** — add new objects via appearance conditioning

---

## 7. Limitations and Future Work

### 7.1 Current Limitations

| Limitation | Impact | Mitigation |
|-----------|--------|------------|
| Parameter tuning (tweak, tstrong) | User effort | Defaults provided |
| Identity to first frame only | Can't introduce new objects | Inpainting recovery |
| Full object masks required | Annotation overhead | Works with imperfect masks |

### 7.2 Future Extensions

- **Multiple regions** — separate clocks per region
- **Soft masks** — continuous control strength
- **Smoother schedules** — interpolation between clocks
- **Articulated motion** — structured deformation
- **Long-horizon** — extended temporal coherence

---

## 8. Citation

```bibtex
@article{singer2025ttm,
  title={Time-to-Move: Training-Free Motion Controlled Video Generation via Dual-Clock Denoising},
  author={Singer, Assaf and Rotstein, Noam and Mann, Amir and Kimmel, Ron and Litany, Or},
  year={2025},
  eprint={2511.08633},
  archivePrefix={arXiv},
  primaryClass={cs.CV}
}
```

---

*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
