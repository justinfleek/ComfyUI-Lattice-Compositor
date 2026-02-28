# ATI: Any Trajectory Instruction for Controllable Video Generation

**arXiv:** 2505.22944  
**Authors:** Angtian Wang, Haibin Huang, Jacob Zhiyuan Fang, Yiding Yang, Chongyang Ma (ByteDance Intelligent Creation)  
**Date:** June 10, 2025  
**Domain:** Computer Vision / Video Generation / Motion Control

---

## Abstract

ATI provides a **unified framework for motion control** in video generation that seamlessly integrates:
- Camera movement
- Object-level translation
- Fine-grained local motion

**Key Innovation:** All motion types are represented as **trajectories of specific points**, projected into latent space via a lightweight motion injector.

---

## 1. Problem: Fragmented Motion Control

### 1.1 Previous Approaches

| Method | Motion Type | Limitation |
|--------|------------|------------|
| CameraCtrl | Camera only | Separate from object |
| DragNUWA | Object flow | Different module |
| MOFA-Video | Dense motion | Different module |
| Motion-I2V | Local deformation | Different module |

**Problem:** Different motion types required separate modules, leading to fragmented workflows.

### 1.2 ATI Solution: Unified Trajectories

```
┌─────────────────────────────────────────────────────────────┐
│                     ATI Architecture                         │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Input Image ──► VAE Encoder ──► Latent Feature Map        │
│                                                              │
│  User Trajectories (point paths) ──► Motion Injector       │
│                                              │               │
│                                              ▼               │
│  ┌─────────────────────────────────────────────────────┐  │
│  │              Gaussian-Based Motion Injector           │  │
│  │  1. Sample feature at initial position (x₀, y₀)     │  │
│  │  2. Compute spatial Gaussian mask for each frame     │  │
│  │  3. Softly distribute feature along trajectory        │  │
│  └─────────────────────────────────────────────────────┘  │
│                                              │               │
│                                              ▼               │
│  DiT Blocks ──► Denoised Latents ──► VAE Decoder ──► Video│
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## 2. Methodology

### 2.1 Gaussian Model for Trajectory Instruction

For each trajectory point φ_t = (x_t, y_t) at frame t:

```
P(f | l_{i,j,t}) = exp(-||φ_t - (i,j)||² / (2σ))
```

Where:
- σ = 1/440 (Gaussian spread)
- Feature f sampled at initial position (x₀, y₀)
- Gaussian mask distributes feature to nearby pixels

### 2.2 Feature Extraction

```python
# Input image → VAE encoder
L_I = VAE_Encoder(I)  # H × W × C latent

# Sample feature at trajectory start position
f = bilinear_sample(L_I, x_0, y_0)

# For each frame t, compute Gaussian mask
for t in range(T):
    mask_t = Gaussian(φ_t, σ)  # Centered at trajectory position
    guided_feature_t = f * mask_t
```

### 2.3 Motion Injector Integration

- Projects trajectory signals into DiT latent space
- Works with pretrained I2V models (no retraining required)
- Compatible with Seaweed-7B and Wan2.1-14B

### 2.4 Tail Dropout Regularization

**Problem:** When trajectory ends early, model hallucinates occluders.

**Solution:** During training, randomly truncate trajectories:
```python
if random() < 0.2:
    td = random(0, T)  # Dropout frame
    visibility[td:] = 0  # Simulate early termination
```

---

## 3. Motion Types Supported

### 3.1 Local Deformations

- Specify keypoints on object
- Track their motion paths
- Generates fine-grained local movement

### 3.2 Object Translation

- Track bounding box corners
- Control whole-object movement

### 3.3 Camera Dynamics

- Define points at infinity (vanishing points)
- Control pan, zoom, rotation

### 3.4 Combined Control

- Coordinate camera + object motion
- Complex multi-point trajectories

---

## 4. Results

### 4.1 Evaluation Tasks

| Task | Metric | ATI Performance |
|------|--------|-----------------|
| Motion brushes | Temporal consistency | SOTA |
| Viewpoint changes | Control precision | Outperforms commercial |
| Local manipulation | Visual quality | Superior |

### 4.2 Baselines Beat

- ✓ Academic methods (CameraCtrl, MOFA-Video)
- ✓ Commercial products

---

## 5. Relation to Hydrogen

### 5.1 Video Generation for UI

For **billion-agent swarms:**

| Need | ATI Solution |
|------|---------------|
| **Motion specification** | Unified trajectory format |
| **Camera control** | Point-at-infinity trajectories |
| **Object animation** | Keypoint tracking |
| **No retraining** | Lightweight injector |

### 5.2 Complementary Papers

- **Wan-Animate**: Character animation with skeleton + face
- **BindWeave**: Subject consistency with MLLM
- **AnchorWeave**: World consistency with local memories

---

## 6. References

1. Seaweed-7B (I2V backbone)
2. Wan2.1-14B (I2V backbone)
3. DiT (Diffusion Transformer)
4. CameraCtrl (camera conditioning)
5. DragNUWA (optical flow control)
6. MOFA-Video (dense motion fields)

---

## 7. Citation

```bibtex
@misc{wang2025ati,
  title={ATI: Any Trajectory Instruction for Controllable Video Generation},
  author={Angtian Wang and Haibin Huang and Jacob Zhiyuan Fang and Yiding Yang and Chongyang Ma},
  year={2025},
  eprint={2505.22944},
  archivePrefix={arXiv},
  primaryClass={cs.CV}
}
```

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
