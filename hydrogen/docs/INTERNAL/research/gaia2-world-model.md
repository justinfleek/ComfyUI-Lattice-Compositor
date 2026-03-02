# GAIA-2: A Controllable Multi-View Generative World Model for Autonomous Driving

**arXiv:** 2503.20523  
**Authors:** Lloyd Russell, Anthony Hu, Lorenzo Bertoni, George Fedoseev, Jamie Shotton, Elahe Arani, Gianluca Corrado (Wayve)  
**Venue:** Technical Report, 2025

---

## 1. Abstract

Generative models offer a scalable and flexible paradigm for simulating complex environments, yet current approaches fall short in addressing domain-specific requirements of autonomous driving—such as multi-agent interactions, fine-grained control, and multi-camera consistency.

GAIA-2 (Generative AI for Autonomy) is a latent diffusion world model that unifies these capabilities:
- **Controllable video generation** conditioned on ego-vehicle dynamics, agent configurations, environmental factors, and road semantics
- **High-resolution, spatiotemporally consistent multi-camera videos** across geographically diverse driving environments (UK, US, Germany)
- **Structured conditioning** and external latent embeddings for semantic control

---

## 2. Architecture Overview

### 2.1 Two-Component System

```
┌─────────────────────────────────────────────────────────────────┐
│                      GAIA-2 Architecture                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────┐     ┌──────────────────────┐                │
│  │   Video      │     │   Latent World Model │                │
│  │  Tokenizer   │────▶│   (8.4B parameters)  │                │
│  │  (Encoder)   │     │                      │                │
│  └──────────────┘     └──────────────────────┘                │
│         │                        │                              │
│         │                        ▼                              │
│         │               ┌──────────────────┐                   │
│         │               │  Flow Matching   │                   │
│         │               │   Diffusion      │                   │
│         │               └──────────────────┘                   │
│         │                        │                              │
│         ▼                        ▼                              │
│  ┌──────────────┐     ┌──────────────────────┐                │
│  │   Video      │◀────│    Video Tokenizer   │                │
│  │  Decoder     │     │    (Decoder)          │                │
│  └──────────────┘     └──────────────────────┘                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 Video Tokenizer

Compresses raw high-resolution video into compact continuous latent space:

| Component | Parameters | Specification |
|-----------|------------|---------------|
| Encoder | 85M | Space-time factorized transformer |
| Decoder | 200M | Asymmetric architecture |
| Spatial compression | 32× | vs typical 8× |
| Temporal compression | 8× | 24 frames → 3 latents |
| Latent dimension | 64 | Channels |
| Total compression | ~400× | (Tv×Hv×Wv×3)/(TL×H×W×L) |

### 2.3 Latent World Model

| Component | Specification |
|-----------|---------------|
| Architecture | Space-time factorized transformer |
| Parameters | 8.4B |
| Hidden dimension | 4096 |
| Attention heads | 32 |
| Transformer blocks | 22 |
| Training | Flow matching |

---

## 3. Video Tokenizer Details

### 3.1 Encoder Architecture

```python
# Given input video (i_1, ..., i_Tv)
# Encoder computes: (z_1, ..., z_TL) = e_φ(i_1, ..., i_Tv)

# Spatial downsampling: 32× (Hv/H = 32)
# Temporal downsampling: 8× (Tv/TL = 8)

Encoder architecture:
1. Downsampling conv block: stride (2, 8, 8) → embedding dim 512
2. Downsampling conv block: stride (2, 2, 2) → embedding dim 512
3. 24 spatial transformer blocks (dim 512, 16 heads)
4. Final conv: stride (1, 2, 2) → project to 2L channels
5. Sample from Gaussian: z ∼ N(μ, σ)
```

### 3.2 Decoder Architecture

```python
# Decoder architecture:
1. Linear projection: L → embedding dim
2. Upsampling conv block: stride (1, 2, 2) [depth-to-space]
3. 16 space-time factorized transformer blocks (dim 512, 16 heads)
4. Upsampling conv block: stride (2, 2, 2)
5. 8 space-time factorized transformer blocks (dim 512, 16 heads)
6. Final upsampling: stride (2, 8, 8) → RGB channels
```

**Key difference:** Encoder maps 8 consecutive frames to 1 temporal latent; decoder jointly decodes all TL latents to Tv frames for temporal consistency.

### 3.3 Training Losses

The tokenizer is trained with:

1. **Image reconstruction:**
   - L1 loss (weight 0.2)
   - L2 loss (weight 2.0)
   - LPIPS perceptual loss (weight 0.1)

2. **Semantic alignment:**
   - DINO v2 distillation (weight 0.1)
   - Cosine similarity on latent features

3. **Latent space regularization:**
   - KL divergence (weight 10⁻⁶)
   - Regularize to unit Gaussian

4. **GAN fine-tuning:**
   - 3D convolutional discriminator
   - GAN loss (weight 0.1)
   - Spectral normalization

---

## 4. World Model Details

### 4.1 Input Specification

```
x_{1:T} ∈ R^{T × N × H × W × L}

Where:
- T = temporal window (e.g., 48 frames)
- N = number of cameras (5 typically)
- H, W = latent spatial dimensions (14, 30)
- L = latent dimension (64)
```

### 4.2 Conditioning Inputs

| Input Type | Encoding | Integration |
|------------|----------|-------------|
| **Ego-vehicle action** (speed, curvature) | symlog transform + MLP | Adaptive Layer Norm |
| **Dynamic agents** (3D bounding boxes) | Projected to 2D + MLP | Cross-attention |
| **Metadata** (country, weather, time) | Learnable embeddings | Cross-attention |
| **Camera parameters** (intrinsics, extrinsics) | Sinusoidal + MLP | Additive |
| **Timestamp** | Sinusoidal + MLP | Additive |
| **CLIP embeddings** | Linear projection | Cross-attention |
| **Scenario embeddings** | Linear projection | Cross-attention |

### 4.3 Action Encoding (symlog)

**Definition 1 (Symmetric Logarithmic Transform):**
```
symlog(y) = sign(y) × log(1 + s×|y|) / log(1 + s×|y_max|)
```

For different inputs:
- **Curvature** (range: 0.0001 to 0.1 m⁻¹): s = 1000
- **Speed** (range: 0 to 75 m/s): s = 3.6

### 4.4 Flow Matching Training

**Definition 2 (Flow Matching):** A generative framework that learns to predict velocity fields.

**Forward process (training):**
```python
# Randomly sample flow matching time τ ∈ [0, 1]
τ ~ p(τ)  # Bimodal logit-normal distribution

# Interpolate between noise and data
x_τ = τ × x + (1 - τ) × ε  where ε ~ N(0, I)

# Target velocity
v = x - ε
```

**Model prediction:**
```python
# Model predicts velocity
v̂ = f_θ(x_τ | x_context, a, c, τ)

# Loss: L2 between predicted and target velocity
L = ||v - v̂||²
```

### 4.5 Flow Matching Time Distribution

**Bimodal logit-normal distribution:**

| Mode | μ | σ | Probability | Purpose |
|------|---|---|-------------|---------|
| Primary | 0.5 | 1.4 | 0.8 | Learn useful gradients (low-moderate noise) |
| Secondary | -3.0 | 1.0 | 0.2 | Learn spatial structures (high noise) |

**Latent normalization:**
```python
x_norm = (x - μ_x) / σ_x
```
This ensures signal magnitude matches added Gaussian noise.

---

## 5. Training Data

### 5.1 Dataset Specification

| Property | Value |
|----------|-------|
| Video sequences | ~25 million |
| Duration | 2 seconds each |
| Collection period | 2019-2024 |
| Geographic coverage | UK, US, Germany |
| Vehicle platforms | 3 car models, 2 van types |
| Camera count | 5-6 per vehicle |
| Frame rates | 20, 25, 30 Hz |

### 5.2 Data Balancing

The dataset is balanced not just on individual features, but on their **joint probability distribution**:
- Specific lighting + weather in certain geographies
- Behaviors unique to particular road types
- Realistic co-occurrences

### 5.3 Validation Strategy

**Geographically held-out validation:**
- Specific geofences excluded from training
- Evaluation on unseen locations

---

## 6. Generation Modes

### 6.1 From Scratch

Generate entirely novel scenes:
```
Input:  Random noise
Output: Realistic driving video
```

### 6.2 Context Rollout

Continue from observed context:
```
Input:  Past video frames + future actions
Output: Predicted future frames
```

### 6.3 Spatial Inpainting

Edit specific regions:
```
Input:  Partial scene + mask + actions
Output: Coherent edited video
```

---

## 7. Key Algorithms

### 7.1 Adaptive Layer Norm

```python
def adaptive_layer_norm(x, condition, time_emb):
    """
    Inject condition and time into layer normalization.
    
    Args:
        x: Input tensor [B, T, N, H*W, C]
        condition: Action embedding [B, C]
        time_emb: Flow time embedding [B, C]
    """
    # Scale and shift based on condition and time
    gamma = mlp(condition) + mlp(time_emb)
    beta = mlp(condition) + mlp(time_emb)
    
    # Apply: norm(x) * (1 + gamma) + beta
    return (x - mean(x)) / std(x) * (1 + gamma) + beta
```

### 7.2 Camera Geometry Encoding

```python
def encode_camera(intrinsics, extrinsics, distortion):
    """
    Encode camera parameters.
    
    Args:
        intrinsics: [B, N, 4] - focal lengths, principal point
        extrinsics: [B, N, 4, 4] - transformation matrix
        distortion: [B, N, K] - distortion coefficients
    """
    # Intrinsics: extract and normalize
    f_x, f_y, c_x, c_y = split(intrinsics, dim=-1)
    intr_emb = mlp(normalize([f_x, f_y, c_x, c_y]))
    
    # Extrinsics: process each element
    extr_emb = mlp(flatten(extrinsics))
    
    # Distortion: project to latent space
    dist_emb = mlp(distortion)
    
    # Combine
    return intr_emb + extr_emb + dist_emb
```

### 7.3 Dynamic Agent Conditioning

```python
def encode_agents(bounding_boxes_3d, camera_params):
    """
    Encode dynamic agents as conditioning features.
    
    Args:
        bounding_boxes_3d: [B, T, N, B, 13] - 3D boxes
        camera_params: Camera intrinsics/extrinsics
    
    Features per box:
    - 3D location (x, y, z)
    - 3D dimensions (w, h, l)
    - orientation (yaw, pitch, roll)
    - category (vehicle, pedestrian, cyclist)
    """
    # Project 3D boxes to 2D image plane
    boxes_2d = project_3d_to_2d(bounding_boxes_3d, camera_params)
    
    # Normalize coordinates
    boxes_normalized = normalize(boxes_2d)
    
    # Embed each feature dimension
    features = mlp_per_feature(boxes_normalized)
    
    return features  # [B, T, N, B, feature_dim]
```

---

## 8. Results Summary

### 8.1 Capabilities

- **Resolution:** 448 × 960 per camera
- **Multi-camera:** Up to 5 temporally and spatially consistent views
- **Temporal:** 48 frames at native capture frequency
- **Conditioning:** Speed, curvature, weather, time of day, geography, agent positions

### 8.2 Technical Achievements

1. **First unified framework** for controllable driving video generation
2. **8.4B parameter** latent diffusion world model
3. **~400× compression** via video tokenizer
4. **Flow matching** for stable training
5. **Rich structured conditioning** via multiple mechanisms

---

## 9. Key Definitions

1. **Latent Diffusion:** Diffusion in compressed latent space rather than pixel space
2. **Flow Matching:** Generative framework predicting velocity fields
3. **Space-Time Factorization:** Separate spatial and temporal attention
4. **Adaptive Layer Norm:** Condition injection via learned scale/shift
5. **symlog Transform:** Symmetric logarithmic normalization for unbounded inputs

---

## 10. Relation to Hydrogen

### 10.1 Video Generation Implications

GAIA-2 demonstrates that:
1. **Latent space design** is critical for quality/speed trade-off
2. **Flow matching** enables stable training vs. DDPM
3. **Multi-view consistency** requires shared latent conditioning
4. **Structured inputs** (actions, metadata) enable controllable generation

### 10.2 Schema Implications

```purescript
-- Video latent representation
data VideoLatent
  = VideoLatent
      { temporal :: Array (Array Tensor)  -- [T, N, H, W, L]
      , metadata :: SceneMetadata
      , camera :: CameraConfig
      }

-- Conditioning types
data Conditioning
  = Action Speed Curvature
  | AgentState (Array BoundingBox3D)
  | Weather WeatherType
  | TimeOfDay Hour
  | Geography Country

-- World model output
data WorldModelOutput
  = PredictedLatent VideoLatent
  | InpaintedLatent VideoLatent Mask
```

---

## 11. Bibliography

1. Russell et al. "GAIA-2: A Controllable Multi-View Generative World Model for Autonomous Driving" 2025
2. Esser et al. "LDM: High-Resolution Image Synthesis with Latent Diffusion Models" CVPR 2022
3. Lipman et al. "Flow Matching for Generative Modeling" ICLR 2023

---

*Document generated: 2026-02-26*
*Related: GameFactory, WorldGen, PAN World Model*
