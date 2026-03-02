# Depth Anything 3: Recovering the Visual Space from Any Views

**Source**: arXiv:2511.10647v1 (November 2025)
**Authors**: Haotong Lin, Sili Chen, Jun Hao Liew, Donny Y. Chen, et al. (ByteDance Seed)
**Domain**: Geometry Pillar — Depth Estimation, Multi-View Geometry, Camera Pose

---

## Abstract

Depth Anything 3 (DA3) predicts spatially consistent geometry from an arbitrary
number of visual inputs, with or without known camera poses. Two key insights:

1. **Single plain transformer** (vanilla DINO encoder) suffices — no
   architectural specialization required
2. **Depth-ray prediction** obviates complex multi-task learning

**Results**:
- Surpasses VGGT by 35.7% in camera pose accuracy, 23.6% in geometric accuracy
- Outperforms Depth Anything 2 in monocular depth estimation
- SOTA on 18/20 benchmark settings
- Trained exclusively on public academic datasets

## 1. Core Innovation: Depth-Ray Representation

Instead of predicting rotation matrices R (which require orthogonality
constraints), DA3 represents camera pose implicitly via per-pixel ray maps.

**Ray representation**: For each pixel p, the camera ray r ∈ R⁶ is:
```
r = (t, d)  where:
  t ∈ R³ = ray origin (camera center)
  d ∈ R³ = ray direction (unnormalized, preserves projection scale)
```

**3D point recovery**: Given depth D and ray (t, d):
```
P = t + D(u, v) · d
```

**Why this works**:
- No orthogonality constraints to enforce
- Dense ray map M ∈ R^(H×W×6) stores per-pixel parameters
- Element-wise operations generate consistent point clouds
- Camera parameters can be recovered via DLT (see Section 4.1)

## 2. Architecture

### 2.1 Single Transformer Backbone

No specialized architecture — just DINOv2 vision transformer with L blocks:

```
Input: N images {I_i}  →  Patch tokens per view
                        ↓
           First L_s layers: self-attention WITHIN each view
                        ↓  
           Next L_g layers: alternating cross-view / within-view attention
                        ↓
           Dual-DPT Head: depth + ray maps
```

**Layer split**: L_s : L_g = 2 : 1 (optimal tradeoff per ablation)

**Input-adaptive**: With single image, model reduces to monocular depth
estimation with no extra cost.

### 2.2 Cross-View Self-Attention

Cross-view reasoning via token rearrangement (no architecture changes):

```python
def cross_view_attention(tokens, num_views, layer_idx, L_s, L_g):
    """
    Input-adaptive self-attention across views.
    
    tokens: [batch, num_views, num_patches, dim]
    """
    if layer_idx < L_s:
        # Within-view attention only
        # Reshape: [batch * num_views, num_patches, dim]
        tokens = tokens.view(-1, num_patches, dim)
        out = self_attention(tokens)
        return out.view(batch, num_views, num_patches, dim)
    else:
        # Alternate between cross-view and within-view
        if (layer_idx - L_s) % 2 == 0:
            # Cross-view: all tokens attend to all tokens across views
            # Reshape: [batch, num_views * num_patches, dim]
            tokens = tokens.view(batch, -1, dim)
            out = self_attention(tokens)
            return out.view(batch, num_views, num_patches, dim)
        else:
            # Within-view
            tokens = tokens.view(-1, num_patches, dim)
            out = self_attention(tokens)
            return out.view(batch, num_views, num_patches, dim)
```

### 2.3 Dual-DPT Head

Joint depth and ray prediction with shared reassembly, distinct fusion:

```
Feature tokens from backbone
        ↓
┌─────────────────────────────┐
│   Shared Reassembly Modules │  ← Process features for both branches
└─────────────────────────────┘
        ↓                ↓
┌──────────────┐  ┌──────────────┐
│ Depth Fusion │  │  Ray Fusion  │  ← Separate fusion parameters
└──────────────┘  └──────────────┘
        ↓                ↓
┌──────────────┐  ┌──────────────┐
│ Depth Output │  │  Ray Output  │
│   (H×W×1)    │  │   (H×W×6)    │
└──────────────┘  └──────────────┘
```

**Why shared reassembly**: Ensures depth and ray operate on same processed
features, encouraging strong interaction while avoiding redundant representations.

### 2.4 Camera Condition Injection

Optional camera poses via prepended camera tokens:

```python
def inject_camera(patch_tokens, camera_params=None):
    """
    camera_params: (K, R, t) if available, else None
    """
    if camera_params is not None:
        K, R, t = camera_params
        # Convert to compact representation
        f = fov_from_intrinsics(K)  # R²
        q = rotation_to_quaternion(R)  # R⁴
        v = (f, q, t)  # R⁹ total
        
        # Encode via lightweight MLP
        camera_token = camera_encoder(v)  # E_c: R⁹ → R^dim
    else:
        # Shared learnable placeholder
        camera_token = learned_camera_token  # c_l
    
    # Prepend to patch tokens
    tokens = concat([camera_token, patch_tokens], dim=1)
    
    return tokens  # Camera token participates in all attention
```

## 3. Training Pipeline

### 3.1 Teacher-Student Paradigm

Real-world depth data is often noisy/incomplete. Solution: train teacher on
synthetic data only, then use for pseudo-labeling real data.

```
Phase 1: Teacher Training (synthetic only)
  - Train monocular relative depth predictor
  - Datasets: HyperSim, TartanAir, Objaverse, etc. (20+ synthetic sources)
  - High-quality geometric supervision
  
Phase 2: Pseudo-Label Generation  
  - Teacher generates dense depth for all real-world data
  - Align pseudo-depth to sparse/noisy ground truth via RANSAC
  
Phase 3: Student Training (real + synthetic)
  - Train DA3 with aligned pseudo-labels
  - Preserves geometric accuracy while enhancing detail
```

### 3.2 Depth Alignment

Align teacher's relative depth to metric measurements via RANSAC:

```python
def align_depth(teacher_depth, sparse_metric_depth, validity_mask):
    """
    Align scale-shift-invariant depth to absolute measurements.
    
    teacher_depth: D̃ from teacher (relative)
    sparse_metric_depth: D from sensor (sparse, noisy)
    validity_mask: m_p indicating valid measurements
    """
    # RANSAC least squares with inlier threshold = MAD of residual median
    valid_teacher = teacher_depth[validity_mask]
    valid_metric = sparse_metric_depth[validity_mask]
    
    # Solve: D_metric ≈ s * D̃_teacher + t
    s_hat, t_hat = ransac_least_squares(
        valid_teacher, valid_metric,
        inlier_threshold=median_absolute_deviation(residuals)
    )
    
    # Aligned depth preserves teacher detail with metric scale
    aligned_depth = s_hat * teacher_depth + t_hat
    
    return aligned_depth  # D_{T→M}
```

### 3.3 Training Objectives

Multi-term loss with normalized ground truth:

```
L = L_D(D̂, D) + L_M(R̂, M) + L_P(D̂⊙d + t, P) + β·L_C(ĉ, v) + α·L_grad(D̂, D)

where:
  L_D   = depth loss with confidence weighting
  L_M   = ray map loss
  L_P   = point map consistency loss
  L_C   = camera prediction loss (optional)
  L_grad = gradient loss for sharp edges
```

**Gradient loss** (preserves edges, ensures smooth planes):
```
L_grad = ||∇_x D̂ - ∇_x D||₁ + ||∇_y D̂ - ∇_y D||₁
```

**Confidence-weighted depth loss**:
```
L_D = (1/Z) Σ_p m_p · (D_c,p |D̂_p - D_p| - λ_c log D_c,p)
```
where D_c,p is depth confidence, enabling robust learning from noisy labels.

## 4. Key Algorithms

### 4.1 Ray Map to Camera Parameters

Recover explicit camera (R, K, t) from dense ray map via DLT:

```python
def ray_map_to_camera(ray_map):
    """
    ray_map: M ∈ R^(H×W×6)
      M[:,:,:3] = ray origins (per-pixel)
      M[:,:,3:] = ray directions (per-pixel)
    
    Returns: (R, K, t) camera parameters
    """
    H, W = ray_map.shape[:2]
    
    # 1. Estimate camera center by averaging ray origins
    t_c = ray_map[:,:,:3].mean(dim=(0,1))  # Eq. 1
    
    # 2. Solve for homography H = K·R via DLT
    # For identity camera K_I = I, ray direction is d_I = p
    # Target camera: d_cam = K·R·d_I
    # So homography relates canonical rays to observed rays
    
    # Collect pixel coordinates and corresponding ray directions
    pixels = []  # p_{h,w}
    rays = []    # M(h,w,3:)
    
    for h in range(H):
        for w in range(W):
            p = torch.tensor([w, h, 1.0])  # homogeneous pixel
            d = ray_map[h, w, 3:]          # observed ray direction
            pixels.append(p)
            rays.append(d)
    
    # Solve: H* = argmin ||H·p × M(h,w,3:)||  (Eq. 2)
    H_star = dlt_solve(pixels, rays)
    
    # 3. Decompose H* = K·R via RQ decomposition
    # K is upper-triangular, R is orthonormal
    K, R = rq_decomposition(H_star)
    
    return R, K, t_c
```

**Note**: This is computationally expensive, so a lightweight camera head D_C
is added that directly predicts (f, q, t) from camera tokens.

### 4.2 Depth-Ray Fusion for Point Clouds

Element-wise operation generates consistent 3D point cloud:

```python
def fuse_depth_ray(depth_map, ray_map):
    """
    Fuse predicted depth and ray maps into 3D point cloud.
    
    depth_map: D ∈ R^(H×W)
    ray_map: M ∈ R^(H×W×6)
    
    Returns: point cloud P ∈ R^(H×W×3)
    """
    # Extract ray components
    origins = ray_map[:,:,:3]     # t per pixel
    directions = ray_map[:,:,3:]  # d per pixel (unnormalized)
    
    # 3D point = origin + depth * direction
    # P = t + D(u,v) · d
    points = origins + depth_map.unsqueeze(-1) * directions
    
    return points  # Each pixel maps to a 3D point

def multi_view_fusion(depth_maps, ray_maps):
    """
    Fuse multiple views into unified point cloud.
    """
    all_points = []
    for depth, rays in zip(depth_maps, ray_maps):
        points = fuse_depth_ray(depth, rays)
        all_points.append(points.reshape(-1, 3))
    
    # Concatenate all views
    unified_cloud = torch.cat(all_points, dim=0)
    
    return unified_cloud
```

### 4.3 Teacher Model Construction

Teacher improvements over Depth Anything 2:

**1. Data scaling** — 20+ synthetic datasets:
HyperSim, TartanAir, IRS, vKITTI2, BlendedMVS, SPRING, MVSSynth, UnrealStereo4K,
GTA-SfM, TauAgent, KenBurns, MatrixCity, EDEN, ReplicaGSO, UrbanSyn,
PointOdyssey, Structured3D, Objaverse, Trellis, OmniObject

**2. Depth representation** — exponential depth (not disparity):
```python
# DA2: scale-shift-invariant disparity
# DA3: scale-shift-invariant depth (exponential)
def predict_depth_teacher(image):
    log_depth = model(image)
    depth = torch.exp(log_depth)  # Enhanced near-camera sensitivity
    return depth
```

**3. Distance-weighted surface normal loss**:
```python
def normal_loss(pred_depth, gt_depth):
    """Sample 4 neighbors, weight by distance from center."""
    normals = []
    for i in range(4):
        n_i = compute_normal(pred_depth, neighbor_i)
        normals.append(n_i)
    
    # Weight by inverse distance
    weights = [sum(norm(n_j) for j in range(4)) - norm(n_i) for n_i in normals]
    
    # Mean normal closer to true local surface
    n_m = sum(w_i * normalize(n_i) for w_i, n_i in zip(weights, normals))
    
    return angular_error(pred_n_m, gt_n_m) + sum(angular_error(pred_n_i, gt_n_i))
```

## 5. Results

### 5.1 Pose-Geometry Benchmark

5 datasets, 89+ scenes (object-level to indoor/outdoor):

| Dataset | DA3 vs VGGT (Pose) | DA3 vs VGGT (Geo) |
|---------|-------------------|------------------|
| HiRoom | +37% | +25% |
| ETH3D | +34% | +22% |
| DTU | +38% | +24% |
| 7Scenes | +32% | +21% |
| ScanNet++ | +38% | +26% |
| **Average** | **+35.7%** | **+23.6%** |

### 5.2 Monocular Depth

Compared to Depth Anything 2:

| Metric | DA2 | DA3 | DA3-Teacher |
|--------|-----|-----|-------------|
| Accuracy | 90.3 | 92.4 | 94.6 |

### 5.3 Feed-Forward 3DGS

DA3 as backbone for novel view synthesis substantially outperforms specialized
models. Enhanced geometric reconstruction directly correlates with improved NVS.

## 6. Hydrogen Relevance

### 6.1 Geometry Pillar Integration

Depth-ray representation as bounded type:

```purescript
-- Per-pixel ray as bounded type
type Ray =
  { origin :: Point3D      -- t
  , direction :: Vector3D  -- d (unnormalized)
  }

-- Ray map for full image
type RayMap = Array2D Ray  -- H×W×6

-- Depth-ray fusion is pure element-wise operation
fuseDepthRay :: DepthMap -> RayMap -> PointCloud
fuseDepthRay depth rays = zipWith fuse depth rays
  where
    fuse d r = r.origin + scale d r.direction
```

### 6.2 Key Patterns for Hydrogen

1. **Minimal prediction targets**: Depth + ray is sufficient for all 3D tasks
   (no need for complex multi-task heads)

2. **Input-adaptive architecture**: Same model handles 1 view or N views — 
   graceful degradation principle

3. **Teacher-student for noisy data**: Synthetic → real alignment via RANSAC

4. **DLT for camera recovery**: Standard linear algebra, no learned components

### 6.3 Training Configuration

| Parameter | Value |
|-----------|-------|
| GPUs | 128 H100 |
| Steps | 200k (8k warmup) |
| Base resolution | 504×504 |
| Views per batch | [2, 18] uniform |
| Pose conditioning prob | 0.2 |
| Teacher transition | 120k steps |

### 6.4 Bounded Guarantees

| Property | Bound |
|----------|-------|
| Ray origin | R³ (camera center) |
| Ray direction | R³ (unnormalized) |
| Depth | R⁺ (positive) |
| Camera quaternion | S³ (unit sphere) |
| FOV | [0°, 180°] bounded |

---

*Synthesized for the Hydrogen project — unified visual geometry as bounded primitives*
