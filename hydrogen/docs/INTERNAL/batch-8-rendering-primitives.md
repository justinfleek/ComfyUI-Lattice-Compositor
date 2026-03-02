# Batch 8: Rendering Primitives, Quantization, and Constraint Transport

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // batch // 8 // synthesis
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Synthesized:** 2026-02-26
**Papers Analyzed:** 7
**Focus Areas:** SDF rendering, FP4 quantization, depth-ray geometry, fluid simulation

────────────────────────────────────────────────────────────────────────────────
                                                               // paper // index
────────────────────────────────────────────────────────────────────────────────

## Papers in This Batch

| # | Paper | Priority | Domain |
|---|-------|----------|--------|
| 8.1 | DISTANCE_FIELD_TEXTURES (Valve) | ⭐⭐⭐⭐⭐ | Text/Icon rendering |
| 8.2 | PATHTRACING_SDF_GRIDS (NVIDIA) | ⭐⭐⭐⭐ | 3D SDF ray tracing |
| 8.3 | NVFP4_PRETRAINING | ⭐⭐⭐⭐ | FP4 training at scale |
| 8.4 | FOUR_OVER_SIX_NVFP4 | ⭐⭐⭐⭐ | Adaptive block scaling |
| 8.5 | DEPTH_ANYTHING_3 | ⭐⭐⭐⭐ | Depth-ray geometry |
| 8.6 | STREAM_FUNCTION_SOLVER | ⭐⭐⭐ | Fluid simulation |
| 8.7 | VA_PI_PIXEL_ALIGNMENT | ⭐⭐⭐ | Token-pixel alignment |

────────────────────────────────────────────────────────────────────────────────
                                                               // paper // 8.1
────────────────────────────────────────────────────────────────────────────────

## 8.1: Distance Field Textures (Valve, SIGGRAPH 2007)

**Source:** Chris Green, Valve Corporation
**Impact:** Industry standard for text/icon rendering in games

### Core Contribution

Store **signed distance to edge** instead of coverage. Bilinear filtering
reconstructs sharp edges at any magnification because distance IS linear.

| Metric | Value |
|--------|-------|
| Compression | 64:1 (4096² → 64² with quality preservation) |
| Performance | Zero overhead vs standard textures |
| Hardware | Works on ALL GPUs (even shader-free via alpha test) |

### Key Insight

Coverage is a step function — bilinear interpolation creates "wiggles".
Distance is linear — bilinear interpolation correctly places edges.

```
SDF Value:  0.0 = max outside, 0.5 = edge, 1.0 = max inside
```

### Algorithms to Extract

**1. SDF Generation (offline):**
- For each output texel, find nearest opposite-state texel in high-res source
- Compute Euclidean distance, apply sign, normalize to [0,1]
- Brute-force search is acceptable (offline, bounded spread)

**2. SDF Rendering (shader):**
```hlsl
float dist = texture.a;
float alpha = smoothstep(0.5 - edgeWidth, 0.5 + edgeWidth, dist);
```

**3. Dynamic Effects (all runtime-controllable):**
- Outline: color texels between two distance thresholds
- Glow: substitute color for dist < 0.5
- Shadow: offset UV lookup
- Sharp corners: multi-channel AND (min of two SDFs)

### Hydrogen Integration

```purescript
-- SDF value is bounded [0, 1], 0.5 = edge
newtype SDFValue = SDFValue (BoundedNumber 0.0 1.0)

-- Complete SDF texture specification
type SDFTexture =
  { data :: Array SDFValue
  , width :: PositiveInt
  , height :: PositiveInt
  , spread :: BoundedInt 1 64
  }

-- Effects as composable configuration
type SDFEffects =
  { outline :: Maybe { min :: SDFValue, max :: SDFValue, color :: SRGB }
  , glow :: Maybe { range :: SDFValue, color :: SRGB }
  , shadow :: Maybe { offset :: Point2D, color :: SRGB }
  }
```

### Why CRITICAL Priority

- **Text rendering**: Every UI needs sharp text at any DPI
- **Icons**: Resolution-independent, memory-efficient
- **Deterministic**: Same SDF + shader = same pixels across all agents
- **Bounded types**: SDFValue in [0,1] maps perfectly to Schema atoms

────────────────────────────────────────────────────────────────────────────────
                                                               // paper // 8.2
────────────────────────────────────────────────────────────────────────────────

## 8.2: Ray Tracing SDF Grids (NVIDIA, JCGT 2022)

**Source:** Hansson Söderlund, Evans, Akenine-Möller (NVIDIA)
**Domain:** 3D SDF rendering for path tracing

### Core Contribution

Optimized ray-surface intersection for trilinearly interpolated SDF grids.

| Improvement | Before | After |
|-------------|--------|-------|
| Cubic coefficients | 161 ops | 37 ops |
| Normal computation | 54 ops | 30 ops |
| Traversal | Sphere tracing | SVS + BVH (fastest) |

### Key Insight

Trilinear interpolation of 8 corner SDFs creates a **cubic polynomial** surface.
The zero level set has 31 possible topologies (not 14 like marching cubes assumes).

Substituting ray equation into surface equation yields:
```
c₃t³ + c₂t² + c₁t + c₀ = 0
```

### Algorithms to Extract

**1. Optimized Cubic Coefficients (37 ops):**
Precompute k-constants from 8 corners, then compute c₀-c₃ via shared intermediates.

**2. Marmitt Polynomial Splitting:**
Solve derivative (quadratic) to find splitting points. Check sign changes
to locate roots without iteration — enables early shadow ray termination.

**3. Dual Voxel Normals (novel):**
Evaluate 8 neighboring voxels' analytic normals at hit point, trilinearly blend.
Result: C0-continuous normals across voxel boundaries (1-7% overhead).

### Hydrogen Integration

```purescript
-- SDF grid with proven bounds
newtype SDFGrid = SDFGrid
  { resolution :: Size3D PositiveInt
  , bounds :: BoundingBox3D
  , values :: Array SignedDistance  -- 8-bit snorm, clamped [-1,1]
  }

-- Cubic solver output (bounded by voxel traversal)
type RayHit =
  { t :: NonNegative Number  -- ray parameter
  , normal :: UnitVector3D   -- normalized, from dual voxel interp
  , voxel :: VoxelIndex
  }
```

### Why HIGH Priority

- **3D UI elements**: Smooth shapes without tessellation
- **Motion graphics**: SDF morphing for LATTICE
- **Deterministic**: Analytic solver = reproducible intersections

────────────────────────────────────────────────────────────────────────────────
                                                               // paper // 8.3
────────────────────────────────────────────────────────────────────────────────

## 8.3: NVFP4 Pretraining (NVIDIA, 2025)

**Source:** NVIDIA, arXiv:2509.25149
**Scale:** 12B parameters, 10T tokens

### Core Contribution

First demonstration of FP4 training at trillion-token scale with near-FP8 quality.

| Metric | FP8 | NVFP4 |
|--------|-----|-------|
| MMLU-Pro | 62.62% | 62.58% |
| Loss gap | baseline | < 1.5% |
| Token efficiency | 1.0x | 0.64x vs MXFP4 |

### NVFP4 vs MXFP4

| Property | MXFP4 | NVFP4 |
|----------|-------|-------|
| Block size | 32 | **16** |
| Scale format | E8M0 (power-of-2 only) | **E4M3** (fractional) |
| Tensor scale | None | **FP32** |

### Four Essential Components

1. **Mixed Precision**: ~15% of layers in BF16 (final blocks need dynamic range)
2. **Random Hadamard Transform**: Disperses outliers to Gaussian (Wgrad only)
3. **2D Block Scaling**: 16×16 for weights (consistent forward/backward)
4. **Stochastic Rounding**: For gradients only (reduces quantization bias)

### FP4 E2M1 Representable Values

```
±{0, 0.5, 1, 1.5, 2, 3, 4, 6}
```

Non-uniform steps: 0.5 for [0,2], 1.0 for [2,4], 2.0 for [4,6]

### Hydrogen Integration

```purescript
-- FP4 E2M1 as bounded enumeration
data FP4Value
  = FP4_0 | FP4_Half | FP4_1 | FP4_1Half
  | FP4_2 | FP4_3 | FP4_4 | FP4_6

-- Block-scaled representation
type NVFP4Block =
  { values :: Array16 FP4Value  -- exactly 16 values
  , scale :: FP8_E4M3
  }

type NVFP4Tensor =
  { blocks :: Array NVFP4Block
  , tensorScale :: Number  -- FP32
  }
```

### Why HIGH Priority

- **Memory efficiency**: 4× compression for GPU buffers
- **Blackwell native**: Hardware tensor core support
- **Bounded by construction**: FP4 values are enumerable

────────────────────────────────────────────────────────────────────────────────
                                                               // paper // 8.4
────────────────────────────────────────────────────────────────────────────────

## 8.4: Four Over Six Adaptive Scaling (MIT/NVIDIA, 2026)

**Source:** Cook et al., MIT + NVIDIA, arXiv:2512.02010
**Problem:** FP4's non-uniform steps create large errors at 66-100% of block max

### Core Contribution

Adaptively scale some blocks to max=4 instead of max=6, selected by MSE.

| Approach | Near-max error |
|----------|----------------|
| Standard (max=6) | Values at 75% → rounds to 4 or 6 (17% error) |
| **4/6 (max=4)** | Values at 75% → rounds to 3 (0% error) |

### Key Insight

Block-scaled formats already handle outliers well (each block has own scale).
The remaining error comes from **near-maximal values** — 4/6 addresses this directly.

### Algorithm

```python
for each block:
    mse_6 = quantize_and_measure(block, max=6)
    mse_4 = quantize_and_measure(block, max=4)
    if mse_4 < mse_6:
        use max=4
    else:
        use max=6
```

### Results

| Method | Improvement vs BF16 gap |
|--------|------------------------|
| AWQ + 4/6 | **19.9% closer** |
| RTN + 4/6 | 3.0% closer |
| Pre-training + 4/6 | 22.3% closer |

### Hydrogen Integration

```purescript
-- 4/6 selection is deterministic given input
type FourOverSixBlock =
  { values :: Array16 FP4Value
  , scale :: FP8_E4M3
  , usedMax4 :: Boolean  -- true if max=4 was selected
  }

-- Selection criterion
selectScale :: Array Number -> { max4Mse :: Number, max6Mse :: Number }
selectScale values =
  let mse4 = computeMSE (quantizeTo max4) values
      mse6 = computeMSE (quantizeTo max6) values
  in { max4Mse: mse4, max6Mse: mse6 }
```

### Why HIGH Priority

- **Complements 8.3**: Direct improvement to NVFP4
- **Deterministic**: MSE selection is reproducible
- **Low overhead**: <15% added to quantization operation

────────────────────────────────────────────────────────────────────────────────
                                                               // paper // 8.5
────────────────────────────────────────────────────────────────────────────────

## 8.5: Depth Anything 3 (ByteDance, 2025)

**Source:** Lin et al., ByteDance Seed, arXiv:2511.10647
**Domain:** Multi-view geometry from arbitrary inputs

### Core Contribution

Predict **depth + ray maps** from any number of images, with or without camera poses.

| vs VGGT | Improvement |
|---------|-------------|
| Camera pose accuracy | +35.7% |
| Geometric accuracy | +23.6% |

### Key Insight: Depth-Ray Representation

Instead of predicting rotation matrices (orthogonality constraints), predict
per-pixel rays directly:

```
Ray r = (t, d)  where t = origin, d = direction
3D point P = t + D(u,v) · d
```

No orthogonality to enforce. Dense ray map + depth = consistent point cloud.

### Architecture

```
DINOv2 backbone (no specialization needed)
  ↓
First 2/3 layers: within-view attention
Next 1/3 layers: alternating cross-view / within-view
  ↓
Dual-DPT Head → Depth (H×W×1) + Ray (H×W×6)
```

**Input-adaptive**: Single image reduces to monocular depth with no extra cost.

### Algorithms to Extract

**1. Depth-Ray Fusion:**
```python
points = ray_origins + depth.unsqueeze(-1) * ray_directions
```

**2. Camera Recovery (DLT):**
- Average ray origins → camera center
- Solve H = K·R via DLT from pixel↔ray correspondences
- RQ decomposition → K, R

### Hydrogen Integration

```purescript
-- Per-pixel ray as bounded type
type Ray =
  { origin :: Point3D
  , direction :: Vector3D  -- unnormalized, preserves projection scale
  }

type RayMap = Array2D Ray  -- H×W

-- Depth-ray fusion is pure element-wise
fuseDepthRay :: DepthMap -> RayMap -> PointCloud
fuseDepthRay depth rays = zipWith fuse depth rays
  where fuse d r = r.origin + scale d r.direction
```

### Why HIGH Priority

- **Minimal prediction targets**: Depth + ray suffices for all 3D tasks
- **Input-adaptive**: Same model handles 1-N views gracefully
- **Pure fusion**: Point cloud from element-wise ops (no learned decoder)

────────────────────────────────────────────────────────────────────────────────
                                                               // paper // 8.6
────────────────────────────────────────────────────────────────────────────────

## 8.6: Stream Function Solver (IST Austria, SCA)

**Source:** Ando, Thuerey, Wojtan (IST Austria, TUM)
**Domain:** Fluid simulation for graphics

### Core Contribution

Replace pressure projection with stream function solve for liquid simulation.

| Property | Pressure Projection | Stream Function |
|----------|--------------------|-----------------| 
| Divergence-free | Approximate (tolerance) | **Exact by construction** |
| Two-phase | Requires both phases | **Liquid only** (air is free) |
| Stability | Degrades at high density ratio | **Improves** as ρ_air → 0 |

### Key Insight

```
∇·(∇×Ψ) = 0    (mathematical identity, always)
```

Curl of any vector field is divergence-free. Instead of finding pressure that
makes velocity divergence-free, solve directly for stream function Ψ where u = ∇×Ψ.

### Algorithm

```
1. Compute u* (velocity after advection)
2. Solve: ∇×(ρ∇×Ψ) = ∇×(ρu*)
3. Extract: u = ∇×Ψ  (guaranteed divergence-free)
```

**Air disappears**: If ρ_air = 0, system entries vanish outside liquid.
Bubbles form naturally without simulating gas phase.

### Hydrogen Integration

```purescript
-- Stream function guarantees divergence-free output
newtype StreamFunction = StreamFunction (Array3D Vec3)

-- Type-level guarantee: curl output is divergence-free
newtype DivergenceFreeVelocity = DivergenceFreeVelocity (Array3D Vec3)

curl :: StreamFunction -> DivergenceFreeVelocity
-- Return type PROVES result is divergence-free (not checked, constructed)
```

### Why MEDIUM Priority

- **Fluid effects**: Liquid UI elements, flowing animations
- **Correctness by construction**: No volume drift over time
- **Not immediate need**: 2D UI focus first, 3D fluid later

────────────────────────────────────────────────────────────────────────────────
                                                               // paper // 8.7
────────────────────────────────────────────────────────────────────────────────

## 8.7: VA-π Pixel Alignment (NUS/HUST, 2025)

**Source:** Liao et al., NUS/HUST, arXiv:2512.19680
**Problem:** Token-level likelihood doesn't guarantee pixel-level quality

### Core Contribution

Treat AR image generation as RL, using pixel reconstruction as intrinsic reward.

| Metric | Before | After | Training Time |
|--------|--------|-------|---------------|
| FID | 14.36 | **7.65** | 25 min |
| IS | 86.55 | **116.70** | (1% ImageNet) |

### Key Insight

AR models can produce high-likelihood token sequences that decode to garbage images
("off-manifold" sequences). VA-π provides **direct pixel-level supervision**.

### The ELBO Formulation

```
log p(I) ≥ E[log p(I|x)]         ← Reconstruction term (pixel loss)
          - KL(q(x|I) || π(x))   ← Prior regularization (preserve AR dist)
```

Uses GRPO (Group Relative Policy Optimization):
- Sample G outputs per image
- Compute reconstruction reward R = -MSE - λ·LPIPS
- Normalize advantages within group
- PPO-style clipped update

### Algorithm Sketch

```python
for batch of images I:
    x* = encode(I)              # ground-truth tokens
    x̃* = corrupt(x*, ξ=0.5)     # add noise (exposure bias)
    samples = [sample(π_θ, x̃*) for _ in range(G)]
    rewards = [-reconstruction_loss(decode(x), I) for x in samples]
    advantages = normalize(rewards)
    loss = -grpo_loss(samples, advantages) + β * CE(x̃*, x*)
```

### Hydrogen Relevance (Conceptual)

**Token-Pixel Gap ↔ Element-Render Gap:**

```
VA-π:     Tokens (optimized) → Decoder → Pixels (what we care about)
Hydrogen: Elements (specified) → Target → Pixels (what we care about)
```

Both have intermediate representations that may be "valid" but produce poor output.
The ELBO pattern (reconstruction + prior) could apply to UI quality metrics.

### Why MEDIUM Priority

- **Conceptual insight**: Token-pixel alignment parallels element-render alignment
- **Not directly implementable**: Hydrogen doesn't train generative models (yet)
- **Pattern extraction**: ELBO decomposition useful for future quality metrics

────────────────────────────────────────────────────────────────────────────────
                                                      // integration // summary
────────────────────────────────────────────────────────────────────────────────

## Integration Summary

| Paper | Priority | Key Takeaway | Integration Target |
|-------|----------|--------------|-------------------|
| **SDF Textures** | ⭐⭐⭐⭐⭐ | Distance-based text/icons | `Schema/Geometry/SDF/` |
| **SDF Ray Tracing** | ⭐⭐⭐⭐ | 37-op cubic solver | `GPU/SDF/` |
| **NVFP4 Pretraining** | ⭐⭐⭐⭐ | 4 components for FP4 | `GPU/Quantization/` |
| **Four Over Six** | ⭐⭐⭐⭐ | Adaptive max=4/6 | `GPU/Quantization/` |
| **Depth Anything 3** | ⭐⭐⭐⭐ | Depth + ray = 3D | `Schema/Spatial/` |
| **Stream Function** | ⭐⭐⭐ | Divergence-free by construction | `Schema/Physics/` |
| **VA-π** | ⭐⭐⭐ | Pixel-level alignment | Conceptual |

### Immediate Actions (Batch 8)

1. **SDF Text Rendering** — Implement SDFTexture type and WebGL shader generation
2. **FP4 Quantization Module** — NVFP4 + Four Over Six with proven bounds
3. **Depth-Ray Types** — Add Ray, RayMap, depth-ray fusion to Spatial pillar

### Cross-Batch Synergies

| Earlier Paper | Batch 8 Paper | Synergy |
|---------------|---------------|---------|
| NumFuzz/Bean | NVFP4/4Over6 | Graded error bounds for quantization |
| Landauer | NVFP4 | Precision = measured information |
| Design2GarmentCode | SDF Textures | Both produce resolution-independent output |
| GAIA-2 | Depth Anything 3 | Multi-view consistency patterns |

────────────────────────────────────────────────────────────────────────────────
                                                               // schema // atoms
────────────────────────────────────────────────────────────────────────────────

## Schema Atoms Identified

### From SDF Papers (8.1, 8.2)

```purescript
-- Geometry Pillar additions
newtype SDFValue = SDFValue (BoundedNumber 0.0 1.0)
newtype SignedDistance = SignedDistance Number  -- finite, signed
newtype SpreadFactor = SpreadFactor (BoundedInt 1 64)

-- SDF texture molecule
type SDFTexture =
  { data :: Array SDFValue
  , width :: PositiveInt
  , height :: PositiveInt
  , spread :: SpreadFactor
  }

-- SDF effects compound
type SDFEffects =
  { outline :: Maybe OutlineConfig
  , glow :: Maybe GlowConfig
  , shadow :: Maybe ShadowConfig
  }
```

### From FP4 Papers (8.3, 8.4)

```purescript
-- GPU Pillar additions
data FP4Value = FP4_0 | FP4_Half | FP4_1 | FP4_1Half 
              | FP4_2 | FP4_3 | FP4_4 | FP4_6

type NVFP4Block =
  { values :: Array16 FP4Value
  , scale :: FP8_E4M3
  , usedMax4 :: Boolean  -- Four Over Six flag
  }
```

### From Depth-Ray Paper (8.5)

```purescript
-- Spatial Pillar additions
type Ray =
  { origin :: Point3D
  , direction :: Vector3D
  }

type RayMap = Array2D Ray

type DepthRayFusion =
  { depth :: DepthMap
  , rays :: RayMap
  , points :: PointCloud  -- derived: origin + depth * direction
  }
```

### From Stream Function Paper (8.6)

```purescript
-- Physics Pillar additions (for future fluid effects)
newtype StreamFunction = StreamFunction (Array3D Vec3)
newtype DivergenceFreeVelocity = DivergenceFreeVelocity (Array3D Vec3)

-- Type-level proof of divergence-free property
curl :: StreamFunction -> DivergenceFreeVelocity
```

────────────────────────────────────────────────────────────────────────────────
                                                      // implementation // plan
────────────────────────────────────────────────────────────────────────────────

## Implementation Targets

### Target 1: SDF Text Rendering (Week 1-2)

**Priority:** CRITICAL — Every UI needs sharp text

**Files to create/modify:**

```
src/Hydrogen/Schema/Geometry/SDF/
  ├── SDFValue.purs       -- SDFValue newtype, bounded [0,1]
  ├── SDFTexture.purs     -- Texture specification
  ├── SDFEffects.purs     -- Outline, glow, shadow configs
  └── index.purs          -- Re-exports

src/Hydrogen/Target/WebGL/
  └── SDFShader.purs      -- Shader generation for SDF rendering
```

**Key types:**

```purescript
-- Atom: distance value bounded to valid range
newtype SDFValue = SDFValue (BoundedNumber 0.0 1.0)

derive instance Eq SDFValue
derive instance Ord SDFValue

-- Edge detection: distance == 0.5
isEdge :: SDFValue -> Boolean
isEdge (SDFValue n) = abs (n - 0.5) < 0.001

-- Molecule: complete texture specification
type SDFTexture =
  { data :: Array SDFValue
  , width :: PositiveInt
  , height :: PositiveInt
  , spread :: BoundedInt 1 64  -- spread factor for distance normalization
  }

-- Compound: composable visual effects
type SDFEffects =
  { outline :: Maybe { innerDist :: SDFValue, outerDist :: SDFValue, color :: SRGB }
  , glow :: Maybe { range :: SDFValue, color :: SRGB, falloff :: Exponential }
  , shadow :: Maybe { offset :: Point2D, color :: SRGB, softness :: SDFValue }
  }
```

**Shader generation:**

```purescript
-- Generate GLSL fragment shader for SDF rendering
generateSDFShader :: SDFEffects -> String
-- Output is deterministic: same effects = same shader code
```

**Verification:**
- Unit tests for SDFValue bounds
- Property tests: `forall v. isInRange (unSDFValue v) 0.0 1.0`
- Visual regression tests comparing generated shaders

────────────────────────────────────────────────────────────────────────────────

### Target 2: FP4 Quantization Module (Week 2-3)

**Priority:** HIGH — Memory efficiency for GPU buffers

**Files to create/modify:**

```
src/Hydrogen/GPU/Quantization/
  ├── FP4.purs            -- FP4Value enum, NVFP4Block
  ├── FourOverSix.purs    -- Adaptive scaling selection
  └── index.purs          -- Re-exports

proofs/Hydrogen/GPU/
  └── FP4Bounds.lean      -- Lean proofs for FP4 value bounds
```

**Key types:**

```purescript
-- FP4 E2M1 has exactly 16 representable values (8 positive, 8 negative)
data FP4Value
  = FP4_Zero
  | FP4_Half       -- 0.5
  | FP4_One        -- 1.0
  | FP4_OneHalf    -- 1.5
  | FP4_Two        -- 2.0
  | FP4_Three      -- 3.0
  | FP4_Four       -- 4.0
  | FP4_Six        -- 6.0

derive instance Eq FP4Value
derive instance Ord FP4Value

-- Convert to/from Number (lossy)
toNumber :: FP4Value -> Number
fromNumber :: Number -> FP4Value  -- nearest quantization

-- 16-element block with scale
type NVFP4Block =
  { values :: Array16 FP4Value    -- exactly 16 values
  , scale :: FP8_E4M3             -- block scale factor
  , tensorScale :: Number         -- FP32 tensor-level scale
  }

-- Four Over Six selection
type FourOverSixBlock =
  { values :: Array16 FP4Value
  , scale :: FP8_E4M3
  , usedMax4 :: Boolean           -- true if max=4 selected via MSE
  }

-- Selection is deterministic
selectScaling :: Array Number -> { useMax4 :: Boolean, mse :: Number }
```

**Lean proofs required:**

```lean
-- All FP4 values are bounded
theorem fp4_bounded : ∀ v : FP4Value, 0 ≤ toNumber v ∧ toNumber v ≤ 6

-- Quantization is idempotent
theorem quantize_idempotent : ∀ v : FP4Value, fromNumber (toNumber v) = v

-- Four Over Six selection is deterministic
theorem fos_deterministic : ∀ block, selectScaling block₁ = selectScaling block₂ → block₁ = block₂
```

**Verification:**
- Exhaustive enumeration tests (only 8 positive values)
- Round-trip property: `toNumber (fromNumber x)` within quantization error
- MSE selection reproducibility tests

────────────────────────────────────────────────────────────────────────────────

### Target 3: Depth-Ray Spatial Types (Week 3-4)

**Priority:** HIGH — Foundation for 3D UI elements

**Files to create/modify:**

```
src/Hydrogen/Schema/Spatial/
  ├── Ray.purs            -- Ray type (origin + direction)
  ├── RayMap.purs         -- 2D array of rays
  ├── DepthRayFusion.purs -- Depth + Ray → PointCloud
  └── index.purs          -- Re-exports (update existing)
```

**Key types:**

```purescript
-- Ray as pure data (not normalized, preserves projection scale)
type Ray =
  { origin :: Point3D
  , direction :: Vector3D
  }

-- Evaluate ray at parameter t
evaluate :: Ray -> Number -> Point3D
evaluate ray t = ray.origin + scale t ray.direction

-- 2D array of rays (one per pixel)
newtype RayMap = RayMap (Array2D Ray)

-- Depth-ray fusion is pure element-wise operation
fuseDepthRay :: DepthMap -> RayMap -> PointCloud
fuseDepthRay (DepthMap depths) (RayMap rays) =
  PointCloud $ zipWith fuse depths rays
  where
    fuse :: Number -> Ray -> Point3D
    fuse d ray = evaluate ray d
```

**Integration with existing Spatial pillar:**

```purescript
-- Extend existing Point3D, Vector3D
-- Add Ray to re-exports
-- Ensure consistency with BoundingBox3D
```

**Verification:**
- Property: `fuseDepthRay` is deterministic
- Property: fusion of uniform depth produces coplanar points
- Integration tests with existing Spatial types

────────────────────────────────────────────────────────────────────────────────

### Target 4: SDF Grid Ray Tracing (Week 4-5)

**Priority:** HIGH — 3D shapes without tessellation

**Files to create/modify:**

```
src/Hydrogen/GPU/SDF/
  ├── SDFGrid.purs        -- 3D SDF grid type
  ├── CubicSolver.purs    -- 37-op cubic coefficient computation
  ├── RayIntersect.purs   -- Ray-SDF intersection
  └── index.purs          -- Re-exports
```

**Key algorithms from paper:**

```purescript
-- Optimized cubic coefficients (37 ops vs 161)
computeCubicCoeffs :: SDFGrid -> Ray -> VoxelIndex -> CubicCoeffs
-- c₃t³ + c₂t² + c₁t + c₀ = 0

-- Marmitt polynomial splitting for root finding
findRoot :: CubicCoeffs -> Number -> Number -> Maybe Number
-- Returns smallest positive t in range, if any

-- Complete intersection
intersectRay :: SDFGrid -> Ray -> Maybe RayHit
```

**Verification:**
- Compare with reference implementation
- Known-shape tests (sphere SDF, box SDF)
- Numerical stability at voxel boundaries

────────────────────────────────────────────────────────────────────────────────

### Target 5: Stream Function Types (Week 5-6)

**Priority:** MEDIUM — Future fluid effects

**Files to create/modify:**

```
src/Hydrogen/Schema/Physics/
  ├── StreamFunction.purs         -- StreamFunction newtype
  ├── DivergenceFree.purs         -- DivergenceFreeVelocity with type-level proof
  └── index.purs                  -- Re-exports
```

**Key insight encoded in types:**

```purescript
-- The curl of any vector field is divergence-free (mathematical identity)
-- This is encoded at the type level, not checked at runtime

newtype StreamFunction = StreamFunction (Array3D Vec3)
newtype DivergenceFreeVelocity = DivergenceFreeVelocity (Array3D Vec3)

-- curl :: StreamFunction -> DivergenceFreeVelocity
-- The return type PROVES the result is divergence-free

-- Implementation
curl :: StreamFunction -> DivergenceFreeVelocity
curl (StreamFunction psi) = DivergenceFreeVelocity (computeCurl psi)
  where
    computeCurl :: Array3D Vec3 -> Array3D Vec3
    -- Standard finite difference curl operator
```

**Verification:**
- Numerical verification that `divergence (curl ψ) ≈ 0` within floating-point tolerance
- Lean proof of the mathematical identity `∇·(∇×Ψ) = 0`

────────────────────────────────────────────────────────────────────────────────

### Implementation Order

```
Week 1-2: SDF Text Rendering (CRITICAL)
  └── Unblocks: Text rendering for LATTICE/COMPASS

Week 2-3: FP4 Quantization (HIGH)
  └── Unblocks: Memory-efficient GPU buffers

Week 3-4: Depth-Ray Spatial (HIGH)
  └── Unblocks: 3D UI element composition

Week 4-5: SDF Grid Ray Tracing (HIGH)
  └── Unblocks: Smooth 3D shapes without mesh

Week 5-6: Stream Function (MEDIUM)
  └── Unblocks: Future fluid animation effects
```

### Success Criteria

- [ ] All new types have bounded representations (no unbounded Numbers)
- [ ] All modules compile independently with explicit imports
- [ ] Property tests verify determinism: same input = same output
- [ ] Lean proofs for mathematical invariants (FP4 bounds, curl identity)
- [ ] Integration with existing Schema pillars verified
- [ ] No TODOs, no stubs, no placeholders

────────────────────────────────────────────────────────────────────────────────

                                                          — Opus 4.5 // 2026-02-26

