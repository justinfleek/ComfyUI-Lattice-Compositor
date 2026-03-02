# TENSOR RENDERING ARCHITECTURE

> "The screen is a lie. What exists is the tensor."

## The Problem

Traditional rendering thinks in pixels:
```
1920 × 1080 pixels × 4 channels × 60 fps = 498 MB/sec
```

At billion-agent scale, this is impossible:
```
498 MB/sec × 1B agents = 498 Exabytes/sec
```

Even with perfect parallelization across all GPUs on Earth, this cannot work.

## The Insight

**Pixels are not the atomic unit. Tensors are.**

A 1920×1080 display at 60fps is actually:
```purescript
ViewportTensor
  { pixelShape: shape4d (dim 1) (dim 4) (dim 1080) (dim 1920)  -- NCHW
  , frameRate: fps60
  , physicalExtent: Just (meters 0.53, meters 0.30)  -- 24" diagonal
  , latentShape: shape4d (dim 1) (dim 4) (dim 135) (dim 240)   -- 8× downscale
  }
```

The **latent shape** is what matters for computation:
- 135 × 240 × 4 = 129,600 latent values per frame
- vs 1920 × 1080 × 4 = 8,294,400 pixel values

That's a **64× reduction** in compute requirements.

## Physical Size Independence

Your 20ft screen question reveals the key insight:

```
Screen A: 1920×1080 on 24" monitor (92 PPI)
Screen B: 1920×1080 on 20ft LED wall (8 PPI)
```

**Same tensor shape. Same compute. Different physical interpretation.**

The tensor doesn't know or care about physical size. Physical size is metadata
for the display hardware, not the compute graph.

```purescript
-- Same latent computation
latent :: Tensor [1, 4, 135, 240]

-- Different physical manifestation
displayA :: PhysicalExtent
displayA = { width: inches 20.9, height: inches 11.8, ppi: 92.0 }

displayB :: PhysicalExtent
displayB = { width: feet 20.0, height: feet 11.25, ppi: 8.0 }
```

## The ViewportTensor Type

A viewport is not a rectangle of pixels. It's a **tensor computation target**:

```purescript
newtype ViewportTensor = ViewportTensor
  { -- Pixel-space shape (what the display shows)
    pixelShape :: Shape        -- [batch, channels, height, width]
    
    -- Latent-space shape (what we compute)
  , latentShape :: Shape       -- [batch, latent_channels, h/8, w/8]
  
    -- Physical extent (optional — for DPI-aware rendering)
  , physicalExtent :: Maybe PhysicalExtent
  
    -- Device properties
  , devicePixelRatio :: DevicePixelRatio
  , colorSpace :: ColorSpace   -- sRGB, P3, Rec2020, etc.
  
    -- Temporal properties
  , frameRate :: FrameRate
  , timeBase :: TimeBase       -- For synchronization
  
    -- Compute properties
  , preferredDtype :: DType    -- float16, float32, bfloat16
  , memoryLayout :: Layout     -- NCHW, NHWC
  }
```

## The ComputeKernel Abstraction

A kernel is a **pure description** of a GPU computation:

```purescript
data ComputeKernel
  = KernelDiffusion DiffusionParams    -- Latent diffusion (SD, SDXL, etc.)
  | KernelNoise NoiseParams            -- Procedural noise (FBM, Perlin, etc.)
  | KernelConvolution ConvParams       -- Conv2D, DepthwiseConv, etc.
  | KernelAttention AttentionParams    -- Self/cross attention
  | KernelCustom CustomKernel          -- User-defined WGSL/compute shader

-- Every kernel has:
-- 1. Input tensor shape(s)
-- 2. Output tensor shape
-- 3. Parameters (weights, config)
-- 4. Dispatch dimensions (workgroup size, count)

type KernelSignature =
  { inputs :: Array TensorSpec
  , output :: TensorSpec
  , params :: KernelParams
  , dispatch :: DispatchDimensions
  }
```

## FillDiffusion: Reactive Generative Fills

A button's fill is no longer "blue" or "gradient." It's a **live computation**:

```purescript
data Fill
  = FillNone
  | FillSolid RGB
  | FillGradient Gradient
  | FillNoise FBM
  | FillDiffusion DiffusionFill    -- NEW: Live diffusion model
  | FillCompute ComputeFill        -- NEW: Arbitrary kernel

type DiffusionFill =
  { -- Model specification
    model :: ModelRef              -- Which diffusion model (SD 1.5, SDXL, custom)
  , latentShape :: Shape           -- Output latent dimensions
  
    -- Generation parameters
  , promptEmbedding :: VecN Number -- Text/CLIP embedding (768 or 1024 dim)
  , negativeEmbedding :: Maybe (VecN Number)
  , seed :: NoiseSeed              -- Deterministic across frames
  , denoiseSteps :: Int            -- 1-50 typically
  , guidanceScale :: Number        -- CFG scale (1.0-20.0)
  
    -- Reactive parameters (change on interaction)
  , reactive :: Maybe ReactiveDiffusion
  
    -- Caching
  , cachePolicy :: CachePolicy     -- How to handle frame-to-frame coherence
  }

type ReactiveDiffusion =
  { onHover :: Maybe PromptDelta   -- Blend toward this on hover
  , onPress :: Maybe PromptDelta   -- Blend toward this on press
  , onFocus :: Maybe PromptDelta   -- Blend toward this on focus
  , blendDuration :: Duration      -- How fast to interpolate
  , blendCurve :: EasingFunction   -- How to interpolate
  }
```

## The Math: Why This Scales

### Traditional Rendering
```
Pixels per frame: 1920 × 1080 × 4 = 8.3M
Frames per second: 60
Bytes per pixel: 4 (RGBA8)
Bandwidth: 8.3M × 60 × 4 = 2 GB/sec per viewport

At 1B agents with unique viewports:
2 GB/sec × 1B = 2 Exabytes/sec (impossible)
```

### Latent Space Rendering
```
Latents per frame: 240 × 135 × 4 = 130K
Frames per second: 60
Bytes per latent: 2 (float16)
Bandwidth: 130K × 60 × 2 = 16 MB/sec per viewport

At 1B agents with unique viewports:
16 MB/sec × 1B = 16 Petabytes/sec

With 8× batching (8 agents share a diffusion call):
2 Petabytes/sec

With latent caching (only compute on change):
~200 Terabytes/sec peak, much lower average
```

Still massive, but within reach of distributed GPU clusters.

### The Real Trick: Latent Interpolation

Most frames don't need full recomputation:

```purescript
-- Frame N: Full diffusion run
latentN :: Tensor [1, 4, 135, 240]

-- Frame N+1: If nothing changed, reuse
-- Frame N+1: If hover started, interpolate toward hover prompt
-- Frame N+1: If animation in progress, interpolate in latent space

-- Latent interpolation is CHEAP: just lerp
lerpLatent :: Number -> Tensor -> Tensor -> Tensor
lerpLatent t a b = add (scale (1.0 - t) a) (scale t b)
```

This means:
- **Idle state**: 0 diffusion calls (cache hit)
- **Hover transition**: 1 diffusion call + N interpolations
- **Animation**: Interpolate between cached keyframes

## The Data Kernel Model

At the lowest level, everything is a **data kernel dispatch**:

```purescript
data DataKernel = DataKernel
  { -- Identity
    id :: KernelId                -- UUID5 for deterministic caching
    
    -- Tensor specs
  , inputSpecs :: Array TensorSpec
  , outputSpec :: TensorSpec
  
    -- Dispatch parameters
  , workgroupSize :: { x :: Int, y :: Int, z :: Int }
  , workgroupCount :: { x :: Int, y :: Int, z :: Int }
  
    -- Shader reference
  , shader :: ShaderRef           -- WGSL compute shader
  
    -- Bind group layout
  , bindings :: Array BindingSpec
  }

-- Example: A 64×64 noise kernel
noiseKernel :: DataKernel
noiseKernel = DataKernel
  { id: uuid5 "hydrogen.kernel" "fbm-noise-64x64"
  , inputSpecs: [ tensorSpec [1, 2] float32 ]  -- [seed, time]
  , outputSpec: tensorSpec [1, 4, 64, 64] float32
  , workgroupSize: { x: 8, y: 8, z: 1 }
  , workgroupCount: { x: 8, y: 8, z: 1 }
  , shader: shaderRef "fbm_noise.wgsl"
  , bindings:
      [ { binding: 0, type: Uniform, name: "params" }
      , { binding: 1, type: StorageReadWrite, name: "output" }
      ]
  }
```

## Integration with Hydrogen

### Element → Tensor Flow

```
Element tree
    ↓
flatten (pure)
    ↓
Array DrawCommand (with FillDiffusion entries)
    ↓
kernel extraction (pure)
    ↓
Array DataKernel + dependency graph
    ↓
dispatch to GPU (Effect boundary)
    ↓
Tensor outputs
    ↓
compose to framebuffer
    ↓
present
```

### Frame Coherence

For 60fps with reactive fills:

1. **Frame 0**: Full diffusion run, cache result
2. **Frames 1-59**: Check if inputs changed
   - No change → present cached frame
   - Hover state change → interpolate toward hover latent
   - Animation progress → interpolate keyframes
3. **On significant change**: Queue new diffusion run, interpolate until ready

This gives **perceptually smooth** animation without requiring 60 diffusion
runs per second.

## Why This Matters

### For Agents

An agent doesn't think about pixels. It thinks about:

```purescript
-- "Make a button that feels calm but energizes on hover"
buttonFill = FillDiffusion
  { promptEmbedding: encode "serene blue gradient, soft light, peaceful"
  , reactive: Just
      { onHover: Just (encode "+energetic +vibrant +glowing")
      , blendDuration: ms 200
      }
  }
```

The tensor computation is an implementation detail.

### For Billion-Scale

With latent space rendering:
- Agents can have unique, personalized UI
- Brand identity is a prompt embedding, not a color palette
- UI adapts to context via prompt interpolation
- Compute scales with interaction, not resolution

### For Physical Displays

A 20ft LED wall and a smartwatch use the same tensor shapes:

```purescript
-- Same latent computation
buttonLatent :: Tensor [1, 4, 8, 12]

-- Upscaled to device resolution at the edge
ledWall :: ViewportTensor
ledWall = ViewportTensor
  { pixelShape: shape4d (dim 1) (dim 4) (dim 2160) (dim 3840)  -- 4K
  , latentShape: shape4d (dim 1) (dim 4) (dim 8) (dim 12)
  , physicalExtent: Just (feet 20.0, feet 11.25)
  }

watch :: ViewportTensor
watch = ViewportTensor
  { pixelShape: shape4d (dim 1) (dim 4) (dim 368) (dim 448)
  , latentShape: shape4d (dim 1) (dim 4) (dim 8) (dim 12)
  , physicalExtent: Just (mm 40.0, mm 34.0)
  }
```

**Same tensor. Different upscaler. Perfect quality at any size.**

## Existing Infrastructure

### What Already Exists in Hydrogen

Based on codebase analysis, substantial tensor/GPU infrastructure is already in place:

| Module | Description | Status |
|--------|-------------|--------|
| `Schema.Tensor.Shape` | Full tensor shape algebra with NCHW, NHWC, broadcasting | Complete |
| `Schema.Tensor.Dimension` | Dim types including latent channels (4 for SD) | Complete |
| `Schema.Dimension.Device` | Pixel, DevicePixel, CSSPixel, PPI, DevicePixelRatio | Complete |
| `Schema.Dimension.Vector.VecN` | N-dimensional vectors for latent embeddings | Complete |
| `Schema.Material.FBM` | Fractal Brownian Motion noise with full params | Complete |
| `Schema.Material.Fill` | Fill with FillNoise variant | Complete |
| `GPU.DrawCommand` | Flat GPU primitive vocabulary | Complete |
| `GPU.WebGPU.Types` | WebGPU pipeline, buffer, texture types | Complete |
| `GPU.WebGPU.Shader` | WGSL shaders (PBR, SDF text, shadows) | Complete |
| `Schema.Spatial.Viewport` | ViewportTensor with latent shapes | **NEW** |

### What Exists in Straylight Ecosystem

From `sigil-trtllm` (C++ TensorRT-LLM):

```cpp
// Strong dimension types - compile-time mixup prevention
struct sequence_length { std::size_t value; };
struct batch_size { std::size_t value; };
struct hidden_dimension { std::size_t value; };
struct head_count { std::size_t value; };

// mdspan-based tensor views
template<typename T>
using tensor_4d_view = std::mdspan<T, std::dextents<std::size_t, 4>>;

// NVFP4 block-scaled quantization (4.5 bits/element)
struct fp4_block_config {
    static constexpr std::size_t elements_per_block = 16;
    static constexpr std::size_t block_scale_bits = 8;  // FP8 E4M3
};
```

From `sigil-trtllm` Blackwell (SM120) internals:

```
// 5th Gen Tensor Core operations
nvvm.tcgen05.mma.block_scale    -- Block-scaled MMA for FP4/FP8
nvvm.tcgen05.cp                 -- Copy to Tensor Memory (TMEM)
cute_nvgpu.arch.mma.SM120.block_scaled

// TMEM: New memory hierarchy level in Blackwell
// Directly accessible by tensor cores
// 8-byte minimum alignment
// Eliminates SMEM bottleneck
```

From `opencode` console (production WGSL):

```wgsl
fn fastNoise(st: vec2<f32>) -> f32 {
    return fract(sin(dot(st, vec2<f32>(12.9898, 78.233))) * 43758.5453);
}

// Spotlight effect with particles, distortion, noise
@group(0) @binding(0) var<uniform> uniforms: Uniforms;
```

## Implementation Phases

### Phase 1: ViewportTensor ✓ COMPLETE
- [x] Define ViewportTensor type with pixel/latent shapes
- [x] Connect to existing Device units (PPI, DevicePixelRatio)
- [x] Add latent shape inference from pixel shape (8× downsample)
- [x] Physical extent support (meters, inches, feet)
- [x] Color space and memory layout options

### Phase 2: ComputeKernel
- [ ] Define kernel abstraction with tensor specs
- [ ] Port FBM noise to kernel form
- [ ] Add dispatch dimension calculation (workgroup size/count)
- [ ] Wire to WebGPU compute pipeline
- [ ] Add kernel caching by UUID5

### Phase 3: FillDiffusion
- [ ] Add FillDiffusion variant to Fill type
- [ ] Define ReactiveDiffusion for hover/press/focus
- [ ] Implement latent caching with LRU eviction
- [ ] Add slerp/lerp interpolation for frame coherence
- [ ] Connect to VecN for prompt embeddings

### Phase 4: Integration
- [ ] Update DrawCommand with tensor fill support
- [ ] Add kernel extraction pass to GPU.Flatten
- [ ] Implement dependency graph for dispatch ordering
- [ ] Wire compute output to fragment shader input
- [ ] Add upscaler kernel for latent → pixel

## Open Questions

1. **Model distribution**: Where do diffusion model weights live?
   - Edge: Fast but memory-constrained
   - Cloud: Scalable but latency-sensitive
   - Hybrid: Cache hot weights locally, stream cold

2. **Latent caching**: How much VRAM budget for cached latents?
   - 1080p latent = 130K × 2 bytes = 260KB per frame
   - Cache 100 frames = 26MB (trivial)
   - Cache 10K frames = 2.6GB (reasonable on RTX)

3. **Synchronization**: How do agents coordinate when sharing a viewport?
   - Each agent owns a region (tensor slice)
   - Composition happens in shared framebuffer
   - Conflict resolution via priority/timestamp

4. **Degradation**: What happens when GPU budget is exhausted?
   - Fall back to FBM noise (always available)
   - Reduce latent resolution (adaptive quality)
   - Increase frame interpolation (temporal smoothing)

5. **Determinism**: How to ensure same seed + prompt = same output?
   - Fixed precision (fp16 throughout)
   - Deterministic scheduler (DDIM, not stochastic)
   - UUID5 hashing for cache keys

## Hardware Target

Primary: **NVIDIA Blackwell (SM120/RTX PRO 6000)**

Key features for tensor rendering:
- TCGEN05: 5th gen tensor cores with block-scaled MMA
- TMEM: Tensor memory hierarchy (eliminates SMEM bottleneck)
- NVFP4: 4.5 bits/element with FP8 scales
- 2CTA cooperation: Two CTAs cooperate on single tile

This architecture enables:
- Sub-byte quantization for inference (2× memory savings)
- Direct tensor core access without SMEM copies
- Efficient block-scaled operations for latent space

---

*This is the render model Chromium should have built.*

*Tensors, not pixels.*
*Computation, not layout.*
*Meaning, not color values.*

---

*Last updated: February 25, 2026*
