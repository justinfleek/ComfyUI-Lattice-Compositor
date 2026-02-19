# ComfyUI Feature Parity Analysis for LATTICE

**Document Version:** 1.0  
**Date:** February 2026  
**Status:** Complete Technical Specification

---

## Executive Summary

This document provides a comprehensive breakdown of what it would take to integrate ComfyUI functionality into the existing LATTICE PureScript/Haskell/Lean4 codebase as a standalone product with full feature parity. The analysis covers all major subsystems: execution model, memory management, model loading, LoRA integration, samplers, ControlNet, VAE, and the node-based graph system.

### Effort Estimation Summary

| Component | Complexity | Estimated Effort | Dependencies |
|-----------|------------|------------------|--------------|
| Execution Graph Engine | High | 4-6 weeks | None |
| Memory Management | High | 3-4 weeks | FFI to CUDA/Metal |
| Model Loading (Checkpoints) | Medium | 2-3 weeks | safetensors binding |
| LoRA/Adapter System | High | 3-4 weeks | Model Patcher |
| Sampler Implementations | Medium | 3-4 weeks | k-diffusion port |
| ControlNet/IP-Adapter | Medium | 2-3 weeks | CLIP Vision |
| VAE Pipeline | Low | 1-2 weeks | Tensor FFI |
| CLIP Text Encoding | Medium | 2-3 weeks | Tokenizer |
| Node System + UI | High | 4-6 weeks | Execution Engine |
| **Total** | - | **24-35 weeks** | - |

---

## Table of Contents

1. [Core Execution Model](#1-core-execution-model)
2. [Memory Management System](#2-memory-management-system)
3. [Model Management](#3-model-management)
4. [LoRA/Adapter System](#4-loraadapter-system)
5. [Sampler Implementations](#5-sampler-implementations)
6. [ControlNet/IP-Adapter/T2I-Adapter](#6-controlnetip-adaptert2i-adapter)
7. [VAE and Latent Operations](#7-vae-and-latent-operations)
8. [CLIP Text Encoding](#8-clip-text-encoding)
9. [Node-Based Graph System](#9-node-based-graph-system)
10. [Integration with Existing LATTICE Projects](#10-integration-with-existing-lattice-projects)
11. [Implementation Roadmap](#11-implementation-roadmap)

---

## 1. Core Execution Model

### 1.1 Architecture Overview

ComfyUI uses a **dynamic prompt** abstraction with lazy evaluation and hierarchical caching:

```haskell
-- | Core execution types
data DynamicPrompt = DynamicPrompt
  { dpOriginalPrompt  :: Prompt           -- User's workflow
  , dpEphemeralPrompt :: Map NodeId Node  -- Runtime-generated nodes
  , dpEphemeralParents :: Map NodeId NodeId
  , dpEphemeralDisplay :: Map NodeId NodeId
  }

data Node = Node
  { nodeClassType :: Text
  , nodeInputs    :: Map Text InputValue
  }

data InputValue
  = Constant Value
  | Link SocketRef   -- (source_node_id, output_index)
```

### 1.2 Topological Execution

The execution engine implements **topological dissolve**:

1. Output nodes are added to execution list
2. Dependencies are recursively traced (respecting lazy inputs)
3. Nodes with zero blocking dependencies are "ready"
4. After execution, blocked nodes have their count decremented
5. Cycle detection via reverse topological dissolve

```haskell
data ExecutionState = ExecutionState
  { esPendingNodes :: Set NodeId
  , esBlockCount   :: Map NodeId Int
  , esBlocking     :: Map NodeId (Map NodeId (Set Int))
  , esCache        :: HierarchicalCache
  , esCurrentHooks :: Maybe HookGroup
  }
```

### 1.3 Caching Strategies

| Strategy | Description | Use Case |
|----------|-------------|----------|
| `CacheKeySetID` | Simple identity caching | Development/debugging |
| `CacheKeySetInputSignature` | Content-addressable | Production (default) |
| `HierarchicalCache` | Nested caches for subgraphs | Subgraph expansion |
| `LRUCache` | Size-limited with generation tracking | Intermediate outputs |
| `RAMPressureCache` | Evicts based on RAM availability | Production |

### 1.4 Required Implementation

```haskell
module Lattice.Diffusion.Execution where

-- | Main execution loop
executePrompt 
  :: DynamicPrompt 
  -> ExecutionConfig 
  -> IO (Either ExecutionError ExecutionResult)

-- | Topological sort with lazy input handling
buildExecutionOrder 
  :: DynamicPrompt 
  -> Set NodeId 
  -> IO (Either CycleError [NodeId])

-- | Cache key computation
computeCacheKey 
  :: CacheStrategy 
  -> DynamicPrompt 
  -> NodeId 
  -> IO CacheKey

-- | Node execution with batching
executeNode 
  :: Node 
  -> Map Text Value 
  -> IO (Either NodeError NodeOutput)
```

---

## 2. Memory Management System

### 2.1 VRAM State Machine

```haskell
data VRAMState
  = Disabled      -- No GPU
  | NoVRAM        -- Very low VRAM (<2GB) - aggressive offloading
  | LowVRAM       -- Partial model loading (2-6GB)
  | NormalVRAM    -- Standard operation (6-12GB)
  | HighVRAM      -- Keep everything loaded (>12GB)
  | Shared        -- Unified memory (Apple Silicon)
  deriving stock (Eq, Show, Bounded, Enum)
```

### 2.2 Model Loading with Memory Budgets

```haskell
data LoadedModel = LoadedModel
  { lmModelRef      :: Weak Model
  , lmDevice        :: Device
  , lmLoadedSize    :: Int64    -- Bytes currently on GPU
  , lmTotalSize     :: Int64    -- Total model size
  , lmCurrentlyUsed :: Bool
  , lmAge           :: Int      -- For LRU eviction
  }

-- | Free memory to accommodate new model
freeMemory 
  :: Int64              -- Memory required
  -> Device             -- Target device
  -> [LoadedModel]      -- Models to keep loaded
  -> IO Int64           -- Memory actually freed

-- | Load model with partial offloading
loadModelGPU 
  :: ModelPatcher 
  -> Int64              -- Memory budget
  -> Bool               -- Force patch weights
  -> IO LoadedModel
```

### 2.3 Async Weight Offloading

ComfyUI uses multiple CUDA streams for async weight transfer:

```haskell
-- | Number of async streams (2 for Nvidia/AMD)
numOffloadStreams :: Int
numOffloadStreams = 2

-- | Get next offload stream (round-robin)
getOffloadStream :: Device -> IO Stream

-- | Async weight transfer
asyncLoadWeight 
  :: Tensor 
  -> Device 
  -> Stream 
  -> IO (Future Tensor)
```

### 2.4 Required FFI Bindings

- CUDA memory info (`cudaMemGetInfo`)
- CUDA stream management
- Metal unified memory APIs (for Apple Silicon)
- Memory-mapped file handling for models

---

## 3. Model Management

### 3.1 Checkpoint Loading

ComfyUI supports multiple checkpoint formats:

| Format | Extension | Library |
|--------|-----------|---------|
| SafeTensors | `.safetensors` | safetensors-rs |
| Pickle | `.ckpt`, `.pt` | torch (restricted) |
| Diffusers | folder structure | custom loader |

```haskell
-- | Load checkpoint with auto-detection
loadCheckpoint 
  :: FilePath 
  -> LoadConfig 
  -> IO (Either LoadError CheckpointData)

data CheckpointData = CheckpointData
  { cdUNet      :: StateDict
  , cdVAE       :: Maybe StateDict
  , cdCLIP      :: Maybe StateDict
  , cdModelType :: ModelType
  }

data ModelType
  = SD15
  | SD21
  | SDXL
  | SD3
  | SD35
  | Flux
  | FluxSchnell
  | Mochi
  | LTXVideo
  | HunyuanVideo
  | Wan21
  deriving stock (Eq, Show)
```

### 3.2 Model Detection

Model type is detected from state dict key patterns:

```haskell
-- | Detect model type from state dict
detectModelType :: StateDict -> Either DetectionError ModelType
detectModelType sd
  | hasKey "model.diffusion_model.joint_blocks.0.x_block.attn.proj.weight" = Right SD3
  | hasKey "double_blocks.0.img_attn.proj.weight" = Right Flux
  | hasKey "model.diffusion_model.label_emb.0.0.weight" = 
      if hasKey "model.diffusion_model.input_blocks.4.1.transformer_blocks.0.attn2.to_k.weight"
      then Right SDXL
      else Right SD21
  | hasKey "model.diffusion_model.input_blocks.1.1.proj_in.weight" = Right SD15
  | otherwise = Left UnknownModelType
```

### 3.3 State Dict Manipulation

```haskell
-- | Separate combined checkpoint into components
separateCheckpoint 
  :: StateDict 
  -> ModelType 
  -> (StateDict, Maybe StateDict, Maybe StateDict)
  -- (unet, vae, clip)

-- | Convert diffusers format to ComfyUI format
convertDiffusers 
  :: FilePath 
  -> IO (Either ConversionError StateDict)
```

---

## 4. LoRA/Adapter System

### 4.1 Supported Adapter Types

| Type | Formula | Parameters |
|------|---------|------------|
| LoRA | `W' = W + α/r × (up @ down)` | up, down, alpha |
| LoHa | `W' = W + α/r × ((w1a@w1b) ⊙ (w2a@w2b))` | w1a, w1b, w2a, w2b, alpha |
| LoKr | `W' = W + α/r × kron(w1, w2)` | w1, w2 (or decomposed) |
| OFT | `W' = R @ W` (orthogonal transform) | blocks |
| BOFT | `W' = butterfly_ortho(W)` | 4D blocks |
| GLoRA | `W' = W + α × (W @ a1 @ a2 + b1 @ b2)` | a1, a2, b1, b2 |
| Diff | `W' = W + diff` | diff |

### 4.2 Core Types

```haskell
data WeightAdapter
  = AdapterLoRA LoRAWeights
  | AdapterLoHa LoHaWeights
  | AdapterLoKr LoKrWeights
  | AdapterOFT OFTWeights
  | AdapterBOFT BOFTWeights
  | AdapterGLoRA GLoRAWeights
  | AdapterDiff Tensor (Maybe Tensor)
  | AdapterSet Tensor

data LoRAWeights = LoRAWeights
  { loraUp       :: Tensor
  , loraDown     :: Tensor
  , loraAlpha    :: Maybe Float
  , loraMid      :: Maybe Tensor    -- Tucker decomposition
  , doraScale    :: Maybe Tensor    -- DoRA support
  , reshapeTarget :: Maybe [Int]
  }
```

### 4.3 Model Patcher

```haskell
data ModelPatcher = ModelPatcher
  { mpModel          :: Model
  , mpPatches        :: Map Text [Patch]
  , mpBackup         :: Map Text BackupEntry
  , mpObjectPatches  :: Map Text Value
  , mpPatchesUUID    :: UUID
  , mpParent         :: Maybe ModelPatcher
  , mpLoadDevice     :: Device
  , mpOffloadDevice  :: Device
  }

-- | Apply patches to model weights
patchModel :: ModelPatcher -> IO ()

-- | Restore original weights
unpatchModel :: ModelPatcher -> IO ()

-- | Clone patcher for LoRA stacking
clonePatcher :: ModelPatcher -> IO ModelPatcher
```

### 4.4 Weight Calculation

```haskell
-- | Calculate patched weight
calculateWeight 
  :: [Patch] 
  -> Tensor       -- Original weight
  -> Text         -- Key for stochastic rounding seed
  -> DType        -- Intermediate dtype
  -> IO Tensor

-- | Apply LoRA with DoRA support
applyLoRA 
  :: LoRAWeights 
  -> Tensor 
  -> Float        -- Strength
  -> IO Tensor
```

---

## 5. Sampler Implementations

### 5.1 Sampler Categories

**Euler Family:**
- Euler (first-order)
- Euler Ancestral (with noise injection)
- Heun (second-order predictor-corrector)

**DPM Family:**
- DPM++ 2M (multistep)
- DPM++ 2M SDE (stochastic)
- DPM++ 2S Ancestral
- DPM++ 3M SDE

**Other:**
- UniPC (unified predictor-corrector)
- LCM (latent consistency)
- DDIM (deterministic)
- LMS (linear multistep)

### 5.2 Scheduler Types

```haskell
data Scheduler
  = Karras         -- σ_i = σ_min^(1/ρ) * (σ_max^(1/ρ) - σ_min^(1/ρ)) * ...
  | Exponential    -- σ_i = σ_max * (σ_min/σ_max)^(i/(n-1))
  | SGMUniform     -- Linear in timestep space
  | Beta           -- Beta distribution
  | LinearQuadratic
  | AYS            -- Align Your Steps (model-specific)
  | KLOptimal      -- KL-optimal sigmas

-- | Generate sigma schedule
generateSigmas 
  :: Scheduler 
  -> Int          -- Steps
  -> Float        -- Sigma max
  -> Float        -- Sigma min
  -> Vector Float
```

### 5.3 CFG Implementation

```haskell
-- | Classifier-free guidance
data CFGConfig = CFGConfig
  { cfgScale     :: Float       -- Guidance strength
  , cfgRescale   :: Float       -- Rescale factor (0-1)
  , cfgPerpNeg   :: Bool        -- CFG++ perpendicular negative
  }

-- | Apply CFG to model output
applyCFG 
  :: CFGConfig 
  -> Tensor       -- Conditional output
  -> Tensor       -- Unconditional output
  -> Tensor

-- | CFG with rescale
applyCFGRescale 
  :: Float        -- Scale
  -> Float        -- Rescale
  -> Tensor       -- Cond
  -> Tensor       -- Uncond
  -> Tensor
applyCFGRescale scale rescale cond uncond =
  let xCfg = uncond + scale * (cond - uncond)
      stdCond = std cond
      stdCfg = std xCfg
      rescaleFactor = stdCond / stdCfg
      xRescaled = xCfg * rescaleFactor
  in xCfg * (1 - rescale) + xRescaled * rescale
```

### 5.4 Core Sampling Loop

```haskell
-- | Generic sampling step
data SamplerStep = SamplerStep
  { ssDenoised  :: Tensor
  , ssSigma     :: Float
  , ssSigmaNext :: Float
  , ssNoise     :: Maybe Tensor
  }

-- | Euler step
eulerStep :: SamplerStep -> Tensor -> Tensor
eulerStep SamplerStep{..} x =
  let dt = ssSigmaNext - ssSigma
      d = (x - ssDenoised) / ssSigma
  in x + d * dt

-- | DPM++ 2M step
dpmpp2mStep 
  :: SamplerStep 
  -> Tensor 
  -> Maybe Tensor   -- Previous denoised
  -> Tensor
```

---

## 6. ControlNet/IP-Adapter/T2I-Adapter

### 6.1 ControlNet Architecture

```haskell
data ControlNet = ControlNet
  { cnModel            :: ControlModel
  , cnStrength         :: Float
  , cnTimestepRange    :: (Float, Float)  -- (start%, end%)
  , cnPreviousControl  :: Maybe ControlNet  -- Multi-ControlNet chaining
  , cnCompressionRatio :: Int             -- 8 for SD1.5/SDXL, 1 for SD3/Flux
  }

data ControlOutput = ControlOutput
  { coInput  :: [Maybe Tensor]  -- Input block additions
  , coMiddle :: [Maybe Tensor]  -- Middle block addition
  , coOutput :: [Maybe Tensor]  -- Output block additions
  }

-- | Get control signals (recursive for chained ControlNets)
getControlSignals 
  :: ControlNet 
  -> Tensor       -- x_noisy
  -> Tensor       -- timestep
  -> Conditioning
  -> IO (Maybe ControlOutput)
```

### 6.2 IP-Adapter

```haskell
data IPAdapter = IPAdapter
  { ipaClipVision   :: CLIPVisionModel
  , ipaImageProj    :: ImageProjModel
  , ipaToKV         :: Map Text Linear  -- Per-layer K/V projections
  , ipaWeightType   :: IPAdapterWeightType
  , ipaStrength     :: Float
  }

data IPAdapterWeightType
  = IPALinear
  | IPAEaseIn
  | IPAEaseOut
  | IPAStyleTransfer      -- Only deep blocks
  | IPAComposition        -- Only shallow blocks

-- | Encode image for IP-Adapter
encodeIPAdapterImage 
  :: IPAdapter 
  -> Tensor       -- Image [B, H, W, C]
  -> IO (Tensor, Tensor)  -- (cond_embed, uncond_embed)

-- | Modified cross-attention with IP-Adapter
ipAdapterAttention 
  :: IPAdapter 
  -> Tensor       -- Q
  -> Tensor       -- K (text)
  -> Tensor       -- V (text)
  -> Tensor       -- IP hidden states
  -> Tensor
```

### 6.3 T2I-Adapter

Lightweight alternative to ControlNet (input blocks only, ~80M params vs ~1.2B):

```haskell
data T2IAdapter = T2IAdapter
  { t2iModel    :: T2IModel
  , t2iStrength :: Float
  , t2iConfig   :: ControlConfig
  }

-- | T2I-Adapter forward (input blocks only)
t2iAdapterForward 
  :: T2IAdapter 
  -> Tensor       -- Control hint
  -> IO [Tensor]  -- Feature maps for input blocks
```

---

## 7. VAE and Latent Operations

### 7.1 VAE Configuration

```haskell
data LatentFormat = LatentFormat
  { lfScaleFactor     :: Float
  , lfShiftFactor     :: Maybe Float    -- SD3/Flux
  , lfLatentChannels  :: Int            -- 4 (SD1.5), 16 (SD3/Flux)
  , lfSpatialDownscale :: Int           -- 8 (SD1.5), 16 (SD3)
  , lfLatentRGBFactors :: Maybe [[Float]] -- For preview
  }

-- | Standard formats
sd15Format, sdxlFormat, sd3Format, fluxFormat :: LatentFormat
```

### 7.2 Encode/Decode

```haskell
-- | Encode pixels to latents
vaeEncode :: VAE -> Tensor -> IO Tensor

-- | Decode latents to pixels
vaeDecode :: VAE -> Tensor -> IO Tensor

-- | Tiled decode for high resolution
tiledDecode 
  :: VAE 
  -> (Int, Int)   -- Tile size
  -> Int          -- Overlap
  -> Tensor 
  -> IO Tensor
```

### 7.3 Latent Operations

```haskell
-- | Upscale latents
latentUpscale 
  :: UpscaleMethod  -- Nearest, Bilinear, Bicubic, Bislerp
  -> (Int, Int)     -- Target size
  -> Tensor 
  -> Tensor

-- | Composite latents with mask
latentComposite 
  :: Tensor       -- Base
  -> Tensor       -- Overlay
  -> Tensor       -- Mask
  -> (Int, Int)   -- Offset
  -> Tensor

-- | Add noise for img2img
injectNoise 
  :: Tensor       -- Clean latents
  -> Tensor       -- Noise
  -> Float        -- Denoise strength
  -> ModelSampling
  -> Tensor
```

---

## 8. CLIP Text Encoding

### 8.1 Tokenizer

```haskell
data CLIPTokenizer = CLIPTokenizer
  { ctVocab        :: Map Text Int
  , ctMerges       :: Vector (Text, Text)
  , ctMaxLength    :: Int
  , ctPadToken     :: Int
  , ctStartToken   :: Int
  , ctEndToken     :: Int
  }

-- | Tokenize text
tokenize :: CLIPTokenizer -> Text -> [Int]

-- | Tokenize with embeddings (for textual inversion)
tokenizeWithEmbeddings 
  :: CLIPTokenizer 
  -> Map Text Tensor   -- Embedding dict
  -> Text 
  -> ([Int], [Maybe Tensor])
```

### 8.2 Text Encoder

```haskell
data CLIPTextEncoder = CLIPTextEncoder
  { cteModel       :: TransformerModel
  , ctePooler      :: Maybe Pooler
  , cteTokenizer   :: CLIPTokenizer
  }

-- | Encode text to conditioning
encodeText 
  :: CLIPTextEncoder 
  -> Text 
  -> IO (Tensor, Maybe Tensor)  -- (last_hidden, pooled)

-- | SDXL dual encoder
encodeTextSDXL 
  :: CLIPTextEncoder  -- OpenCLIP ViT-G
  -> CLIPTextEncoder  -- CLIP ViT-L
  -> Text 
  -> IO Conditioning
```

### 8.3 Conditioning Structure

```haskell
data Conditioning = Conditioning
  { condCrossAttn    :: Tensor          -- Cross-attention context
  , condPooled       :: Maybe Tensor    -- Pooled output (SDXL/SD3)
  , condMask         :: Maybe Tensor    -- Attention mask
  , condArea         :: Maybe CondArea  -- Regional prompts
  , condStrength     :: Float
  , condTimestepRange :: (Float, Float)
  }

data CondArea = CondArea
  { caX, caY, caWidth, caHeight :: Int
  , caStrength :: Float
  }
```

---

## 9. Node-Based Graph System

### 9.1 Node Definition

```haskell
data NodeDef = NodeDef
  { ndName          :: Text
  , ndCategory      :: Text
  , ndInputTypes    :: [(Text, TypeSpec)]
  , ndOutputTypes   :: [TypeSpec]
  , ndFunction      :: NodeFunction
  , ndIsOutputNode  :: Bool
  }

data TypeSpec
  = TSString
  | TSInt
  | TSFloat
  | TSBool
  | TSImage
  | TSLatent
  | TSConditioning
  | TSModel
  | TSClip
  | TSVae
  | TSControlNet
  | TSMask
  | TSCombo [Text]   -- Enum
  | TSAny
```

### 9.2 Node Registry

```haskell
-- | Global node registry
type NodeRegistry = Map Text NodeDef

-- | Register built-in nodes
registerBuiltinNodes :: IO NodeRegistry

-- | Load custom nodes from directory
loadCustomNodes :: FilePath -> NodeRegistry -> IO NodeRegistry
```

### 9.3 Workflow Serialization

```haskell
-- | Workflow JSON format
data Workflow = Workflow
  { wfNodes      :: Map NodeId NodeInstance
  , wfLinks      :: [Link]
  , wfGroups     :: [Group]
  , wfConfig     :: WorkflowConfig
  }

-- | Load/save workflow
loadWorkflow :: FilePath -> IO (Either ParseError Workflow)
saveWorkflow :: FilePath -> Workflow -> IO ()

-- | Convert workflow to prompt
workflowToPrompt :: Workflow -> IO Prompt
```

---

## 10. Integration with Existing LATTICE Projects

### 10.1 Verified-PureScript Integration

The Lean4 formal verification in `verified-purescript-main` can verify:
- Tensor shape compatibility in node connections
- Type-safe latent space operations
- Memory bound proofs for tiled operations

```lean
-- Example: Verify latent dimensions match
theorem latent_compatible (sd15 : LatentFormat) (sdxl : LatentFormat) :
  sd15.channels = 4 ∧ sdxl.channels = 4 →
  latent_compatible sd15 sdxl := by
  simp [latent_compatible]
```

### 10.2 Trinity-Engine Integration

The Haskell io_uring integration in `trinity-engine-hs-dev` provides:
- Async file I/O for model loading
- Zero-copy tensor transfers
- Non-blocking checkpoint streaming

### 10.3 Slide Integration

The LLM wire protocol in `slide-main` can be extended for:
- Diffusion model inference serving
- Streaming image generation
- Multi-model orchestration

### 10.4 Dhall Configuration

Following LATTICE patterns, all configuration should use Dhall:

```dhall
let Sampler = < Euler | EulerAncestral | DPMpp2M | UniPC >

let SamplerConfig = {
  sampler : Sampler,
  steps : Natural,
  cfg_scale : Double,
  scheduler : Text
}

let defaultSamplerConfig : SamplerConfig = {
  sampler = Sampler.Euler,
  steps = 20,
  cfg_scale = 7.0,
  scheduler = "normal"
}
```

---

## 11. Implementation Roadmap

### Phase 1: Foundation (Weeks 1-8)

**Week 1-2: FFI Layer**
- [ ] SafeTensors Haskell bindings
- [ ] CUDA memory management FFI
- [ ] Basic tensor operations wrapper

**Week 3-4: Model Loading**
- [ ] Checkpoint loader (safetensors + pickle)
- [ ] Model type detection
- [ ] State dict manipulation

**Week 5-6: Memory Management**
- [ ] VRAM state machine
- [ ] Model caching/eviction
- [ ] Partial loading for low VRAM

**Week 7-8: Execution Engine (Basic)**
- [ ] Node graph representation
- [ ] Topological sort
- [ ] Basic caching

### Phase 2: Diffusion Core (Weeks 9-16)

**Week 9-10: VAE**
- [ ] Encode/decode pipeline
- [ ] Tiled operations
- [ ] Latent format handling

**Week 11-12: CLIP**
- [ ] Tokenizer implementation
- [ ] Text encoder wrapper
- [ ] SDXL dual encoding

**Week 13-14: Samplers**
- [ ] Euler family
- [ ] DPM++ family
- [ ] CFG implementation

**Week 15-16: Basic Generation**
- [ ] txt2img pipeline
- [ ] img2img pipeline
- [ ] Inpainting

### Phase 3: Advanced Features (Weeks 17-24)

**Week 17-18: LoRA System**
- [ ] LoRA weight loading
- [ ] Model patcher
- [ ] LoHa/LoKr/OFT support

**Week 19-20: ControlNet**
- [ ] ControlNet model loading
- [ ] Control signal injection
- [ ] Multi-ControlNet

**Week 21-22: IP-Adapter**
- [ ] CLIP Vision encoding
- [ ] Attention modification
- [ ] Weight types

**Week 23-24: Node System**
- [ ] Node definition DSL
- [ ] Built-in node library
- [ ] Workflow serialization

### Phase 4: Production Polish (Weeks 25-35)

**Week 25-27: UI Integration**
- [ ] PureScript-Radix UI components
- [ ] Node graph editor
- [ ] Preview system

**Week 28-30: Performance**
- [ ] Async weight loading
- [ ] Pipeline parallelism
- [ ] Memory optimization

**Week 31-33: Model Support**
- [ ] SD3/SD3.5 support
- [ ] Flux support
- [ ] Video models (Mochi, LTX)

**Week 34-35: Testing & Documentation**
- [ ] Property-based tests (via haskemathesis)
- [ ] Integration tests
- [ ] User documentation

---

## Appendix A: Key Data Structures

### A.1 Complete Type Hierarchy

```haskell
-- Core tensor type (FFI wrapper)
data Tensor = Tensor
  { tensorShape  :: [Int]
  , tensorDtype  :: DType
  , tensorDevice :: Device
  , tensorPtr    :: ForeignPtr ()
  }

-- Model hierarchy
data DiffusionModel
  = UNetSD15 UNet2DConditionModel
  | UNetSDXL UNet2DConditionModel
  | DiTSD3 DiT
  | DiTFlux FluxModel
  | MochiModel MochiTransformer
  | LTXModel LTXTransformer

-- Conditioning
data FullConditioning = FullConditioning
  { fcPositive :: [Conditioning]
  , fcNegative :: [Conditioning]
  , fcControl  :: [ControlNet]
  , fcIPAdapter :: [IPAdapterEmbed]
  }
```

### A.2 Memory Layout

```
┌─────────────────────────────────────────────────┐
│                   System RAM                     │
├─────────────────────────────────────────────────┤
│  Model Cache (LRU)                              │
│  ├── UNet weights (offloaded)                   │
│  ├── CLIP weights (offloaded)                   │
│  └── VAE weights (offloaded)                    │
├─────────────────────────────────────────────────┤
│  Execution Cache                                │
│  ├── Node outputs                               │
│  └── Intermediate tensors                       │
└─────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────┐
│                     VRAM                         │
├─────────────────────────────────────────────────┤
│  Active Model (~2-10GB depending on model)      │
│  ├── Loaded UNet blocks                         │
│  ├── Active LoRA patches                        │
│  └── ControlNet (if active)                     │
├─────────────────────────────────────────────────┤
│  Working Memory (~1-4GB)                        │
│  ├── Latents                                    │
│  ├── Attention KV cache                         │
│  └── Intermediate activations                   │
└─────────────────────────────────────────────────┘
```

---

## Appendix B: Compatibility Matrix

### B.1 Model Support

| Model | txt2img | img2img | Inpaint | ControlNet | LoRA | IP-Adapter |
|-------|---------|---------|---------|------------|------|------------|
| SD 1.5 | Yes | Yes | Yes | Yes | Yes | Yes |
| SD 2.1 | Yes | Yes | Yes | Yes | Yes | Yes |
| SDXL | Yes | Yes | Yes | Yes | Yes | Yes |
| SD3 | Yes | Yes | Yes | Partial | Yes | No |
| SD3.5 | Yes | Yes | Yes | Yes | Yes | No |
| Flux.1 | Yes | Yes | Yes | Yes | Yes | Partial |
| Mochi | Video | No | No | No | Yes | No |
| LTX | Video | No | No | No | Yes | No |

### B.2 Platform Support

| Platform | CUDA | Metal | ROCm | CPU |
|----------|------|-------|------|-----|
| Linux | Full | N/A | Partial | Slow |
| macOS | N/A | Full | N/A | Slow |
| Windows | Full | N/A | No | Slow |

---

## Appendix C: References

1. ComfyUI Source: https://github.com/comfyanonymous/ComfyUI
2. K-Diffusion: https://github.com/crowsonkb/k-diffusion
3. SafeTensors: https://github.com/huggingface/safetensors
4. LoRA Paper: https://arxiv.org/abs/2106.09685
5. ControlNet Paper: https://arxiv.org/abs/2302.05543
6. IP-Adapter Paper: https://arxiv.org/abs/2308.06721

---

*Document generated by LATTICE ComfyUI Integration Analysis*
