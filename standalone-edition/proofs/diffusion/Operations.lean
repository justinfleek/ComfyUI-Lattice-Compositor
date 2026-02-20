/-
Diffusion Operations with Shape Verification
=============================================

GPU kernel operations with compile-time shape verification.
Each operation carries a proof that shapes are compatible.
-/

import Diffusion.Tensor

namespace Diffusion.Operations

open Diffusion.Tensor

/-!
## Verified Operations

Each operation takes shape proofs as arguments, ensuring
type-level safety before any GPU kernels are invoked.
-/

/-- A shape-verified tensor reference -/
structure VerifiedTensor where
  meta : TensorMeta
  valid : meta.valid = true
  deriving Repr

/-!
## Linear Algebra Operations
-/

/-- Matrix multiplication with shape proof -/
structure MatMul where
  a : VerifiedTensor
  b : VerifiedTensor
  compatible : Shape.matmulCompatible a.meta.shape b.meta.shape
  deriving Repr

/-- Batch matrix multiplication for attention -/
structure BatchMatMul where
  a : VerifiedTensor
  b : VerifiedTensor
  -- Last two dims must be matmul-compatible
  compatible : Shape.matmulCompatible a.meta.shape b.meta.shape
  -- Batch dims must broadcast
  batchCompat : a.meta.shape.length ≥ 3 → b.meta.shape.length ≥ 3 →
    Shape.broadcastCompatible
      (a.meta.shape.take (a.meta.shape.length - 2))
      (b.meta.shape.take (b.meta.shape.length - 2)) = true

/-!
## Normalization Operations
-/

/-- Layer normalization configuration -/
structure LayerNorm where
  input : VerifiedTensor
  weight : VerifiedTensor
  bias : VerifiedTensor
  -- Weight and bias must match last dim of input
  weightMatch : input.meta.shape.length > 0 →
    match input.meta.shape.reverse with
    | d :: _ => weight.meta.shape = [d]
    | _ => False
  biasMatch : input.meta.shape.length > 0 →
    match input.meta.shape.reverse with
    | d :: _ => bias.meta.shape = [d]
    | _ => False

/-- Group normalization (used in UNet) -/
structure GroupNorm where
  input : VerifiedTensor
  numGroups : Dim
  weight : VerifiedTensor
  bias : VerifiedTensor
  -- Input must be at least 3D: [batch, channels, ...]
  inputRank : input.meta.shape.length ≥ 3
  -- Channels must be divisible by numGroups
  channelsDivisible : input.meta.shape.length ≥ 2 →
    match input.meta.shape with
    | _ :: c :: _ => numGroups.size ∣ c.size
    | _ => False

/-!
## Convolution Operations
-/

/-- 2D Convolution with shape verification -/
structure Conv2d where
  input : VerifiedTensor
  weight : VerifiedTensor
  bias : Option VerifiedTensor
  config : Conv2dConfig
  -- Input shape: [batch, in_channels, H, W]
  inputValid : input.meta.shape.length = 4
  -- Weight shape: [out_channels, in_channels, kH, kW]
  weightValid : weight.meta.shape.length = 4
  -- Input channels must match
  channelsMatch : match input.meta.shape, weight.meta.shape with
    | [_, ic, _, _], [_, wic, _, _] => ic.size = wic.size
    | _, _ => False
  -- Bias must match out_channels if present
  biasValid : bias.map (fun b => b.meta.shape = [config.outChannels]) = some true ∨
              bias.isNone

/-!
## Attention Operations
-/

/-- Self-attention operation -/
structure SelfAttention where
  q : VerifiedTensor  -- Query
  k : VerifiedTensor  -- Key
  v : VerifiedTensor  -- Value
  config : AttentionConfig
  -- Q, K, V must have compatible shapes
  qkvValid : config.checkQKV q.meta.shape k.meta.shape v.meta.shape = true

/-- Cross-attention (text conditioning) -/
structure CrossAttention where
  q : VerifiedTensor      -- From image features
  k : VerifiedTensor      -- From text encoder
  v : VerifiedTensor      -- From text encoder
  -- Q head_dim must match K, V head_dim
  headDimMatch : match q.meta.shape.reverse, k.meta.shape.reverse with
    | qd :: _, kd :: _ => qd.size = kd.size
    | _, _ => False

/-!
## Diffusion-Specific Operations
-/

/-- Timestep embedding -/
structure TimestepEmbed where
  timesteps : VerifiedTensor  -- [batch] integer timesteps
  embDim : Dim                -- Embedding dimension
  -- Timesteps must be 1D
  timestepsRank : timesteps.meta.shape.length = 1

/-- Classifier-free guidance combination -/
structure CFGCombine where
  conditioned : VerifiedTensor    -- Conditional output
  unconditioned : VerifiedTensor  -- Unconditional output
  guidanceScale : Float           -- CFG scale (typically 7.0-8.0)
  -- Shapes must match exactly
  shapesMatch : conditioned.meta.shape = unconditioned.meta.shape

/-- VAE encode: image → latent -/
structure VAEEncode where
  input : VerifiedTensor
  -- Input: [batch, 3, H, W] RGB image
  inputValid : input.meta.shape.length = 4 ∧
    match input.meta.shape with
    | [_, c, _, _] => c.size = 3
    | _ => False

/-- VAE decode: latent → image -/
structure VAEDecode where
  latent : VerifiedTensor
  -- Latent: [batch, 4, H/8, W/8] for SD, [batch, 16, H/8, W/8] for Flux
  latentValid : latent.meta.shape.length = 4 ∧
    match latent.meta.shape with
    | [_, c, _, _] => c.size = 4 ∨ c.size = 16
    | _ => False

/-!
## Scheduler Operations

These handle the noise schedule for diffusion sampling.
-/

/-- Single denoising step -/
structure DenoisingStep where
  sample : VerifiedTensor       -- Current noisy sample
  modelOutput : VerifiedTensor  -- UNet/DiT output
  timestep : Nat                -- Current timestep
  -- Shapes must match
  shapesMatch : sample.meta.shape = modelOutput.meta.shape

/-!
## Operation Composition

Build verified pipelines by composing operations.
-/

/-- A verified computation graph -/
inductive VerifiedOp where
  | matmul : MatMul → VerifiedOp
  | batchMatmul : BatchMatMul → VerifiedOp
  | layerNorm : LayerNorm → VerifiedOp
  | groupNorm : GroupNorm → VerifiedOp
  | conv2d : Conv2d → VerifiedOp
  | selfAttention : SelfAttention → VerifiedOp
  | crossAttention : CrossAttention → VerifiedOp
  | timestepEmbed : TimestepEmbed → VerifiedOp
  | cfgCombine : CFGCombine → VerifiedOp
  | vaeEncode : VAEEncode → VerifiedOp
  | vaeDecode : VAEDecode → VerifiedOp
  | denoise : DenoisingStep → VerifiedOp
  | sequence : List VerifiedOp → VerifiedOp

/-- All operations in a verified graph are valid -/
def VerifiedOp.allValid : VerifiedOp → Bool
  | .matmul _ => true
  | .batchMatmul _ => true
  | .layerNorm _ => true
  | .groupNorm _ => true
  | .conv2d _ => true
  | .selfAttention _ => true
  | .crossAttention _ => true
  | .timestepEmbed _ => true
  | .cfgCombine _ => true
  | .vaeEncode _ => true
  | .vaeDecode _ => true
  | .denoise _ => true
  | .sequence ops => ops.all VerifiedOp.allValid

/-!
## Model Loading

Verify shapes when loading from safetensors.
-/

/-- Load and verify a tensor from safetensors metadata -/
def loadVerifiedTensor (meta : TensorMeta) : Option VerifiedTensor :=
  if h : meta.valid = true then
    some ⟨meta, h⟩
  else
    none

/-- Verify an entire model's weights -/
structure ModelWeights where
  tensors : List VerifiedTensor
  -- All tensors are valid
  allValid : tensors.all (fun t => t.valid = true) = true

end Diffusion.Operations
