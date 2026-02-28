-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // compute // operation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Operation — Compute operations for ML inference.
-- |
-- | ## Design Philosophy
-- |
-- | Operations are the building blocks of compute graphs. Each operation
-- | transforms input tensors to output tensors according to well-defined
-- | semantics. Operations are pure descriptions — execution happens separately.
-- |
-- | ## Operation Categories
-- |
-- | **Linear Operations**:
-- | - MatMul: Matrix multiplication
-- | - Conv: Convolution (1D, 2D, 3D)
-- | - Linear: Fully connected layer
-- |
-- | **Elementwise Operations**:
-- | - Add, Mul, Sub, Div: Arithmetic
-- | - ReLU, GELU, SiLU: Activations
-- | - Softmax, LayerNorm: Normalization
-- |
-- | **Attention Operations**:
-- | - ScaledDotProductAttention
-- | - MultiHeadAttention
-- | - FlashAttention (fused kernel)
-- |
-- | **Shape Operations**:
-- | - Reshape, Transpose, Concat, Split
-- | - Broadcast, Squeeze, Unsqueeze
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Tensor.Shape (Shape)
-- | - Hydrogen.Schema.Tensor.DType (DType)

module Hydrogen.Schema.Compute.Operation
  ( -- * Core Types
    Operation(..)
  , ActivationType(..)
  , ConvParams
  , AttentionParams
  , NormParams
  
  -- * Default Parameters
  , defaultConvParams
  , defaultAttentionParams
  , defaultNormParams
  
  -- * Linear Operations
  , matmul
  , linear
  , conv1d
  , conv2d
  , conv3d
  
  -- * Elementwise Operations
  , add
  , mul
  , sub
  , div
  , neg
  , abs
  , sqrt
  , exp
  , log
  
  -- * Activation Functions
  , relu
  , gelu
  , silu
  , sigmoid
  , tanh
  , softmax
  , leakyRelu
  
  -- * Normalization
  , layerNorm
  , batchNorm
  , groupNorm
  , rmsnorm
  
  -- * Attention
  , scaledDotProductAttention
  , multiHeadAttention
  , flashAttention
  
  -- * Shape Operations
  , reshape
  , transpose
  , concat
  , split
  , broadcast
  , squeeze
  , unsqueeze
  , permute
  
  -- * Reduction Operations
  , reduceSum
  , reduceMean
  , reduceMax
  , reduceMin
  
  -- * Operation Properties
  , isElementwise
  , isLinear
  , isReduction
  , requiresTraining
  , operationName
  
  -- * Shape Inference
  , inferOutputShape
  , checkInputShapes
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , pure
  , bind
  , (==)
  , (<>)
  , (>=)
  , (&&)
  , ($)
  , (-)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Tensor.Dimension (dim)
import Hydrogen.Schema.Tensor.Shape (Shape, dims, shapeFromArray)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // activation type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Activation function type.
data ActivationType
  = ReLU
  | GELU
  | SiLU          -- ^ Also known as Swish
  | Sigmoid
  | Tanh
  | LeakyReLU { negativeSlope :: Number }
  | Identity

derive instance eqActivationType :: Eq ActivationType

instance showActivationType :: Show ActivationType where
  show ReLU = "ReLU"
  show GELU = "GELU"
  show SiLU = "SiLU"
  show Sigmoid = "Sigmoid"
  show Tanh = "Tanh"
  show (LeakyReLU p) = "LeakyReLU(" <> show p.negativeSlope <> ")"
  show Identity = "Identity"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conv params
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convolution parameters.
type ConvParams =
  { kernelSize :: Array Int      -- ^ Kernel dimensions
  , stride :: Array Int          -- ^ Stride per dimension
  , padding :: Array Int         -- ^ Padding per dimension
  , dilation :: Array Int        -- ^ Dilation per dimension
  , groups :: Int                -- ^ Number of groups (1 = regular conv)
  }

-- | Default convolution parameters.
defaultConvParams :: Int -> ConvParams
defaultConvParams spatialDims =
  { kernelSize: Array.replicate spatialDims 3
  , stride: Array.replicate spatialDims 1
  , padding: Array.replicate spatialDims 1
  , dilation: Array.replicate spatialDims 1
  , groups: 1
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // attention params
-- ═════════════════════════════════════════════════════════════════════════════

-- | Attention operation parameters.
type AttentionParams =
  { numHeads :: Int              -- ^ Number of attention heads
  , headDim :: Int               -- ^ Dimension per head
  , dropout :: Number            -- ^ Dropout probability (0 = no dropout)
  , causal :: Boolean            -- ^ Use causal mask (for autoregressive)
  , scale :: Maybe Number        -- ^ Custom scale (default: 1/sqrt(headDim))
  }

-- | Default attention parameters.
defaultAttentionParams :: Int -> Int -> AttentionParams
defaultAttentionParams numHeads headDim =
  { numHeads
  , headDim
  , dropout: 0.0
  , causal: false
  , scale: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // norm params
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalization parameters.
type NormParams =
  { eps :: Number                -- ^ Epsilon for numerical stability
  , affine :: Boolean            -- ^ Has learnable affine parameters
  , numGroups :: Maybe Int       -- ^ Groups (for GroupNorm)
  }

-- | Default normalization parameters.
defaultNormParams :: NormParams
defaultNormParams =
  { eps: 1.0e-5
  , affine: true
  , numGroups: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // operation
-- ═════════════════════════════════════════════════════════════════════════════

-- | A compute operation in an ML graph.
-- |
-- | Operations are pure descriptions of computation. They specify:
-- | - What computation to perform
-- | - Parameters for the computation
-- | - Shape and type constraints
data Operation
  -- Linear operations
  = MatMul
  | Linear { outFeatures :: Int, bias :: Boolean }
  | Conv1D ConvParams
  | Conv2D ConvParams
  | Conv3D ConvParams
  
  -- Elementwise binary
  | Add
  | Mul
  | Sub
  | Div
  
  -- Elementwise unary
  | Neg
  | Abs
  | Sqrt
  | Exp
  | Log
  
  -- Activations
  | Activation ActivationType
  | Softmax { axis :: Int }
  
  -- Normalization
  | LayerNorm NormParams
  | BatchNorm NormParams
  | GroupNorm NormParams
  | RMSNorm NormParams
  
  -- Attention
  | ScaledDotProductAttention AttentionParams
  | MultiHeadAttention AttentionParams
  | FlashAttention AttentionParams
  
  -- Shape operations
  | Reshape { targetShape :: Shape }
  | Transpose { axes :: Array Int }
  | Concat { axis :: Int }
  | Split { axis :: Int, numSplits :: Int }
  | Broadcast { targetShape :: Shape }
  | Squeeze { axes :: Array Int }
  | Unsqueeze { axes :: Array Int }
  | Permute { perm :: Array Int }
  
  -- Reductions
  | ReduceSum { axes :: Array Int, keepDims :: Boolean }
  | ReduceMean { axes :: Array Int, keepDims :: Boolean }
  | ReduceMax { axes :: Array Int, keepDims :: Boolean }
  | ReduceMin { axes :: Array Int, keepDims :: Boolean }

derive instance eqOperation :: Eq Operation

instance showOperation :: Show Operation where
  show = operationName

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // linear operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matrix multiplication: [B, M, K] × [B, K, N] → [B, M, N]
matmul :: Operation
matmul = MatMul

-- | Linear (fully connected) layer: [B, inF] → [B, outF]
linear :: Int -> Boolean -> Operation
linear outFeatures bias = Linear { outFeatures, bias }

-- | 1D convolution: [B, Cin, L] → [B, Cout, Lout]
conv1d :: ConvParams -> Operation
conv1d = Conv1D

-- | 2D convolution: [B, Cin, H, W] → [B, Cout, Hout, Wout]
conv2d :: ConvParams -> Operation
conv2d = Conv2D

-- | 3D convolution: [B, Cin, D, H, W] → [B, Cout, Dout, Hout, Wout]
conv3d :: ConvParams -> Operation
conv3d = Conv3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // elementwise operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Elementwise addition
add :: Operation
add = Add

-- | Elementwise multiplication
mul :: Operation
mul = Mul

-- | Elementwise subtraction
sub :: Operation
sub = Sub

-- | Elementwise division
div :: Operation
div = Div

-- | Elementwise negation
neg :: Operation
neg = Neg

-- | Elementwise absolute value
abs :: Operation
abs = Abs

-- | Elementwise square root
sqrt :: Operation
sqrt = Sqrt

-- | Elementwise exponential
exp :: Operation
exp = Exp

-- | Elementwise natural logarithm
log :: Operation
log = Log

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // activations
-- ═════════════════════════════════════════════════════════════════════════════

-- | ReLU activation: max(0, x)
relu :: Operation
relu = Activation ReLU

-- | GELU activation: x * Φ(x)
-- |
-- | Gaussian Error Linear Unit. Default activation in transformers.
gelu :: Operation
gelu = Activation GELU

-- | SiLU activation: x * sigmoid(x)
-- |
-- | Also known as Swish. Common in modern CNNs.
silu :: Operation
silu = Activation SiLU

-- | Sigmoid activation: 1 / (1 + exp(-x))
sigmoid :: Operation
sigmoid = Activation Sigmoid

-- | Tanh activation
tanh :: Operation
tanh = Activation Tanh

-- | Softmax: exp(x) / sum(exp(x))
-- |
-- | Normalizes along specified axis to produce probability distribution.
softmax :: Int -> Operation
softmax axis = Softmax { axis }

-- | Leaky ReLU: max(slope * x, x)
leakyRelu :: Number -> Operation
leakyRelu slope = Activation (LeakyReLU { negativeSlope: slope })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // normalization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer normalization
-- |
-- | Normalizes across features for each sample.
-- | Common in transformers.
layerNorm :: NormParams -> Operation
layerNorm = LayerNorm

-- | Batch normalization
-- |
-- | Normalizes across batch for each feature.
-- | Common in CNNs.
batchNorm :: NormParams -> Operation
batchNorm = BatchNorm

-- | Group normalization
-- |
-- | Normalizes across groups of channels.
-- | Works well with small batches.
groupNorm :: NormParams -> Operation
groupNorm = GroupNorm

-- | RMS normalization
-- |
-- | Like LayerNorm but without mean centering.
-- | Used in LLaMA and other efficient transformers.
rmsnorm :: NormParams -> Operation
rmsnorm = RMSNorm

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // attention
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scaled dot-product attention
-- |
-- | Attention(Q, K, V) = softmax(QK^T / sqrt(d)) * V
scaledDotProductAttention :: AttentionParams -> Operation
scaledDotProductAttention = ScaledDotProductAttention

-- | Multi-head attention
-- |
-- | Splits Q, K, V into multiple heads, applies attention, concatenates.
multiHeadAttention :: AttentionParams -> Operation
multiHeadAttention = MultiHeadAttention

-- | Flash attention
-- |
-- | Fused, memory-efficient attention implementation.
-- | Uses tiling to reduce memory bandwidth.
flashAttention :: AttentionParams -> Operation
flashAttention = FlashAttention

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // shape operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reshape tensor (element count must match)
reshape :: Shape -> Operation
reshape targetShape = Reshape { targetShape }

-- | Transpose (swap last two dimensions)
transpose :: Array Int -> Operation
transpose axes = Transpose { axes }

-- | Concatenate tensors along axis
concat :: Int -> Operation
concat axis = Concat { axis }

-- | Split tensor along axis
split :: Int -> Int -> Operation
split axis numSplits = Split { axis, numSplits }

-- | Broadcast to target shape
broadcast :: Shape -> Operation
broadcast targetShape = Broadcast { targetShape }

-- | Remove dimensions of size 1
squeeze :: Array Int -> Operation
squeeze axes = Squeeze { axes }

-- | Add dimensions of size 1
unsqueeze :: Array Int -> Operation
unsqueeze axes = Unsqueeze { axes }

-- | Permute dimensions
permute :: Array Int -> Operation
permute perm = Permute { perm }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // reduction operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum reduction along axes
reduceSum :: Array Int -> Boolean -> Operation
reduceSum axes keepDims = ReduceSum { axes, keepDims }

-- | Mean reduction along axes
reduceMean :: Array Int -> Boolean -> Operation
reduceMean axes keepDims = ReduceMean { axes, keepDims }

-- | Max reduction along axes
reduceMax :: Array Int -> Boolean -> Operation
reduceMax axes keepDims = ReduceMax { axes, keepDims }

-- | Min reduction along axes
reduceMin :: Array Int -> Boolean -> Operation
reduceMin axes keepDims = ReduceMin { axes, keepDims }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // operation properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this an elementwise operation?
-- |
-- | Elementwise operations apply independently to each element.
isElementwise :: Operation -> Boolean
isElementwise Add = true
isElementwise Mul = true
isElementwise Sub = true
isElementwise Div = true
isElementwise Neg = true
isElementwise Abs = true
isElementwise Sqrt = true
isElementwise Exp = true
isElementwise Log = true
isElementwise (Activation _) = true
isElementwise _ = false

-- | Is this a linear operation?
-- |
-- | Linear operations involve matrix/tensor multiplication.
isLinear :: Operation -> Boolean
isLinear MatMul = true
isLinear (Linear _) = true
isLinear (Conv1D _) = true
isLinear (Conv2D _) = true
isLinear (Conv3D _) = true
isLinear _ = false

-- | Is this a reduction operation?
isReduction :: Operation -> Boolean
isReduction (ReduceSum _) = true
isReduction (ReduceMean _) = true
isReduction (ReduceMax _) = true
isReduction (ReduceMin _) = true
isReduction _ = false

-- | Does this operation require training mode?
-- |
-- | Some operations behave differently during training vs inference.
requiresTraining :: Operation -> Boolean
requiresTraining (BatchNorm _) = true
requiresTraining _ = false

-- | Get human-readable operation name.
operationName :: Operation -> String
operationName MatMul = "MatMul"
operationName (Linear _) = "Linear"
operationName (Conv1D _) = "Conv1D"
operationName (Conv2D _) = "Conv2D"
operationName (Conv3D _) = "Conv3D"
operationName Add = "Add"
operationName Mul = "Mul"
operationName Sub = "Sub"
operationName Div = "Div"
operationName Neg = "Neg"
operationName Abs = "Abs"
operationName Sqrt = "Sqrt"
operationName Exp = "Exp"
operationName Log = "Log"
operationName (Activation a) = show a
operationName (Softmax _) = "Softmax"
operationName (LayerNorm _) = "LayerNorm"
operationName (BatchNorm _) = "BatchNorm"
operationName (GroupNorm _) = "GroupNorm"
operationName (RMSNorm _) = "RMSNorm"
operationName (ScaledDotProductAttention _) = "ScaledDotProductAttention"
operationName (MultiHeadAttention _) = "MultiHeadAttention"
operationName (FlashAttention _) = "FlashAttention"
operationName (Reshape _) = "Reshape"
operationName (Transpose _) = "Transpose"
operationName (Concat _) = "Concat"
operationName (Split _) = "Split"
operationName (Broadcast _) = "Broadcast"
operationName (Squeeze _) = "Squeeze"
operationName (Unsqueeze _) = "Unsqueeze"
operationName (Permute _) = "Permute"
operationName (ReduceSum _) = "ReduceSum"
operationName (ReduceMean _) = "ReduceMean"
operationName (ReduceMax _) = "ReduceMax"
operationName (ReduceMin _) = "ReduceMin"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // shape inference
-- ═════════════════════════════════════════════════════════════════════════════

-- | Infer output shape from operation and input shapes.
-- |
-- | Returns Nothing if shapes are incompatible.
inferOutputShape :: Operation -> Array Shape -> Maybe Shape
inferOutputShape MatMul inputs = do
  a <- Array.index inputs 0
  b <- Array.index inputs 1
  inferMatmulShape a b
inferOutputShape (Linear { outFeatures }) inputs = do
  input <- Array.index inputs 0
  let inputDims = dims input
  let outDim = dim outFeatures
  case Array.init inputDims of
    Nothing -> Nothing
    Just batchDims -> pure $ shapeFromArray (batchDims <> [outDim])
inferOutputShape (Reshape { targetShape }) _ = Just targetShape
inferOutputShape (Broadcast { targetShape }) _ = Just targetShape
inferOutputShape op inputs
  | isElementwise op = Array.head inputs  -- Elementwise: output = input shape
  | true = Nothing

-- | Infer matmul output shape: [B, M, K] × [B, K, N] → [B, M, N]
inferMatmulShape :: Shape -> Shape -> Maybe Shape
inferMatmulShape a b = do
  let aDims = dims a
  let bDims = dims b
  let aRank = Array.length aDims
  let bRank = Array.length bDims
  -- Need at least 2D
  _ <- if aRank >= 2 && bRank >= 2 then Just true else Nothing
  -- Check inner dimensions match
  aK <- Array.index aDims (aRank - 1)
  bK <- Array.index bDims (bRank - 2)
  _ <- if aK == bK then Just true else Nothing
  -- Compute output shape
  aM <- Array.index aDims (aRank - 2)
  bN <- Array.index bDims (bRank - 1)
  -- Batch dimensions from larger operand
  let batchDims = if aRank >= bRank 
                  then Array.take (aRank - 2) aDims 
                  else Array.take (bRank - 2) bDims
  pure $ shapeFromArray (batchDims <> [aM, bN])

-- | Check if input shapes are valid for operation.
checkInputShapes :: Operation -> Array Shape -> Boolean
checkInputShapes op inputs = case inferOutputShape op inputs of
  Just _ -> true
  Nothing -> false
