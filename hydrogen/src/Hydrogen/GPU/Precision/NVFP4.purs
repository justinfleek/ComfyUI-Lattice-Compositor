-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // precision // nvfp4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NVFP4 Quantization — 4-bit Floating Point with Four Over Six Scaling
-- |
-- | ## Purpose
-- |
-- | NVFP4 is NVIDIA's 4-bit floating point format for Blackwell GPUs:
-- | - FP4 E2M1 values: ±{0, 0.5, 1, 1.5, 2, 3, 4, 6}
-- | - FP8 E4M3 block scale per 16 values
-- | - FP32 tensor-wide scale
-- |
-- | ## The Four Over Six Innovation
-- |
-- | Standard NVFP4 scales blocks to max=6. Problem: values between 66.6%-100%
-- | of block max round poorly (up to 16.7% error at 83% of max).
-- |
-- | Four Over Six adaptively scales some blocks to max=4 instead:
-- | - Values at 75% of max → 3 (exact representation with max=4)
-- | - MSE-based selection chooses optimal scaling per block
-- | - 22.3% closer to BF16 baseline in training
-- |
-- | ## Landauer Integration
-- |
-- | Per the Landauer precision principle: precision is a measured physical
-- | quantity, not a hyperparameter. The epilogue (post-accumulator) is the
-- | last reversible place to change precision gauges.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | NVFP4 enables:
-- | - 4× memory reduction vs FP16
-- | - Deterministic quantization (same input → same output)
-- | - Bounded error guarantees (types encode valid ranges)
-- |
-- | ## References
-- |
-- | - "Four Over Six" (Cook et al., 2026) — Adaptive block scaling
-- | - "Pretraining LLMs with NVFP4" (NVIDIA, 2025) — Training pipeline
-- | - "Landauer Precision" — Thermodynamic precision framework

module Hydrogen.GPU.Precision.NVFP4
  ( -- * FP4 E2M1 Representation
    FP4Value
      ( FP4_Zero
      , FP4_Half
      , FP4_One
      , FP4_OneHalf
      , FP4_Two
      , FP4_Three
      , FP4_Four
      , FP4_Six
      )
  , FP4Sign(Positive, Negative)
  , SignedFP4
  
  -- * Block Scaling
  , BlockSize
  , blockSize16
  , FP8Scale
  , mkFP8Scale
  , unwrapFP8Scale
  , BlockScaledFP4
  , mkBlockScaledFP4
  
  -- * Tensor Scale
  , TensorScale
  , mkTensorScale
  , unwrapTensorScale
  
  -- * Four Over Six Selection
  , ScaleMode(ScaleMax6, ScaleMax4)
  , FourOverSixBlock
  , quantizeFourOverSix
  , selectScaleMode
  
  -- * Quantization
  , quantizeToFP4
  , dequantizeFP4
  , roundToNearestFP4
  
  -- * Block Operations
  , quantizeBlock
  , dequantizeBlock
  , blockMSE
  
  -- * Tensor Operations
  , NVFP4Tensor
  , mkNVFP4Tensor
  , quantizeTensor
  , dequantizeTensor
  
  -- * Precision Analysis
  , maxFP4Error
  , avgFP4Error
  , isBlockBetterWithMax4
  
  -- * Constants
  , fp4Values
  , fp4MaxValue
  , fp4MinPositive
  , fp8MaxScale
  , defaultTensorScaleDivisor
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semiring
  , show
  , map
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (/=)
  , (<>)
  , (&&)
  , negate
  , min
  , max
  , zero
  , one
  )

import Data.Array as Array
import Data.Int as Int
import Data.Number (abs) as Number
import Data.Number as Number
import Data.Foldable (sum, foldl)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // fp4 e2m1 type
-- ═════════════════════════════════════════════════════════════════════════════

-- | FP4 E2M1 representable values (unsigned)
-- |
-- | The 8 positive values in FP4 E2M1 format.
-- | Non-uniform spacing: 0.5 steps near 0, 1.0 steps mid-range, 2.0 steps at top.
data FP4Value
  = FP4_Zero      -- 0.0
  | FP4_Half      -- 0.5
  | FP4_One       -- 1.0
  | FP4_OneHalf   -- 1.5
  | FP4_Two       -- 2.0
  | FP4_Three     -- 3.0
  | FP4_Four      -- 4.0
  | FP4_Six       -- 6.0

derive instance eqFP4Value :: Eq FP4Value
derive instance ordFP4Value :: Ord FP4Value

instance showFP4Value :: Show FP4Value where
  show FP4_Zero = "FP4(0)"
  show FP4_Half = "FP4(0.5)"
  show FP4_One = "FP4(1)"
  show FP4_OneHalf = "FP4(1.5)"
  show FP4_Two = "FP4(2)"
  show FP4_Three = "FP4(3)"
  show FP4_Four = "FP4(4)"
  show FP4_Six = "FP4(6)"

-- | Convert FP4Value to Number
fp4ToNumber :: FP4Value -> Number
fp4ToNumber FP4_Zero = 0.0
fp4ToNumber FP4_Half = 0.5
fp4ToNumber FP4_One = 1.0
fp4ToNumber FP4_OneHalf = 1.5
fp4ToNumber FP4_Two = 2.0
fp4ToNumber FP4_Three = 3.0
fp4ToNumber FP4_Four = 4.0
fp4ToNumber FP4_Six = 6.0

-- | All FP4 values in ascending order
fp4Values :: Array FP4Value
fp4Values = 
  [ FP4_Zero
  , FP4_Half
  , FP4_One
  , FP4_OneHalf
  , FP4_Two
  , FP4_Three
  , FP4_Four
  , FP4_Six
  ]

-- | Maximum FP4 value
fp4MaxValue :: Number
fp4MaxValue = 6.0

-- | Minimum positive FP4 value
fp4MinPositive :: Number
fp4MinPositive = 0.5

-- | Sign for signed FP4
data FP4Sign = Positive | Negative

derive instance eqFP4Sign :: Eq FP4Sign
derive instance ordFP4Sign :: Ord FP4Sign

instance showFP4Sign :: Show FP4Sign where
  show Positive = "+"
  show Negative = "-"

-- | Signed FP4 value
type SignedFP4 = { sign :: FP4Sign, magnitude :: FP4Value }

-- | Convert SignedFP4 to Number
signedFP4ToNumber :: SignedFP4 -> Number
signedFP4ToNumber sfp4 =
  let mag = fp4ToNumber sfp4.magnitude
  in case sfp4.sign of
       Positive -> mag
       Negative -> negate mag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // fp4 quantization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Round a normalized value to the nearest FP4 representation
-- |
-- | Input should be pre-scaled to [0, 6] range.
-- | Uses non-uniform rounding due to FP4's step sizes:
-- | - 0.5 steps in [0, 2)
-- | - 1.0 steps in [2, 4)
-- | - 2.0 steps in [4, 6]
roundToNearestFP4 :: Number -> FP4Value
roundToNearestFP4 x
  | x < 0.25 = FP4_Zero
  | x < 0.75 = FP4_Half
  | x < 1.25 = FP4_One
  | x < 1.75 = FP4_OneHalf
  | x < 2.5 = FP4_Two
  | x < 3.5 = FP4_Three
  | x < 5.0 = FP4_Four
  | true = FP4_Six

-- | Quantize a number to signed FP4
quantizeToFP4 :: Number -> SignedFP4
quantizeToFP4 x =
  let sign = if x >= 0.0 then Positive else Negative
      magnitude = roundToNearestFP4 (Number.abs x)
  in { sign, magnitude }

-- | Dequantize signed FP4 to Number
dequantizeFP4 :: SignedFP4 -> Number
dequantizeFP4 = signedFP4ToNumber

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // block scaling
-- ═════════════════════════════════════════════════════════════════════════════

-- | NVFP4 block size (always 16)
newtype BlockSize = BlockSize Int

derive instance eqBlockSize :: Eq BlockSize

instance showBlockSize :: Show BlockSize where
  show (BlockSize n) = "(BlockSize " <> show n <> ")"

-- | Standard NVFP4 block size
blockSize16 :: BlockSize
blockSize16 = BlockSize 16

-- | FP8 E4M3 scale factor
-- |
-- | Bounded to [0, 448] for standard NVFP4, or [0, 384] for 4/6 compatibility.
newtype FP8Scale = FP8Scale Number

derive instance eqFP8Scale :: Eq FP8Scale
derive instance ordFP8Scale :: Ord FP8Scale

instance showFP8Scale :: Show FP8Scale where
  show (FP8Scale s) = "(FP8Scale " <> show s <> ")"

-- | Maximum FP8 E4M3 scale (standard)
fp8MaxScale :: Number
fp8MaxScale = 448.0

-- | Create a bounded FP8 scale
mkFP8Scale :: Number -> FP8Scale
mkFP8Scale s = FP8Scale (min fp8MaxScale (max 0.0 s))

-- | Unwrap FP8 scale
unwrapFP8Scale :: FP8Scale -> Number
unwrapFP8Scale (FP8Scale s) = s

-- | Block-scaled FP4 representation
type BlockScaledFP4 =
  { values :: Array SignedFP4    -- exactly 16 values
  , scale :: FP8Scale            -- block scale
  , usedMax4 :: Boolean          -- 4/6 flag
  }

-- | Create a block-scaled FP4 from values and scale
mkBlockScaledFP4 :: Array SignedFP4 -> FP8Scale -> Boolean -> BlockScaledFP4
mkBlockScaledFP4 values scale usedMax4 = { values, scale, usedMax4 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // tensor scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tensor-wide scale factor (FP32)
newtype TensorScale = TensorScale Number

derive instance eqTensorScale :: Eq TensorScale
derive instance ordTensorScale :: Ord TensorScale

instance showTensorScale :: Show TensorScale where
  show (TensorScale s) = "(TensorScale " <> show s <> ")"

-- | Default divisor for tensor scale: M_FP4 × M_FP8
-- | Standard: 6 × 448 = 2688
-- | Four Over Six: 6 × 256 = 1536 (allows 1.5× headroom)
defaultTensorScaleDivisor :: Number
defaultTensorScaleDivisor = 6.0 * 256.0  -- 4/6 compatible

-- | Create tensor scale from max absolute value
mkTensorScale :: Number -> TensorScale
mkTensorScale maxAbs = TensorScale (maxAbs / defaultTensorScaleDivisor)

-- | Unwrap tensor scale
unwrapTensorScale :: TensorScale -> Number
unwrapTensorScale (TensorScale s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // four over six core
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale mode selection
data ScaleMode = ScaleMax6 | ScaleMax4

derive instance eqScaleMode :: Eq ScaleMode
derive instance ordScaleMode :: Ord ScaleMode

instance showScaleMode :: Show ScaleMode where
  show ScaleMax6 = "ScaleMax6"
  show ScaleMax4 = "ScaleMax4"

-- | Four Over Six quantized block
type FourOverSixBlock =
  { quantized :: Array SignedFP4
  , scale :: FP8Scale
  , mode :: ScaleMode
  , mse :: Number
  }

-- | Compute MSE between original and dequantized values
blockMSE :: Array Number -> Array Number -> Number
blockMSE original dequantized =
  let squaredErrors = Array.zipWith computeSquaredError original dequantized
      n = Int.toNumber (Array.length original)
  in if n > 0.0 then sum squaredErrors / n else 0.0
  where
    computeSquaredError :: Number -> Number -> Number
    computeSquaredError o d = 
      let diff = o - d
      in diff * diff

-- | Quantize a block with a specific max value (4 or 6)
quantizeBlockWithMax :: Number -> Array Number -> TensorScale -> Number 
                     -> { quantized :: Array SignedFP4, scale :: FP8Scale, dequantized :: Array Number }
quantizeBlockWithMax maxVal block tensorScale blockMax =
  let alpha = unwrapTensorScale tensorScale
      delta = blockMax / (alpha * maxVal)
      fp8Delta = mkFP8Scale delta
      actualDelta = unwrapFP8Scale fp8Delta
      
      quantized = map (\x -> 
        let scaled = x / (alpha * actualDelta)
            clampedScaled = min maxVal (max (negate maxVal) scaled)
        in quantizeToFP4 clampedScaled) block
      
      dequantized = map (\sfp4 -> 
        signedFP4ToNumber sfp4 * actualDelta * alpha) quantized
  in { quantized, scale: fp8Delta, dequantized }

-- | Select the better scale mode based on MSE
selectScaleMode :: Array Number -> TensorScale -> Number -> ScaleMode
selectScaleMode block tensorScale blockMax =
  let result6 = quantizeBlockWithMax 6.0 block tensorScale blockMax
      result4 = quantizeBlockWithMax 4.0 block tensorScale blockMax
      mse6 = blockMSE block result6.dequantized
      mse4 = blockMSE block result4.dequantized
  in if mse4 < mse6 then ScaleMax4 else ScaleMax6

-- | Quantize a block using Four Over Six adaptive scaling
quantizeFourOverSix :: Array Number -> TensorScale -> FourOverSixBlock
quantizeFourOverSix block tensorScale =
  let blockMax = foldl (\acc x -> max acc (Number.abs x)) 0.0 block
      mode = selectScaleMode block tensorScale blockMax
      maxVal = case mode of
                 ScaleMax6 -> 6.0
                 ScaleMax4 -> 4.0
      result = quantizeBlockWithMax maxVal block tensorScale blockMax
      mse = blockMSE block result.dequantized
  in { quantized: result.quantized
     , scale: result.scale
     , mode
     , mse
     }

-- | Check if a block would be better with max=4
isBlockBetterWithMax4 :: Array Number -> TensorScale -> Boolean
isBlockBetterWithMax4 block tensorScale =
  selectScaleMode block tensorScale (foldl (\acc x -> max acc (Number.abs x)) 0.0 block) == ScaleMax4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // block operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quantize a block (standard, max=6)
quantizeBlock :: Array Number -> TensorScale -> BlockScaledFP4
quantizeBlock block tensorScale =
  let result = quantizeFourOverSix block tensorScale
      usedMax4 = result.mode == ScaleMax4
  in { values: result.quantized
     , scale: result.scale
     , usedMax4
     }

-- | Dequantize a block
dequantizeBlock :: BlockScaledFP4 -> TensorScale -> Array Number
dequantizeBlock block tensorScale =
  let alpha = unwrapTensorScale tensorScale
      delta = unwrapFP8Scale block.scale
  in map (\sfp4 -> signedFP4ToNumber sfp4 * delta * alpha) block.values

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // tensor operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | NVFP4 quantized tensor
type NVFP4Tensor =
  { blocks :: Array BlockScaledFP4
  , tensorScale :: TensorScale
  , shape :: { rows :: Int, cols :: Int }
  }

-- | Create an NVFP4 tensor
mkNVFP4Tensor :: Array BlockScaledFP4 -> TensorScale -> Int -> Int -> NVFP4Tensor
mkNVFP4Tensor blocks tensorScale rows cols = 
  { blocks, tensorScale, shape: { rows, cols } }

-- | Quantize a tensor to NVFP4
quantizeTensor :: Array Number -> Int -> Int -> NVFP4Tensor
quantizeTensor values rows cols =
  let maxAbs = foldl (\acc x -> max acc (Number.abs x)) 0.0 values
      tensorScale = mkTensorScale maxAbs
      chunks = chunksOf 16 values
      blocks = map (\chunk -> quantizeBlock chunk tensorScale) chunks
  in { blocks, tensorScale, shape: { rows, cols } }

-- | Dequantize an NVFP4 tensor
dequantizeTensor :: NVFP4Tensor -> Array Number
dequantizeTensor tensor =
  Array.concat (map (\block -> dequantizeBlock block tensor.tensorScale) tensor.blocks)

-- | Split array into chunks of size n
chunksOf :: forall a. Int -> Array a -> Array (Array a)
chunksOf n arr =
  if Array.length arr <= n then [arr]
  else case Array.splitAt n arr of
         { before, after } -> [before] <> chunksOf n after

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // precision analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum quantization error in a block
maxFP4Error :: Array Number -> Array Number -> Number
maxFP4Error original dequantized =
  let errors = Array.zipWith (\o d -> Number.abs (o - d)) original dequantized
  in foldl max 0.0 errors

-- | Average quantization error in a block
avgFP4Error :: Array Number -> Array Number -> Number
avgFP4Error original dequantized =
  let errors = Array.zipWith (\o d -> Number.abs (o - d)) original dequantized
      n = Int.toNumber (Array.length errors)
  in if n > 0.0 then sum errors / n else 0.0
