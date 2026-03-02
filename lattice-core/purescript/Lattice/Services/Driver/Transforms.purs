-- | Lattice.Services.Driver.Transforms - Property Driver Transforms
-- |
-- | Pure mathematical functions for transforming property values in
-- | property-to-property linking (drivers). These transforms are applied
-- | as a chain to map source values to target values.
-- |
-- | Features:
-- | - Scale, offset, clamp transforms
-- | - Value remapping (input range → output range)
-- | - Threshold gating (binary output)
-- | - Oscillation (sinusoidal modulation)
-- | - Value inversion
-- | - Temporal smoothing (low-pass filter)
-- | - Blend modes (replace, add, multiply)
-- |
-- | Source: ui/src/services/propertyDriver.ts

module Lattice.Services.Driver.Transforms
  ( TransformType(..)
  , BlendMode(..)
  , Transform
  , defaultTransform
  , applyScale
  , applyOffset
  , applyClamp
  , applySmooth
  , applyInvert
  , applyRemap
  , applyThreshold
  , applyOscillate
  , applyTransformWithPrev
  , applyTransform
  , applyTransformChain
  , blendValue
  , mkScaleTransform
  , mkOffsetTransform
  , mkClampTransform
  , mkRemapTransform
  , mkThresholdTransform
  , mkOscillateTransform
  ) where

import Prelude

import Data.Array (foldl)
import Math (pi, sin)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Transform type for property drivers
data TransformType
  = TransformScale
  | TransformOffset
  | TransformClamp
  | TransformSmooth
  | TransformInvert
  | TransformRemap
  | TransformThreshold
  | TransformOscillate

derive instance eqTransformType :: Eq TransformType

-- | Blend mode for combining base and driven values
data BlendMode
  = BlendReplace   -- ^ Use driven value directly
  | BlendAdd       -- ^ Add driven to base
  | BlendMultiply  -- ^ Multiply base by driven

derive instance eqBlendMode :: Eq BlendMode

-- | Transform configuration
type Transform =
  { transformType :: TransformType
  , factor    :: Number  -- ^ Scale factor
  , amount    :: Number  -- ^ Offset amount
  , minVal    :: Number  -- ^ Clamp minimum
  , maxVal    :: Number  -- ^ Clamp maximum
  , smoothing :: Number  -- ^ Smoothing coefficient (0-1)
  , inMin     :: Number  -- ^ Remap input minimum
  , inMax     :: Number  -- ^ Remap input maximum
  , outMin    :: Number  -- ^ Remap output minimum
  , outMax    :: Number  -- ^ Remap output maximum
  , threshold :: Number  -- ^ Threshold value
  , frequency :: Number  -- ^ Oscillate frequency
  , amplitude :: Number  -- ^ Oscillate amplitude
  , phase     :: Number  -- ^ Oscillate phase
  }

-- | Default transform
defaultTransform :: Transform
defaultTransform =
  { transformType: TransformScale
  , factor: 1.0
  , amount: 0.0
  , minVal: 0.0
  , maxVal: 1.0
  , smoothing: 0.5
  , inMin: 0.0
  , inMax: 1.0
  , outMin: 0.0
  , outMax: 1.0
  , threshold: 0.5
  , frequency: 1.0
  , amplitude: 1.0
  , phase: 0.0
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Individual Transform Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Scale transform: value * factor
applyScale :: Number -> Number -> Number
applyScale value factor = value * factor

-- | Offset transform: value + amount
applyOffset :: Number -> Number -> Number
applyOffset value amount = value + amount

-- | Clamp transform: clamp(value, min, max)
applyClamp :: Number -> Number -> Number -> Number
applyClamp value minVal maxVal = max minVal (min maxVal value)

-- | Smooth transform: exponential smoothing (one-pole low-pass filter).
-- |
-- | Formula: smoothed = prevValue * smoothing + value * (1 - smoothing)
applySmooth :: Number -> Number -> Number -> Number
applySmooth value prevValue smoothing =
  let s = max 0.0 (min 1.0 smoothing)
  in prevValue * s + value * (1.0 - s)

-- | Invert transform: 1 - value
applyInvert :: Number -> Number
applyInvert value = 1.0 - value

-- | Remap transform: map value from [inMin, inMax] to [outMin, outMax].
-- |
-- | Handles zero input range by returning midpoint of output range.
applyRemap :: Number -> Number -> Number -> Number -> Number -> Number
applyRemap value inMin inMax outMin outMax =
  let inRange = inMax - inMin
  in if inRange == 0.0
     then (outMin + outMax) / 2.0
     else let normalized = (value - inMin) / inRange
          in outMin + normalized * (outMax - outMin)

-- | Threshold transform: value > threshold ? 1 : 0
applyThreshold :: Number -> Number -> Number
applyThreshold value thresholdVal =
  if value > thresholdVal then 1.0 else 0.0

-- | Oscillate transform: sin((value * frequency + phase) * 2π) * amplitude
applyOscillate :: Number -> Number -> Number -> Number -> Number
applyOscillate value frequency amplitude phase =
  let freq = if frequency <= 0.0 then 1.0 else frequency
      amp = if amplitude < 0.0 then 0.0 else amplitude
  in sin ((value * freq + phase) * pi * 2.0) * amp

-- ────────────────────────────────────────────────────────────────────────────
-- Transform Chain
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply a single transform to a value.
-- |
-- | For smooth transform, requires previous smoothed value.
applyTransformWithPrev :: Transform -> Number -> Number -> Number
applyTransformWithPrev transform value prevValue =
  case transform.transformType of
    TransformScale     -> applyScale value transform.factor
    TransformOffset    -> applyOffset value transform.amount
    TransformClamp     -> applyClamp value transform.minVal transform.maxVal
    TransformSmooth    -> applySmooth value prevValue transform.smoothing
    TransformInvert    -> applyInvert value
    TransformRemap     -> applyRemap value transform.inMin transform.inMax
                            transform.outMin transform.outMax
    TransformThreshold -> applyThreshold value transform.threshold
    TransformOscillate -> applyOscillate value transform.frequency
                            transform.amplitude transform.phase

-- | Apply a single transform to a value (no smoothing state).
applyTransform :: Transform -> Number -> Number
applyTransform transform value = applyTransformWithPrev transform value value

-- | Apply a chain of transforms to a value.
applyTransformChain :: Array Transform -> Number -> Number
applyTransformChain transforms value =
  foldl (\v t -> applyTransform t v) value transforms

-- ────────────────────────────────────────────────────────────────────────────
-- Blend Modes
-- ────────────────────────────────────────────────────────────────────────────

-- | Blend driven value with base value using blend mode.
blendValue :: Number -> Number -> BlendMode -> Number -> Number
blendValue base driven mode amount =
  let result = case mode of
        BlendReplace  -> driven
        BlendAdd      -> base + driven
        BlendMultiply -> base * driven
  -- Mix between base and result based on blend amount
  in base * (1.0 - amount) + result * amount

-- ────────────────────────────────────────────────────────────────────────────
-- Constructors
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a scale transform
mkScaleTransform :: Number -> Transform
mkScaleTransform factor = defaultTransform { transformType = TransformScale, factor = factor }

-- | Create an offset transform
mkOffsetTransform :: Number -> Transform
mkOffsetTransform amount = defaultTransform { transformType = TransformOffset, amount = amount }

-- | Create a clamp transform
mkClampTransform :: Number -> Number -> Transform
mkClampTransform minVal maxVal = defaultTransform
  { transformType = TransformClamp, minVal = minVal, maxVal = maxVal }

-- | Create a remap transform
mkRemapTransform :: Number -> Number -> Number -> Number -> Transform
mkRemapTransform inMin inMax outMin outMax = defaultTransform
  { transformType = TransformRemap
  , inMin = inMin
  , inMax = inMax
  , outMin = outMin
  , outMax = outMax
  }

-- | Create a threshold transform
mkThresholdTransform :: Number -> Transform
mkThresholdTransform thresholdVal = defaultTransform
  { transformType = TransformThreshold, threshold = thresholdVal }

-- | Create an oscillate transform
mkOscillateTransform :: Number -> Number -> Number -> Transform
mkOscillateTransform frequency amplitude phase = defaultTransform
  { transformType = TransformOscillate
  , frequency = frequency
  , amplitude = amplitude
  , phase = phase
  }
