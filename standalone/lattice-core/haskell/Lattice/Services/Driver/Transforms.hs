{-|
Module      : Lattice.Services.Driver.Transforms
Description : Property Driver Transforms
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for transforming property values in
property-to-property linking (drivers). These transforms are applied
as a chain to map source values to target values.

Features:
- Scale, offset, clamp transforms
- Value remapping (input range → output range)
- Threshold gating (binary output)
- Oscillation (sinusoidal modulation)
- Value inversion
- Temporal smoothing (low-pass filter)
- Blend modes (replace, add, multiply)

Source: ui/src/services/propertyDriver.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Driver.Transforms
  ( -- * Types
    TransformType(..)
  , BlendMode(..)
  , Transform(..)
    -- * Individual Transforms
  , applyScale
  , applyOffset
  , applyClamp
  , applySmooth
  , applyInvert
  , applyRemap
  , applyThreshold
  , applyOscillate
    -- * Transform Chain
  , applyTransformWithPrev
  , applyTransform
  , applyTransformChain
    -- * Blend Modes
  , blendValue
    -- * Constructors
  , mkScaleTransform
  , mkOffsetTransform
  , mkClampTransform
  , mkRemapTransform
  , mkThresholdTransform
  , mkOscillateTransform
  , defaultTransform
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V

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
  deriving (Show, Eq)

-- | Blend mode for combining base and driven values
data BlendMode
  = BlendReplace   -- ^ Use driven value directly
  | BlendAdd       -- ^ Add driven to base
  | BlendMultiply  -- ^ Multiply base by driven
  deriving (Show, Eq)

-- | Transform configuration
data Transform = Transform
  { trType      :: TransformType
  , trFactor    :: Double  -- ^ Scale factor
  , trAmount    :: Double  -- ^ Offset amount
  , trMinVal    :: Double  -- ^ Clamp minimum
  , trMaxVal    :: Double  -- ^ Clamp maximum
  , trSmoothing :: Double  -- ^ Smoothing coefficient (0-1)
  , trInMin     :: Double  -- ^ Remap input minimum
  , trInMax     :: Double  -- ^ Remap input maximum
  , trOutMin    :: Double  -- ^ Remap output minimum
  , trOutMax    :: Double  -- ^ Remap output maximum
  , trThreshold :: Double  -- ^ Threshold value
  , trFrequency :: Double  -- ^ Oscillate frequency
  , trAmplitude :: Double  -- ^ Oscillate amplitude
  , trPhase     :: Double  -- ^ Oscillate phase
  } deriving (Show, Eq)

-- | Default transform
defaultTransform :: Transform
defaultTransform = Transform
  { trType = TransformScale
  , trFactor = 1
  , trAmount = 0
  , trMinVal = 0
  , trMaxVal = 1
  , trSmoothing = 0.5
  , trInMin = 0
  , trInMax = 1
  , trOutMin = 0
  , trOutMax = 1
  , trThreshold = 0.5
  , trFrequency = 1
  , trAmplitude = 1
  , trPhase = 0
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Individual Transform Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Scale transform: value * factor
applyScale :: Double -> Double -> Double
applyScale value factor = value * factor

-- | Offset transform: value + amount
applyOffset :: Double -> Double -> Double
applyOffset value amount = value + amount

-- | Clamp transform: clamp(value, min, max)
applyClamp :: Double -> Double -> Double -> Double
applyClamp value minVal maxVal = max minVal (min maxVal value)

-- | Smooth transform: exponential smoothing (one-pole low-pass filter).
--
-- Formula: smoothed = prevValue * smoothing + value * (1 - smoothing)
applySmooth :: Double -> Double -> Double -> Double
applySmooth value prevValue smoothing =
  let s = max 0 (min 1 smoothing)
  in prevValue * s + value * (1 - s)

-- | Invert transform: 1 - value
applyInvert :: Double -> Double
applyInvert value = 1 - value

-- | Remap transform: map value from [inMin, inMax] to [outMin, outMax].
--
-- Handles zero input range by returning midpoint of output range.
applyRemap :: Double -> Double -> Double -> Double -> Double -> Double
applyRemap value inMin inMax outMin outMax =
  let inRange = inMax - inMin
  in if inRange == 0
     then (outMin + outMax) / 2
     else let normalized = (value - inMin) / inRange
          in outMin + normalized * (outMax - outMin)

-- | Threshold transform: value > threshold ? 1 : 0
applyThreshold :: Double -> Double -> Double
applyThreshold value thresholdVal =
  if value > thresholdVal then 1 else 0

-- | Oscillate transform: sin((value * frequency + phase) * 2π) * amplitude
applyOscillate :: Double -> Double -> Double -> Double -> Double
applyOscillate value frequency amplitude phase =
  let freq = if frequency <= 0 then 1 else frequency
      amp = if amplitude < 0 then 0 else amplitude
  in sin ((value * freq + phase) * pi * 2) * amp

-- ────────────────────────────────────────────────────────────────────────────
-- Transform Chain
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply a single transform to a value.
--
-- For smooth transform, requires previous smoothed value.
applyTransformWithPrev :: Transform -> Double -> Double -> Double
applyTransformWithPrev transform value prevValue =
  case trType transform of
    TransformScale     -> applyScale value (trFactor transform)
    TransformOffset    -> applyOffset value (trAmount transform)
    TransformClamp     -> applyClamp value (trMinVal transform) (trMaxVal transform)
    TransformSmooth    -> applySmooth value prevValue (trSmoothing transform)
    TransformInvert    -> applyInvert value
    TransformRemap     -> applyRemap value (trInMin transform) (trInMax transform)
                            (trOutMin transform) (trOutMax transform)
    TransformThreshold -> applyThreshold value (trThreshold transform)
    TransformOscillate -> applyOscillate value (trFrequency transform)
                            (trAmplitude transform) (trPhase transform)

-- | Apply a single transform to a value (no smoothing state).
applyTransform :: Transform -> Double -> Double
applyTransform transform value = applyTransformWithPrev transform value value

-- | Apply a chain of transforms to a value.
applyTransformChain :: Vector Transform -> Double -> Double
applyTransformChain transforms value =
  V.foldl' (\v t -> applyTransform t v) value transforms

-- ────────────────────────────────────────────────────────────────────────────
-- Blend Modes
-- ────────────────────────────────────────────────────────────────────────────

-- | Blend driven value with base value using blend mode.
blendValue :: Double -> Double -> BlendMode -> Double -> Double
blendValue base driven mode amount =
  let result = case mode of
        BlendReplace  -> driven
        BlendAdd      -> base + driven
        BlendMultiply -> base * driven
  -- Mix between base and result based on blend amount
  in base * (1 - amount) + result * amount

-- ────────────────────────────────────────────────────────────────────────────
-- Constructors
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a scale transform
mkScaleTransform :: Double -> Transform
mkScaleTransform factor = defaultTransform { trType = TransformScale, trFactor = factor }

-- | Create an offset transform
mkOffsetTransform :: Double -> Transform
mkOffsetTransform amount = defaultTransform { trType = TransformOffset, trAmount = amount }

-- | Create a clamp transform
mkClampTransform :: Double -> Double -> Transform
mkClampTransform minVal maxVal = defaultTransform
  { trType = TransformClamp, trMinVal = minVal, trMaxVal = maxVal }

-- | Create a remap transform
mkRemapTransform :: Double -> Double -> Double -> Double -> Transform
mkRemapTransform inMin inMax outMin outMax = defaultTransform
  { trType = TransformRemap
  , trInMin = inMin
  , trInMax = inMax
  , trOutMin = outMin
  , trOutMax = outMax
  }

-- | Create a threshold transform
mkThresholdTransform :: Double -> Transform
mkThresholdTransform thresholdVal = defaultTransform
  { trType = TransformThreshold, trThreshold = thresholdVal }

-- | Create an oscillate transform
mkOscillateTransform :: Double -> Double -> Double -> Transform
mkOscillateTransform frequency amplitude phase = defaultTransform
  { trType = TransformOscillate
  , trFrequency = frequency
  , trAmplitude = amplitude
  , trPhase = phase
  }
