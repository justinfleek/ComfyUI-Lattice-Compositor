-- | Lattice.Services.Color.ValueMapping - Value Mapping for Reactivity
-- |
-- | Pure mathematical functions for mapping sampled values to output:
-- | - Sensitivity scaling
-- | - Smoothing (low-pass filter)
-- | - Range mapping (min/max)
-- | - Inversion
-- | - Depth normalization
-- |
-- | Source: ui/src/services/colorDepthReactivity.ts

module Lattice.Services.Color.ValueMapping
  ( -- * Types
    ValueMappingConfig, DepthMappingConfig
  , defaultValueMappingConfig, defaultDepthMappingConfig
    -- * Core Mapping
  , clamp01, applySensitivity, applyInversion, mapToRange, applySmoothing
    -- * Complete Mapping
  , mapValue, mapValueSimple
    -- * Depth Mapping
  , normalizeDepth, mapDepthValue
    -- * Motion Detection
  , pixelDifference, applyMotionThreshold, mapMotionValue
    -- * Gradient
  , gradientMagnitude, calculateGradient
    -- * Statistics
  , calculateVariance, calculateStdDev, calculateMean, findMin, findMax
  ) where

import Prelude
import Data.Array (foldl, length)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Math (abs, max, min, sqrt) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Configuration for value mapping.
type ValueMappingConfig =
  { sensitivity :: Number  -- Multiplier for raw value
  , smoothing :: Number    -- 0-1 (0 = no smoothing, 1 = full smoothing)
  , min :: Number          -- Output minimum
  , max :: Number          -- Output maximum
  , invert :: Boolean      -- Invert before mapping
  }

-- | Default value mapping configuration.
defaultValueMappingConfig :: ValueMappingConfig
defaultValueMappingConfig =
  { sensitivity: 1.0
  , smoothing: 0.0
  , min: 0.0
  , max: 1.0
  , invert: false
  }

-- | Depth mapping configuration.
type DepthMappingConfig =
  { nearPlane :: Number   -- Depth value considered "near"
  , farPlane :: Number    -- Depth value considered "far"
  , sensitivity :: Number
  , smoothing :: Number
  , min :: Number
  , max :: Number
  , invert :: Boolean
  }

-- | Default depth mapping configuration.
defaultDepthMappingConfig :: DepthMappingConfig
defaultDepthMappingConfig =
  { nearPlane: 0.0
  , farPlane: 1.0
  , sensitivity: 1.0
  , smoothing: 0.0
  , min: 0.0
  , max: 1.0
  , invert: false
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Core Mapping Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp a value to 0-1 range.
clamp01 :: Number -> Number
clamp01 x = Math.max 0.0 (Math.min 1.0 x)

-- | Apply sensitivity scaling to a raw value.
-- |
-- | Multiplies the value by sensitivity and clamps to 0-1.
applySensitivity :: Number -> Number -> Number
applySensitivity rawValue sensitivity = clamp01 (rawValue * sensitivity)

-- | Apply inversion if needed.
-- |
-- | If invert is true, returns 1 - value.
applyInversion :: Number -> Boolean -> Number
applyInversion value invert = if invert then 1.0 - value else value

-- | Map a 0-1 value to an output range.
mapToRange :: Number -> Number -> Number -> Number
mapToRange value minVal maxVal = minVal + value * (maxVal - minVal)

-- | Apply exponential smoothing (one-pole low-pass filter).
-- |
-- | output = previous * smoothing + current * (1 - smoothing)
-- |
-- | smoothing = 0: No smoothing (instant response)
-- | smoothing → 1: More smoothing (slower response)
applySmoothing :: Number -> Number -> Number -> Number
applySmoothing currentValue previousValue smoothing =
  if smoothing <= 0.0 then currentValue
  else previousValue * smoothing + currentValue * (1.0 - smoothing)

-- ────────────────────────────────────────────────────────────────────────────
-- Complete Value Mapping
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply complete value mapping pipeline.
-- |
-- | Pipeline:
-- | 1. Apply sensitivity
-- | 2. Clamp to 0-1
-- | 3. Invert if needed
-- | 4. Map to output range
-- | 5. Apply smoothing
mapValue :: Number -> ValueMappingConfig -> Maybe Number -> Number
mapValue rawValue config mPreviousValue =
  let -- Step 1: Apply sensitivity
      scaled = applySensitivity rawValue config.sensitivity

      -- Step 2: Invert if needed
      inverted = applyInversion scaled config.invert

      -- Step 3: Map to output range
      mapped = mapToRange inverted config.min config.max

      -- Step 4: Apply smoothing
  in case mPreviousValue of
       Nothing -> mapped
       Just prev -> applySmoothing mapped prev config.smoothing

-- | Map value without smoothing (no previous value).
mapValueSimple :: Number -> ValueMappingConfig -> Number
mapValueSimple rawValue config = mapValue rawValue config Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Depth Mapping
-- ────────────────────────────────────────────────────────────────────────────

-- | Normalize depth value to near/far range.
-- |
-- | Converts raw depth to 0-1 where:
-- | - 0 = near plane
-- | - 1 = far plane
normalizeDepth :: Number -> Number -> Number -> Number
normalizeDepth depthValue nearPlane farPlane =
  let range = farPlane - nearPlane
  in if range <= 0.0 then depthValue
     else clamp01 ((depthValue - nearPlane) / range)

-- | Apply complete depth mapping pipeline.
-- |
-- | Pipeline:
-- | 1. Normalize to near/far range
-- | 2. Apply sensitivity
-- | 3. Invert if needed
-- | 4. Map to output range
-- | 5. Apply smoothing
mapDepthValue :: Number -> DepthMappingConfig -> Maybe Number -> Number
mapDepthValue depthValue config mPreviousValue =
  let -- Step 1: Normalize to near/far range
      normalized = normalizeDepth depthValue config.nearPlane config.farPlane

      -- Step 2: Apply sensitivity
      scaled = applySensitivity normalized config.sensitivity

      -- Step 3: Invert if needed
      inverted = applyInversion scaled config.invert

      -- Step 4: Map to output range
      mapped = mapToRange inverted config.min config.max

      -- Step 5: Apply smoothing
  in case mPreviousValue of
       Nothing -> mapped
       Just prev -> applySmoothing mapped prev config.smoothing

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Detection Math
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate per-pixel color difference (0-1).
-- |
-- | Returns average of RGB channel differences.
pixelDifference :: Number -> Number -> Number -> Number -> Number -> Number -> Number
pixelDifference r1 g1 b1 r2 g2 b2 =
  let dr = Math.abs (r1 - r2)
      dg = Math.abs (g1 - g2)
      db = Math.abs (b1 - b2)
  in (dr + dg + db) / 3.0

-- | Apply threshold to motion value.
-- |
-- | Returns 0 if below threshold, otherwise returns the value.
applyMotionThreshold :: Number -> Number -> Number
applyMotionThreshold difference threshold =
  if difference > threshold then difference else 0.0

-- | Map motion value to output.
-- |
-- | Takes accumulated motion (0-1) and maps to output range.
mapMotionValue :: Number -> Number -> Number -> Number -> Maybe Number -> Number -> Number
mapMotionValue motionValue sensitivity minVal maxVal mPreviousValue smoothing =
  let -- Apply sensitivity
      scaled = clamp01 (motionValue * sensitivity)

      -- Map to output range
      mapped = mapToRange scaled minVal maxVal

      -- Apply smoothing
  in case mPreviousValue of
       Nothing -> mapped
       Just prev -> applySmoothing mapped prev smoothing

-- ────────────────────────────────────────────────────────────────────────────
-- Gradient Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate gradient magnitude from dx and dy.
gradientMagnitude :: Number -> Number -> Number
gradientMagnitude dx dy = Math.sqrt (dx * dx + dy * dy)

-- | Sobel-like gradient calculation (given neighbor values).
-- |
-- | dx = right - left
-- | dy = bottom - top
calculateGradient :: Number -> Number -> Number -> Number -> Number
calculateGradient left right top bottom =
  let dx = right - left
      dy = bottom - top
  in gradientMagnitude dx dy

-- ────────────────────────────────────────────────────────────────────────────
-- Statistics
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate variance of an array of values.
calculateVariance :: Array Number -> Number
calculateVariance values =
  let n = length values
  in if n == 0 then 0.0
     else
       let sum = foldl (+) 0.0 values
           mean = sum / toNumber n
           squaredDiffs = map (\v -> (v - mean) * (v - mean)) values
           sumSquaredDiffs = foldl (+) 0.0 squaredDiffs
       in sumSquaredDiffs / toNumber n

-- | Calculate standard deviation.
calculateStdDev :: Array Number -> Number
calculateStdDev values = Math.sqrt (calculateVariance values)

-- | Calculate mean of values.
calculateMean :: Array Number -> Number
calculateMean values =
  let n = length values
  in if n == 0 then 0.0
     else foldl (+) 0.0 values / toNumber n

-- | Find minimum value in array.
findMin :: Array Number -> Number
findMin values = foldl Math.min (1.0 / 0.0) values  -- Start with infinity

-- | Find maximum value in array.
findMax :: Array Number -> Number
findMax values = foldl Math.max (-1.0 / 0.0) values  -- Start with -infinity
