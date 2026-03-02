{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Services.Color.ValueMapping
Description : Value Mapping for Reactivity
Copyright   : (c) Lattice, 2026
License     : MIT

Pure mathematical functions for mapping sampled values to output:
- Sensitivity scaling
- Smoothing (low-pass filter)
- Range mapping (min/max)
- Inversion
- Depth normalization

Source: ui/src/services/colorDepthReactivity.ts
-}

module Lattice.Services.Color.ValueMapping
  ( -- * Types
    ValueMappingConfig(..), DepthMappingConfig(..)
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

import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Configuration for value mapping.
data ValueMappingConfig = ValueMappingConfig
  { vmcSensitivity :: Double  -- ^ Multiplier for raw value
  , vmcSmoothing :: Double    -- ^ 0-1 (0 = no smoothing, 1 = full smoothing)
  , vmcMin :: Double          -- ^ Output minimum
  , vmcMax :: Double          -- ^ Output maximum
  , vmcInvert :: Bool         -- ^ Invert before mapping
  } deriving (Eq, Show)

-- | Default value mapping configuration.
defaultValueMappingConfig :: ValueMappingConfig
defaultValueMappingConfig = ValueMappingConfig 1 0 0 1 False

-- | Depth mapping configuration.
data DepthMappingConfig = DepthMappingConfig
  { dmcNearPlane :: Double   -- ^ Depth value considered "near"
  , dmcFarPlane :: Double    -- ^ Depth value considered "far"
  , dmcSensitivity :: Double
  , dmcSmoothing :: Double
  , dmcMin :: Double
  , dmcMax :: Double
  , dmcInvert :: Bool
  } deriving (Eq, Show)

-- | Default depth mapping configuration.
defaultDepthMappingConfig :: DepthMappingConfig
defaultDepthMappingConfig = DepthMappingConfig 0 1 1 0 0 1 False

--------------------------------------------------------------------------------
-- Core Mapping Functions
--------------------------------------------------------------------------------

-- | Clamp a value to 0-1 range.
clamp01 :: Double -> Double
clamp01 x = max 0 (min 1 x)

-- | Apply sensitivity scaling to a raw value.
--
--   Multiplies the value by sensitivity and clamps to 0-1.
applySensitivity :: Double -> Double -> Double
applySensitivity rawValue sensitivity = clamp01 (rawValue * sensitivity)

-- | Apply inversion if needed.
--
--   If invert is true, returns 1 - value.
applyInversion :: Double -> Bool -> Double
applyInversion value invert = if invert then 1 - value else value

-- | Map a 0-1 value to an output range.
mapToRange :: Double -> Double -> Double -> Double
mapToRange value minVal maxVal = minVal + value * (maxVal - minVal)

-- | Apply exponential smoothing (one-pole low-pass filter).
--
--   output = previous * smoothing + current * (1 - smoothing)
--
--   smoothing = 0: No smoothing (instant response)
--   smoothing → 1: More smoothing (slower response)
applySmoothing :: Double -> Double -> Double -> Double
applySmoothing currentValue previousValue smoothing
  | smoothing <= 0 = currentValue
  | otherwise = previousValue * smoothing + currentValue * (1 - smoothing)

--------------------------------------------------------------------------------
-- Complete Value Mapping
--------------------------------------------------------------------------------

-- | Apply complete value mapping pipeline.
--
--   Pipeline:
--   1. Apply sensitivity
--   2. Clamp to 0-1
--   3. Invert if needed
--   4. Map to output range
--   5. Apply smoothing
mapValue :: Double -> ValueMappingConfig -> Maybe Double -> Double
mapValue rawValue config mPreviousValue =
  let -- Step 1: Apply sensitivity
      scaled = applySensitivity rawValue (vmcSensitivity config)

      -- Step 2: Invert if needed
      inverted = applyInversion scaled (vmcInvert config)

      -- Step 3: Map to output range
      mapped = mapToRange inverted (vmcMin config) (vmcMax config)

      -- Step 4: Apply smoothing
  in case mPreviousValue of
       Nothing -> mapped
       Just prev -> applySmoothing mapped prev (vmcSmoothing config)

-- | Map value without smoothing (no previous value).
mapValueSimple :: Double -> ValueMappingConfig -> Double
mapValueSimple rawValue config = mapValue rawValue config Nothing

--------------------------------------------------------------------------------
-- Depth Mapping
--------------------------------------------------------------------------------

-- | Normalize depth value to near/far range.
--
--   Converts raw depth to 0-1 where:
--   - 0 = near plane
--   - 1 = far plane
normalizeDepth :: Double -> Double -> Double -> Double
normalizeDepth depthValue nearPlane farPlane =
  let range = farPlane - nearPlane
  in if range <= 0 then depthValue
     else clamp01 ((depthValue - nearPlane) / range)

-- | Apply complete depth mapping pipeline.
--
--   Pipeline:
--   1. Normalize to near/far range
--   2. Apply sensitivity
--   3. Invert if needed
--   4. Map to output range
--   5. Apply smoothing
mapDepthValue :: Double -> DepthMappingConfig -> Maybe Double -> Double
mapDepthValue depthValue config mPreviousValue =
  let -- Step 1: Normalize to near/far range
      normalized = normalizeDepth depthValue (dmcNearPlane config) (dmcFarPlane config)

      -- Step 2: Apply sensitivity
      scaled = applySensitivity normalized (dmcSensitivity config)

      -- Step 3: Invert if needed
      inverted = applyInversion scaled (dmcInvert config)

      -- Step 4: Map to output range
      mapped = mapToRange inverted (dmcMin config) (dmcMax config)

      -- Step 5: Apply smoothing
  in case mPreviousValue of
       Nothing -> mapped
       Just prev -> applySmoothing mapped prev (dmcSmoothing config)

--------------------------------------------------------------------------------
-- Motion Detection Math
--------------------------------------------------------------------------------

-- | Calculate per-pixel color difference (0-1).
--
--   Returns average of RGB channel differences.
pixelDifference :: Double -> Double -> Double -> Double -> Double -> Double -> Double
pixelDifference r1 g1 b1 r2 g2 b2 =
  let dr = abs (r1 - r2)
      dg = abs (g1 - g2)
      db = abs (b1 - b2)
  in (dr + dg + db) / 3

-- | Apply threshold to motion value.
--
--   Returns 0 if below threshold, otherwise returns the value.
applyMotionThreshold :: Double -> Double -> Double
applyMotionThreshold difference threshold =
  if difference > threshold then difference else 0

-- | Map motion value to output.
--
--   Takes accumulated motion (0-1) and maps to output range.
mapMotionValue :: Double -> Double -> Double -> Double -> Maybe Double -> Double -> Double
mapMotionValue motionValue sensitivity minVal maxVal mPreviousValue smoothing =
  let -- Apply sensitivity
      scaled = clamp01 (motionValue * sensitivity)

      -- Map to output range
      mapped = mapToRange scaled minVal maxVal

      -- Apply smoothing
  in case mPreviousValue of
       Nothing -> mapped
       Just prev -> applySmoothing mapped prev smoothing

--------------------------------------------------------------------------------
-- Gradient Calculation
--------------------------------------------------------------------------------

-- | Calculate gradient magnitude from dx and dy.
gradientMagnitude :: Double -> Double -> Double
gradientMagnitude dx dy = sqrt (dx * dx + dy * dy)

-- | Sobel-like gradient calculation (given neighbor values).
--
--   dx = right - left
--   dy = bottom - top
calculateGradient :: Double -> Double -> Double -> Double -> Double
calculateGradient left right top bottom =
  let dx = right - left
      dy = bottom - top
  in gradientMagnitude dx dy

--------------------------------------------------------------------------------
-- Statistics
--------------------------------------------------------------------------------

-- | Calculate variance of a vector of values.
calculateVariance :: Vector Double -> Double
calculateVariance values
  | V.null values = 0
  | otherwise =
      let n = fromIntegral (V.length values)
          sumVals = V.sum values
          mean = sumVals / n
          squaredDiffs = V.map (\v -> (v - mean) * (v - mean)) values
      in V.sum squaredDiffs / n

-- | Calculate standard deviation.
calculateStdDev :: Vector Double -> Double
calculateStdDev values = sqrt (calculateVariance values)

-- | Calculate mean of values.
calculateMean :: Vector Double -> Double
calculateMean values
  | V.null values = 0
  | otherwise = V.sum values / fromIntegral (V.length values)

-- | Find minimum value in vector.
findMin :: Vector Double -> Double
findMin values
  | V.null values = 1/0  -- Infinity
  | otherwise = V.minimum values

-- | Find maximum value in vector.
findMax :: Vector Double -> Double
findMax values
  | V.null values = -1/0  -- -Infinity
  | otherwise = V.maximum values
