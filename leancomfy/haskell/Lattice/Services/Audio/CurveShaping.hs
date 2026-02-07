{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Audio.CurveShaping
Description : Audio Curve Shaping Functions
Copyright   : (c) Lattice, 2026
License     : MIT

Pure mathematical functions for shaping audio-reactive values:
- Value curve shaping (exponential, logarithmic, smoothstep, bounce)
- Amplitude curves (power curves for noise gate/compressor)
- Threshold gating

Source: ui/src/services/audioReactiveMapping.ts (applyCurve)
-}

module Lattice.Services.Audio.CurveShaping
  ( -- * Types
    CurveType(..)
    -- * Clamping
  , clamp01
    -- * Curve Functions
  , exponentialCurve, logarithmicCurve, smoothstepCurve, bounceCurve
  , applyCurve
    -- * Amplitude Curves
  , applyAmplitudeCurve
    -- * Threshold/Gate
  , applyThreshold, applyThresholdSoftKnee
    -- * Combined Processing
  , processAudioValue
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Curve type for value shaping
data CurveType
  = Linear
  | Exponential
  | Logarithmic
  | Smoothstep
  | Bounce
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Clamping
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1] range
clamp01 :: Double -> Double
clamp01 v = max 0 (min 1 v)

--------------------------------------------------------------------------------
-- Curve Shaping Functions
--------------------------------------------------------------------------------

-- | Apply exponential curve (square).
--
--   Creates more dynamic response - low values become lower,
--   high values relatively unchanged.
--   Output: x²
exponentialCurve :: Double -> Double
exponentialCurve value =
  let clamped = clamp01 value
  in clamped * clamped

-- | Apply logarithmic curve (square root).
--
--   Creates compressed response - boosts low values,
--   compresses high values.
--   Output: √x
logarithmicCurve :: Double -> Double
logarithmicCurve value =
  let clamped = clamp01 value
  in sqrt clamped

-- | Apply smoothstep curve.
--
--   S-curve with smooth acceleration and deceleration.
--   Output: 3x² - 2x³
smoothstepCurve :: Double -> Double
smoothstepCurve value =
  let clamped = clamp01 value
  in clamped * clamped * (3 - 2 * clamped)

-- | Apply bounce curve.
--
--   Overshoot and bounce back effect.
--   Two-phase quadratic for snappy response.
bounceCurve :: Double -> Double
bounceCurve value =
  let clamped = clamp01 value
  in if clamped < 0.5
     then 2 * clamped * clamped
     else let t = clamped - 0.5
              overshoot = 1 - 2 * t
          in 0.5 + 0.5 * (1 - overshoot * overshoot)

-- | Apply curve shaping to a value.
--
--   Maps input value [0,1] through selected curve function.
--   All curves preserve the [0,1] range.
applyCurve :: Double -> CurveType -> Double
applyCurve value curve = case curve of
  Linear -> clamp01 value
  Exponential -> exponentialCurve value
  Logarithmic -> logarithmicCurve value
  Smoothstep -> smoothstepCurve value
  Bounce -> bounceCurve value

--------------------------------------------------------------------------------
-- Amplitude Curves (Power Law)
--------------------------------------------------------------------------------

-- | Apply amplitude curve (power law).
--
--   amplitudeCurve > 1.0: Expander (emphasize loud, suppress quiet)
--   amplitudeCurve = 1.0: Linear (no change)
--   amplitudeCurve < 1.0: Compressor (boost quiet, limit loud)
--
--   This is the core of ATI_AudioReactive style dynamics processing.
applyAmplitudeCurve :: Double -> Double -> Double
applyAmplitudeCurve value power
  | power == 1 = value
  | otherwise = max 0 value ** power

--------------------------------------------------------------------------------
-- Threshold / Noise Gate
--------------------------------------------------------------------------------

-- | Apply threshold (noise gate).
--
--   Values below threshold become 0.
--   Values at or above threshold pass through unchanged.
applyThreshold :: Double -> Double -> Double
applyThreshold value threshold
  | value < threshold = 0
  | otherwise = value

-- | Apply threshold with soft knee.
--
--   Soft knee provides gradual transition around threshold
--   instead of hard cutoff.
applyThresholdSoftKnee :: Double -> Double -> Double -> Double
applyThresholdSoftKnee value threshold knee
  | knee <= 0 = applyThreshold value threshold
  | value < kneeStart = 0
  | value > kneeEnd = value
  | otherwise =
      let t = (value - kneeStart) / knee
          curved = t * t
      in value * curved
  where
    kneeStart = threshold - knee / 2
    kneeEnd = threshold + knee / 2

--------------------------------------------------------------------------------
-- Combined Processing
--------------------------------------------------------------------------------

-- | Apply full audio value processing chain.
--
--   1. Threshold (noise gate)
--   2. Amplitude curve (dynamics)
--   3. Value curve (shaping)
--   4. Inversion (optional)
--
--   This matches the processing order in audioReactiveMapping.ts
processAudioValue :: Double -> Double -> Double -> CurveType -> Bool -> Double
processAudioValue value threshold amplitudeCurve curve invert =
  let v1 = applyThreshold value threshold
      v2 = applyAmplitudeCurve v1 amplitudeCurve
      v3 = applyCurve v2 curve
  in if invert then 1 - v3 else v3
