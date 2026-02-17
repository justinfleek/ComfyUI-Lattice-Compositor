{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Expressions.JitterExpressions
Description : Noise and jitter functions
Copyright   : (c) Lattice, 2026
License     : MIT

Expression functions for adding noise/randomness:
- jitter: Simple noise based on sine waves
- temporalJitter: Smooth noise with Catmull-Rom interpolation

Source: ui/src/services/expressions/jitterExpressions.ts
-}

module Lattice.Services.Expressions.JitterExpressions
  ( -- * Constants
    maxOctaves, defaultFrequency, defaultAmplitude
    -- * Simple Jitter
  , jitter, jitterVec
  , jitterScalar, jitterVector
    -- * Temporal Jitter
  , temporalJitter, temporalJitterVec
  , temporalJitterScalar, temporalJitterVector
    -- * Noise Functions
  , sineNoise, smoothNoise
    -- * Helpers
  , deterministicRand, catmullRom
  , clampOctaves, safeFrequency
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Maximum octaves to prevent excessive computation
maxOctaves :: Int
maxOctaves = 10

-- | Default frequency
defaultFrequency :: Double
defaultFrequency = 5.0

-- | Default amplitude
defaultAmplitude :: Double
defaultAmplitude = 50.0

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Clamp octaves to valid range [1, maxOctaves]
clampOctaves :: Double -> Int
clampOctaves octaves
  | isNaN octaves || isInfinite octaves || octaves < 1 = 1
  | octaves > fromIntegral maxOctaves = maxOctaves
  | otherwise = floor octaves

-- | Ensure frequency is valid
safeFrequency :: Double -> Double
safeFrequency freq
  | isNaN freq || isInfinite freq || freq <= 0 = defaultFrequency
  | otherwise = freq

--------------------------------------------------------------------------------
-- Simple Noise (Sine-based)
--------------------------------------------------------------------------------

-- | Generate noise value from sine waves with multiple octaves.
sineNoise :: Double -> Double -> Double -> Int -> Double -> Double
sineNoise seed t frequency octaves ampMultiplier =
  let go 0 result _ _ = result
      go n result amp freq =
        let phase = t * frequency * freq * pi * 2 + seed * 1000
            noise1 = amp * sin phase
            noise2 = amp * 0.5 * sin (phase * 1.5 - seed * 500)
        in go (n - 1) (result + noise1 + noise2) (amp * ampMultiplier) (freq * 2)
      result = go octaves 0 1 1
      denominator = 1 + (fromIntegral octaves - 1) * ampMultiplier
  in if isNaN denominator || isInfinite denominator || denominator == 0
     then result
     else result / denominator

--------------------------------------------------------------------------------
-- Jitter Function
--------------------------------------------------------------------------------

-- | Jitter: Add noise to a scalar value
jitterScalar :: Double -> Double -> Double -> Double -> Int -> Double -> Double
jitterScalar value t frequency amplitude octaves ampMultiplier =
  let noise = sineNoise 0 t frequency octaves ampMultiplier
  in value + noise * amplitude

-- | Jitter: Add noise to a vector value.
jitterVector :: Vector Double -> Double -> Double -> Double -> Int -> Double -> Vector Double
jitterVector values t frequency amplitude octaves ampMultiplier =
  V.imap (\i v ->
    let noise = sineNoise (fromIntegral i) t frequency octaves ampMultiplier
    in v + noise * amplitude) values

--------------------------------------------------------------------------------
-- Smooth Noise (Catmull-Rom Interpolated)
--------------------------------------------------------------------------------

-- | Deterministic random from integer index and seed
deterministicRand :: Double -> Double -> Double
deterministicRand n seed =
  let x = sin (n * 12.9898 + seed * 78.233) * 43758.5453
  in x - fromIntegral (floor x :: Int)

-- | Catmull-Rom spline interpolation between 4 values
catmullRom :: Double -> Double -> Double -> Double -> Double -> Double
catmullRom v0 v1 v2 v3 t =
  let t2 = t * t
      t3 = t2 * t
  in 0.5 * (2 * v1 +
            (-v0 + v2) * t +
            (2 * v0 - 5 * v1 + 4 * v2 - v3) * t2 +
            (-v0 + 3 * v1 - 3 * v2 + v3) * t3)

-- | Smooth noise with temporal correlation using Catmull-Rom interpolation
smoothNoise :: Double -> Double -> Double -> Double
smoothNoise seed t frequency =
  let period = 1 / frequency
      index = fromIntegral (floor (t / period) :: Int)
      frac = t / period - index
      v0 = deterministicRand (index - 1) seed * 2 - 1
      v1 = deterministicRand index seed * 2 - 1
      v2 = deterministicRand (index + 1) seed * 2 - 1
      v3 = deterministicRand (index + 2) seed * 2 - 1
  in catmullRom v0 v1 v2 v3 frac

--------------------------------------------------------------------------------
-- Temporal Jitter Function
--------------------------------------------------------------------------------

-- | Temporal jitter: Smooth noise on a scalar value
temporalJitterScalar :: Double -> Double -> Double -> Double -> Int -> Double
temporalJitterScalar value t frequency amplitude octaves =
  let go 0 result _ _ = result
      go n result amp freq =
        let noise = smoothNoise (fromIntegral n * 100) (t * freq / frequency) frequency
        in go (n - 1) (result + noise * amp) (amp * 0.5) (freq * 2)
      result = go octaves 0 amplitude frequency
  in value + result

-- | Temporal jitter: Smooth noise on a vector value
temporalJitterVector :: Vector Double -> Double -> Double -> Double -> Int -> Vector Double
temporalJitterVector values t frequency amplitude octaves =
  V.imap (\idx v ->
    let go 0 result _ _ = result
        go n result amp freq =
          let seed = fromIntegral idx * 100 + fromIntegral n * 1000
              noise = smoothNoise seed (t * freq / frequency) frequency
          in go (n - 1) (result + noise * amp) (amp * 0.5) (freq * 2)
        result = go octaves 0 amplitude frequency
    in v + result) values

--------------------------------------------------------------------------------
-- Main API
--------------------------------------------------------------------------------

-- | Jitter expression for scalar values
jitter :: Double -> Double -> Double -> Double -> Double -> Double -> Double
jitter value t frequency amplitude octaves ampMultiplier =
  let safeOctaves = clampOctaves octaves
      safeFreq = safeFrequency frequency
  in jitterScalar value t safeFreq amplitude safeOctaves ampMultiplier

-- | Jitter expression for vector values
jitterVec :: Vector Double -> Double -> Double -> Double -> Double -> Double -> Vector Double
jitterVec values t frequency amplitude octaves ampMultiplier =
  let safeOctaves = clampOctaves octaves
      safeFreq = safeFrequency frequency
  in jitterVector values t safeFreq amplitude safeOctaves ampMultiplier

-- | Temporal jitter expression for scalar values
temporalJitter :: Double -> Double -> Double -> Double -> Double -> Double
temporalJitter value t frequency amplitude octaves =
  let safeOctaves = clampOctaves octaves
      safeFreq = safeFrequency frequency
  in temporalJitterScalar value t safeFreq amplitude safeOctaves

-- | Temporal jitter expression for vector values
temporalJitterVec :: Vector Double -> Double -> Double -> Double -> Double -> Vector Double
temporalJitterVec values t frequency amplitude octaves =
  let safeOctaves = clampOctaves octaves
      safeFreq = safeFrequency frequency
  in temporalJitterVector values t safeFreq amplitude safeOctaves
