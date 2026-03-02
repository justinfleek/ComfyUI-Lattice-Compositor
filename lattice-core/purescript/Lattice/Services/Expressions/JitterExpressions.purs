-- | Lattice.Services.Expressions.JitterExpressions - Noise and jitter functions
-- |
-- | Expression functions for adding noise/randomness:
-- | - jitter: Simple noise based on sine waves
-- | - temporalJitter: Smooth noise with Catmull-Rom interpolation
-- |
-- | Source: ui/src/services/expressions/jitterExpressions.ts

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

import Prelude
import Data.Array (mapWithIndex)
import Data.Int (floor, toNumber)
import Global (isNaN, isFinite) as Global
import Math (pi, sin) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Maximum octaves to prevent excessive computation
maxOctaves :: Int
maxOctaves = 10

-- | Default frequency
defaultFrequency :: Number
defaultFrequency = 5.0

-- | Default amplitude
defaultAmplitude :: Number
defaultAmplitude = 50.0

-- ────────────────────────────────────────────────────────────────────────────
-- Helper Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp octaves to valid range [1, maxOctaves]
clampOctaves :: Number -> Int
clampOctaves octaves
  | Global.isNaN octaves || not (Global.isFinite octaves) || octaves < 1.0 = 1
  | octaves > toNumber maxOctaves = maxOctaves
  | otherwise = floor octaves

-- | Ensure frequency is valid
safeFrequency :: Number -> Number
safeFrequency freq
  | Global.isNaN freq || not (Global.isFinite freq) || freq <= 0.0 = defaultFrequency
  | otherwise = freq

-- ────────────────────────────────────────────────────────────────────────────
-- Simple Noise (Sine-based)
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate noise value from sine waves with multiple octaves.
sineNoise :: Number -> Number -> Number -> Int -> Number -> Number
sineNoise seed t frequency octaves ampMultiplier =
  let go :: Int -> Number -> Number -> Number -> Number
      go 0 result _ _ = result
      go n result amp freq =
        let phase = t * frequency * freq * Math.pi * 2.0 + seed * 1000.0
            noise1 = amp * Math.sin phase
            noise2 = amp * 0.5 * Math.sin (phase * 1.5 - seed * 500.0)
        in go (n - 1) (result + noise1 + noise2) (amp * ampMultiplier) (freq * 2.0)
      result = go octaves 0.0 1.0 1.0
      denominator = 1.0 + (toNumber octaves - 1.0) * ampMultiplier
  in if Global.isNaN denominator || not (Global.isFinite denominator) || denominator == 0.0
     then result
     else result / denominator

-- ────────────────────────────────────────────────────────────────────────────
-- Jitter Function
-- ────────────────────────────────────────────────────────────────────────────

-- | Jitter: Add noise to a scalar value
jitterScalar :: Number -> Number -> Number -> Number -> Int -> Number -> Number
jitterScalar value t frequency amplitude octaves ampMultiplier =
  let noise = sineNoise 0.0 t frequency octaves ampMultiplier
  in value + noise * amplitude

-- | Jitter: Add noise to a vector value.
jitterVector :: Array Number -> Number -> Number -> Number -> Int -> Number -> Array Number
jitterVector values t frequency amplitude octaves ampMultiplier =
  mapWithIndex (\i v ->
    let noise = sineNoise (toNumber i) t frequency octaves ampMultiplier
    in v + noise * amplitude) values

-- ────────────────────────────────────────────────────────────────────────────
-- Smooth Noise (Catmull-Rom Interpolated)
-- ────────────────────────────────────────────────────────────────────────────

-- | Deterministic random from integer index and seed
deterministicRand :: Number -> Number -> Number
deterministicRand n seed =
  let x = Math.sin (n * 12.9898 + seed * 78.233) * 43758.5453
  in x - toNumber (floor x)

-- | Catmull-Rom spline interpolation between 4 values
catmullRom :: Number -> Number -> Number -> Number -> Number -> Number
catmullRom v0 v1 v2 v3 t =
  let t2 = t * t
      t3 = t2 * t
  in 0.5 * (2.0 * v1 +
            (-v0 + v2) * t +
            (2.0 * v0 - 5.0 * v1 + 4.0 * v2 - v3) * t2 +
            (-v0 + 3.0 * v1 - 3.0 * v2 + v3) * t3)

-- | Smooth noise with temporal correlation using Catmull-Rom interpolation
smoothNoise :: Number -> Number -> Number -> Number
smoothNoise seed t frequency =
  let period = 1.0 / frequency
      index = toNumber (floor (t / period))
      frac = t / period - index
      v0 = deterministicRand (index - 1.0) seed * 2.0 - 1.0
      v1 = deterministicRand index seed * 2.0 - 1.0
      v2 = deterministicRand (index + 1.0) seed * 2.0 - 1.0
      v3 = deterministicRand (index + 2.0) seed * 2.0 - 1.0
  in catmullRom v0 v1 v2 v3 frac

-- ────────────────────────────────────────────────────────────────────────────
-- Temporal Jitter Function
-- ────────────────────────────────────────────────────────────────────────────

-- | Temporal jitter: Smooth noise on a scalar value
temporalJitterScalar :: Number -> Number -> Number -> Number -> Int -> Number
temporalJitterScalar value t frequency amplitude octaves =
  let go :: Int -> Number -> Number -> Number -> Number
      go 0 result _ _ = result
      go n result amp freq =
        let noise = smoothNoise (toNumber n * 100.0) (t * freq / frequency) frequency
        in go (n - 1) (result + noise * amp) (amp * 0.5) (freq * 2.0)
      result = go octaves 0.0 amplitude frequency
  in value + result

-- | Temporal jitter: Smooth noise on a vector value
temporalJitterVector :: Array Number -> Number -> Number -> Number -> Int -> Array Number
temporalJitterVector values t frequency amplitude octaves =
  mapWithIndex (\idx v ->
    let go :: Int -> Number -> Number -> Number -> Number
        go 0 result _ _ = result
        go n result amp freq =
          let seed = toNumber idx * 100.0 + toNumber n * 1000.0
              noise = smoothNoise seed (t * freq / frequency) frequency
          in go (n - 1) (result + noise * amp) (amp * 0.5) (freq * 2.0)
        result = go octaves 0.0 amplitude frequency
    in v + result) values

-- ────────────────────────────────────────────────────────────────────────────
-- Main API
-- ────────────────────────────────────────────────────────────────────────────

-- | Jitter expression for scalar values
jitter :: Number -> Number -> Number -> Number -> Number -> Number -> Number
jitter value t frequency amplitude octaves ampMultiplier =
  let safeOctaves = clampOctaves octaves
      safeFreq = safeFrequency frequency
  in jitterScalar value t safeFreq amplitude safeOctaves ampMultiplier

-- | Jitter expression for vector values
jitterVec :: Array Number -> Number -> Number -> Number -> Number -> Number -> Array Number
jitterVec values t frequency amplitude octaves ampMultiplier =
  let safeOctaves = clampOctaves octaves
      safeFreq = safeFrequency frequency
  in jitterVector values t safeFreq amplitude safeOctaves ampMultiplier

-- | Temporal jitter expression for scalar values
temporalJitter :: Number -> Number -> Number -> Number -> Number -> Number
temporalJitter value t frequency amplitude octaves =
  let safeOctaves = clampOctaves octaves
      safeFreq = safeFrequency frequency
  in temporalJitterScalar value t safeFreq amplitude safeOctaves

-- | Temporal jitter expression for vector values
temporalJitterVec :: Array Number -> Number -> Number -> Number -> Number -> Array Number
temporalJitterVec values t frequency amplitude octaves =
  let safeOctaves = clampOctaves octaves
      safeFreq = safeFrequency frequency
  in temporalJitterVector values t safeFreq amplitude safeOctaves
