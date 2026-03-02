-- |
-- Module      : Lattice.Services.JitterExpressions
-- Description : Pure jitter expression functions for adding deterministic noise
-- 
-- Migrated from ui/src/services/expressions/jitterExpressions.ts
-- Pure deterministic noise functions (uses sine waves, not random)
-- Note: These are pure because they use deterministic hash functions
--

module Lattice.Services.JitterExpressions
  ( -- Jitter expressions
    jitter
  , temporalJitter
  -- Types
  , JitterParams(..)
  ) where

import Lattice.Utils.NumericSafety (isFinite)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Parameters for jitter expressions
-- Simplified from JitterExpressionContext - only what's needed for pure calculations
data JitterParams = JitterParams
  { jitterParamsTime :: Double          -- Current time
  , jitterParamsValue :: [Double]       -- Current value (as array)
  } deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                       // deterministic // noise // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Simple deterministic noise using sine waves
-- Pure function: same inputs → same outputs
-- Uses multiple sine waves with different frequencies for pseudo-noise
noise :: Int -> Double -> Int -> Double -> Double -> Double
noise seed t octaves amplitudeMultiplier frequency =
  let octaves' = max 1 (min 10 octaves)  -- Cap at 1-10
      noiseOctave i amp freq' =
        amp * sin (t * frequency * freq' * 2 * pi + fromIntegral seed * 1000) +
        amp * 0.5 * sin (t * frequency * freq' * 2 * pi * 1.5 + fromIntegral seed * 500)
      octaveResults = [noiseOctave i (amplitudeMultiplier ** fromIntegral i) (2 ** fromIntegral i) | i <- [0 .. octaves' - 1]]
      sumResult = sum octaveResults
      denominator = 1 + fromIntegral (octaves' - 1) * amplitudeMultiplier
  in if denominator > 0 && isFinite denominator
       then sumResult / denominator
       else sumResult

-- | Smooth deterministic noise with temporal correlation
-- Pure function: same inputs → same outputs
-- Uses Catmull-Rom interpolation between deterministic random values
smoothNoise :: Int -> Double -> Double -> Double
smoothNoise seed t frequency =
  let period = 1 / frequency
      index = floor (t / period) :: Int
      frac = t / period - fromIntegral index
      -- Deterministic random value generator
      rand n =
        let x = sin (n * 12.9898 + fromIntegral seed * 78.233) * 43758.5453
        in x - fromIntegral (floor x)
      -- Get surrounding values
      v0 = rand (fromIntegral index - 1) * 2 - 1
      v1 = rand (fromIntegral index) * 2 - 1
      v2 = rand (fromIntegral index + 1) * 2 - 1
      v3 = rand (fromIntegral index + 2) * 2 - 1
      -- Catmull-Rom interpolation
      t2 = frac * frac
      t3 = t2 * frac
  in 0.5 * (2 * v1 +
            (-v0 + v2) * frac +
            (2 * v0 - 5 * v1 + 4 * v2 - v3) * t2 +
            (-v0 + 3 * v1 - 3 * v2 + v3) * t3)

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // jitter // expressions
-- ════════════════════════════════════════════════════════════════════════════

-- | Jitter expression
-- Pure function: same inputs → same outputs
-- Adds deterministic noise to value
jitter ::
  JitterParams ->
  Double ->  -- frequency (default 5)
  Double ->  -- amplitude (default 50)
  Int ->     -- octaves (default 1)
  Double ->  -- amplitudeMultiplier (default 0.5)
  Maybe Double ->  -- optional time override
  [Double]
jitter params frequency amplitude octaves amplitudeMultiplier maybeTime =
  let t = maybe (jitterParamsTime params) id maybeTime
      valueArr = jitterParamsValue params
      safeFrequency = if isFinite frequency && frequency > 0 then frequency else 5
      safeAmplitude = if isFinite amplitude then amplitude else 50
      safeOctaves = max 1 (min 10 octaves)
      safeMultiplier = if isFinite amplitudeMultiplier then amplitudeMultiplier else 0.5
      -- Apply noise to each component with different seed
      applyNoise i v = v + noise i t safeOctaves safeMultiplier safeFrequency * safeAmplitude
  in zipWith applyNoise [0 ..] valueArr

-- | Smooth jitter with temporal correlation
-- Pure function: same inputs → same outputs
-- Uses interpolated noise for smoother results
temporalJitter ::
  JitterParams ->
  Double ->  -- frequency (default 5)
  Double ->  -- amplitude (default 50)
  Int ->     -- octaves (default 1)
  Maybe Double ->  -- optional time override
  [Double]
temporalJitter params frequency amplitude octaves maybeTime =
  let t = maybe (jitterParamsTime params) id maybeTime
      valueArr = jitterParamsValue params
      safeFrequency = if isFinite frequency && frequency > 0 then frequency else 5
      safeAmplitude = if isFinite amplitude then amplitude else 50
      safeOctaves = max 1 (min 10 octaves)
      -- Apply smooth noise to each component
      applySmoothNoise idx v =
        let octaveSum = sum [smoothNoise (idx * 100 + i * 1000) (t * freq / safeFrequency) safeFrequency * amp
                            | i <- [0 .. safeOctaves - 1]
                            , let freq = safeFrequency * (2 ** fromIntegral i)
                            , let amp = safeAmplitude * (0.5 ** fromIntegral i)]
        in v + octaveSum
  in zipWith applySmoothNoise [0 ..] valueArr
