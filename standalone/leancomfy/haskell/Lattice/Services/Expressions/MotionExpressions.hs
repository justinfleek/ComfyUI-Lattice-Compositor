{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Expressions.MotionExpressions
Description : Motion physics functions
Copyright   : (c) Lattice, 2026
License     : MIT

Core physics calculations for momentum-based animations:
- inertiaOscillation: Damped sine wave oscillation
- bouncePhysics: Bouncing settle with elasticity
- elasticOscillation: Spring-like elastic motion

Source: ui/src/services/expressions/motionExpressions.ts
-}

module Lattice.Services.Expressions.MotionExpressions
  ( -- * Constants
    defaultAmplitude, defaultFrequency, defaultDecay
  , defaultElasticity, defaultGravity, defaultPeriod
  , maxBounces
    -- * Inertia
  , inertiaOscillation
  , inertiaScalar, inertiaVector
  , inertia, inertiaVec
    -- * Bounce
  , bouncePhysics
  , bounceScalar, bounceVector
  , bounce, bounceVec
    -- * Elastic
  , elasticOscillation
  , elasticScalar, elasticVector
  , elastic, elasticVec
    -- * Helpers
  , safeAmplitude, safeFrequency, safeDecay
  , safeElasticity, safeGravity, safePeriod
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Default inertia amplitude
defaultAmplitude :: Double
defaultAmplitude = 0.1

-- | Default inertia frequency
defaultFrequency :: Double
defaultFrequency = 2.0

-- | Default inertia decay
defaultDecay :: Double
defaultDecay = 2.0

-- | Default bounce elasticity
defaultElasticity :: Double
defaultElasticity = 0.7

-- | Default bounce gravity
defaultGravity :: Double
defaultGravity = 4000.0

-- | Default elastic period
defaultPeriod :: Double
defaultPeriod = 0.3

-- | Maximum bounces to simulate
maxBounces :: Int
maxBounces = 10

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Ensure amplitude is valid
safeAmplitude :: Double -> Double
safeAmplitude amp = if isFinite amp then amp else defaultAmplitude
  where isFinite x = not (isNaN x || isInfinite x)

-- | Ensure frequency is valid
safeFrequency :: Double -> Double
safeFrequency freq = if isFinite freq then freq else defaultFrequency
  where isFinite x = not (isNaN x || isInfinite x)

-- | Ensure decay is valid (minimum 0.001)
safeDecay :: Double -> Double
safeDecay decay = if isFinite decay then max 0.001 decay else defaultDecay
  where isFinite x = not (isNaN x || isInfinite x)

-- | Ensure elasticity is valid (clamped to [0, 1])
safeElasticity :: Double -> Double
safeElasticity e = if isFinite e then min 1 (max 0 e) else defaultElasticity
  where isFinite x = not (isNaN x || isInfinite x)

-- | Ensure gravity is valid (positive)
safeGravity :: Double -> Double
safeGravity g = if isFinite g && g > 0 then g else defaultGravity
  where isFinite x = not (isNaN x || isInfinite x)

-- | Ensure period is valid (positive)
safePeriod :: Double -> Double
safePeriod p = if isFinite p && p > 0 then p else defaultPeriod
  where isFinite x = not (isNaN x || isInfinite x)

--------------------------------------------------------------------------------
-- Inertia Oscillation
--------------------------------------------------------------------------------

-- | Damped sine wave oscillation for inertia effect.
--
-- velocity: Initial velocity component
-- amplitude: Oscillation amplitude multiplier
-- frequency: Oscillation frequency in Hz
-- decay: Exponential decay rate
-- t: Time since keyframe (must be positive)
--
-- Returns: Oscillation offset to add to value
inertiaOscillation :: Double -> Double -> Double -> Double -> Double -> Double
inertiaOscillation velocity amplitude frequency decay t
  | t <= 0 = 0
  | decayFactor == 0 = 0
  | otherwise = velocity * safeAmp * sin phase / decayFactor
  where
    safeAmp = safeAmplitude amplitude
    safeFreq = safeFrequency frequency
    safeDec = safeDecay decay
    phase = safeFreq * t * 2 * pi
    decayFactor = exp (safeDec * t)

-- | Apply inertia to a scalar value
inertiaScalar :: Double -> Double -> Double -> Double -> Double -> Double -> Double
inertiaScalar value velocity amplitude frequency decay t =
  value + inertiaOscillation velocity amplitude frequency decay t

-- | Apply inertia to a vector value
inertiaVector :: Vector Double -> Vector Double -> Double -> Double -> Double -> Double -> Vector Double
inertiaVector values velocities amplitude frequency decay t =
  V.zipWith (\v vel -> v + inertiaOscillation vel amplitude frequency decay t) values velocities

--------------------------------------------------------------------------------
-- Bounce Physics
--------------------------------------------------------------------------------

-- | Calculate bounce position given time and parameters.
--
-- t: Time since keyframe (must be positive)
-- elasticity: Bounce energy retention (0-1)
-- gravity: Gravity acceleration
--
-- Returns: Bounce offset to subtract from value
bouncePhysics :: Double -> Double -> Double -> Double
bouncePhysics t elasticity gravity
  | t <= 0 = 0
  | otherwise = bounceOffset * (1 - safeE)
  where
    safeE = safeElasticity elasticity
    safeG = safeGravity gravity

    -- Calculate which bounce we're in
    findBounce 0 bounceTime height = (bounceTime, height)
    findBounce n bounceTime height
      | bounceTime <= 0 = (bounceTime, height)
      | bounceTime < bounceDuration * 2 = (bounceTime, height)
      | otherwise = findBounce (n - 1) newTime newHeight
      where
        bounceDuration = sqrt (2 * height / safeG)
        newTime = bounceTime - bounceDuration * 2
        newHeight = height * safeE * safeE

    (bounceTime, bounceHeight) = findBounce maxBounces t 1.0

    -- Position within current bounce (parabola)
    bounceDuration = sqrt (2 * bounceHeight / safeG)
    bounceT = if bounceDuration == 0 then 0 else bounceTime / (bounceDuration * 2)
    bounceOffset = bounceHeight * 4 * bounceT * (1 - bounceT)

-- | Apply bounce to a scalar value
bounceScalar :: Double -> Double -> Double -> Double -> Double
bounceScalar value t elasticity gravity =
  value - bouncePhysics t elasticity gravity

-- | Apply bounce to a vector value (same offset for all components)
bounceVector :: Vector Double -> Double -> Double -> Double -> Vector Double
bounceVector values t elasticity gravity =
  let offset = bouncePhysics t elasticity gravity
  in V.map (\v -> v - offset) values

--------------------------------------------------------------------------------
-- Elastic Oscillation
--------------------------------------------------------------------------------

-- | Elastic spring-like oscillation.
--
-- t: Time since keyframe (must be positive)
-- amplitude: Maximum displacement
-- period: Oscillation period in seconds
--
-- Returns: Oscillation offset to add to value
elasticOscillation :: Double -> Double -> Double -> Double
elasticOscillation t amplitude period
  | t <= 0 = 0
  | otherwise = safeAmp * decay * sin phase
  where
    safeAmp = safeAmplitude amplitude
    safePer = safePeriod period
    s = safePer / 4
    -- Exponential decay: 2^(-10*t)
    decay = exp (-10 * t * log 2)
    phase = (t - s) * 2 * pi / safePer

-- | Apply elastic motion to a scalar value
elasticScalar :: Double -> Double -> Double -> Double -> Double
elasticScalar value t amplitude period =
  value + elasticOscillation t amplitude period

-- | Apply elastic motion to a vector value
elasticVector :: Vector Double -> Double -> Double -> Double -> Vector Double
elasticVector values t amplitude period =
  let oscillation = elasticOscillation t amplitude period
  in V.map (+ oscillation) values

--------------------------------------------------------------------------------
-- Main API
--------------------------------------------------------------------------------

-- | Inertia expression for scalar values
inertia :: Double -> Double -> Double -> Double -> Double -> Double -> Double
inertia value velocity t amplitude frequency decay =
  inertiaScalar value velocity amplitude frequency decay t

-- | Inertia expression for vector values
inertiaVec :: Vector Double -> Vector Double -> Double -> Double -> Double -> Double -> Vector Double
inertiaVec values velocities t amplitude frequency decay =
  inertiaVector values velocities amplitude frequency decay t

-- | Bounce expression for scalar values
bounce :: Double -> Double -> Double -> Double -> Double
bounce value t elasticity gravity =
  bounceScalar value t elasticity gravity

-- | Bounce expression for vector values
bounceVec :: Vector Double -> Double -> Double -> Double -> Vector Double
bounceVec values t elasticity gravity =
  bounceVector values t elasticity gravity

-- | Elastic expression for scalar values
elastic :: Double -> Double -> Double -> Double -> Double
elastic value t amplitude period =
  elasticScalar value t amplitude period

-- | Elastic expression for vector values
elasticVec :: Vector Double -> Double -> Double -> Double -> Vector Double
elasticVec values t amplitude period =
  elasticVector values t amplitude period
