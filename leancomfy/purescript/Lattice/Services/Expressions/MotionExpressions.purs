-- | Lattice.Services.Expressions.MotionExpressions - Motion physics functions
-- |
-- | Core physics calculations for momentum-based animations:
-- | - inertiaOscillation: Damped sine wave oscillation
-- | - bouncePhysics: Bouncing settle with elasticity
-- | - elasticOscillation: Spring-like elastic motion
-- |
-- | Source: ui/src/services/expressions/motionExpressions.ts

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

import Prelude
import Data.Array (zipWith)
import Global (isNaN, isFinite) as Global
import Math (exp, log, pi, sin, sqrt) as Math

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Default inertia amplitude
defaultAmplitude :: Number
defaultAmplitude = 0.1

-- | Default inertia frequency
defaultFrequency :: Number
defaultFrequency = 2.0

-- | Default inertia decay
defaultDecay :: Number
defaultDecay = 2.0

-- | Default bounce elasticity
defaultElasticity :: Number
defaultElasticity = 0.7

-- | Default bounce gravity
defaultGravity :: Number
defaultGravity = 4000.0

-- | Default elastic period
defaultPeriod :: Number
defaultPeriod = 0.3

-- | Maximum bounces to simulate
maxBounces :: Int
maxBounces = 10

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Check if finite
isFiniteNum :: Number -> Boolean
isFiniteNum x = Global.isFinite x && not (Global.isNaN x)

-- | Ensure amplitude is valid
safeAmplitude :: Number -> Number
safeAmplitude amp = if isFiniteNum amp then amp else defaultAmplitude

-- | Ensure frequency is valid
safeFrequency :: Number -> Number
safeFrequency freq = if isFiniteNum freq then freq else defaultFrequency

-- | Ensure decay is valid (minimum 0.001)
safeDecay :: Number -> Number
safeDecay decay = if isFiniteNum decay then max 0.001 decay else defaultDecay

-- | Ensure elasticity is valid (clamped to [0, 1])
safeElasticity :: Number -> Number
safeElasticity e = if isFiniteNum e then min 1.0 (max 0.0 e) else defaultElasticity

-- | Ensure gravity is valid (positive)
safeGravity :: Number -> Number
safeGravity g = if isFiniteNum g && g > 0.0 then g else defaultGravity

-- | Ensure period is valid (positive)
safePeriod :: Number -> Number
safePeriod p = if isFiniteNum p && p > 0.0 then p else defaultPeriod

--------------------------------------------------------------------------------
-- Inertia Oscillation
--------------------------------------------------------------------------------

-- | Damped sine wave oscillation for inertia effect.
-- |
-- | velocity: Initial velocity component
-- | amplitude: Oscillation amplitude multiplier
-- | frequency: Oscillation frequency in Hz
-- | decay: Exponential decay rate
-- | t: Time since keyframe (must be positive)
-- |
-- | Returns: Oscillation offset to add to value
inertiaOscillation :: Number -> Number -> Number -> Number -> Number -> Number
inertiaOscillation velocity amplitude frequency decay t =
  let safeAmp = safeAmplitude amplitude
      safeFreq = safeFrequency frequency
      safeDec = safeDecay decay
      phase = safeFreq * t * 2.0 * Math.pi
      df = Math.exp (safeDec * t)
  in if t <= 0.0 then 0.0
     else if df == 0.0 then 0.0
     else velocity * safeAmp * Math.sin phase / df

-- | Apply inertia to a scalar value
inertiaScalar :: Number -> Number -> Number -> Number -> Number -> Number -> Number
inertiaScalar value velocity amplitude frequency decay t =
  value + inertiaOscillation velocity amplitude frequency decay t

-- | Apply inertia to a vector value
inertiaVector :: Array Number -> Array Number -> Number -> Number -> Number -> Number -> Array Number
inertiaVector values velocities amplitude frequency decay t =
  zipWith (\v vel -> v + inertiaOscillation vel amplitude frequency decay t) values velocities

--------------------------------------------------------------------------------
-- Bounce Physics
--------------------------------------------------------------------------------

-- | Calculate bounce position given time and parameters.
-- |
-- | t: Time since keyframe (must be positive)
-- | elasticity: Bounce energy retention (0-1)
-- | gravity: Gravity acceleration
-- |
-- | Returns: Bounce offset to subtract from value
bouncePhysics :: Number -> Number -> Number -> Number
bouncePhysics t elasticity gravity
  | t <= 0.0 = 0.0
  | otherwise = bounceOffset * (1.0 - safeE)
  where
    safeE = safeElasticity elasticity
    safeG = safeGravity gravity

    -- Calculate which bounce we're in (tail-recursive)
    findBounce nRemaining bounceTime height =
      let bounceDur = Math.sqrt (2.0 * height / safeG)
          newTime = bounceTime - bounceDur * 2.0
          newHeight = height * safeE * safeE
      in if nRemaining <= 0
         then { time: bounceTime, height }
         else if bounceTime <= 0.0
         then { time: bounceTime, height }
         else if bounceTime < bounceDur * 2.0
         then { time: bounceTime, height }
         else findBounce (nRemaining - 1) newTime newHeight

    bounceResult = findBounce maxBounces t 1.0
    bounceTime = bounceResult.time
    bounceHeight = bounceResult.height

    -- Position within current bounce (parabola)
    bounceDuration = Math.sqrt (2.0 * bounceHeight / safeG)
    bounceT = if bounceDuration == 0.0 then 0.0 else bounceTime / (bounceDuration * 2.0)
    bounceOffset = bounceHeight * 4.0 * bounceT * (1.0 - bounceT)

-- | Apply bounce to a scalar value
bounceScalar :: Number -> Number -> Number -> Number -> Number
bounceScalar value t elasticity gravity =
  value - bouncePhysics t elasticity gravity

-- | Apply bounce to a vector value (same offset for all components)
bounceVector :: Array Number -> Number -> Number -> Number -> Array Number
bounceVector values t elasticity gravity =
  let offset = bouncePhysics t elasticity gravity
  in map (\v -> v - offset) values

--------------------------------------------------------------------------------
-- Elastic Oscillation
--------------------------------------------------------------------------------

-- | Elastic spring-like oscillation.
-- |
-- | t: Time since keyframe (must be positive)
-- | amplitude: Maximum displacement
-- | period: Oscillation period in seconds
-- |
-- | Returns: Oscillation offset to add to value
elasticOscillation :: Number -> Number -> Number -> Number
elasticOscillation t amplitude period
  | t <= 0.0 = 0.0
  | otherwise = safeAmp * decay * Math.sin phase
  where
    safeAmp = safeAmplitude amplitude
    safePer = safePeriod period
    s = safePer / 4.0
    -- Exponential decay: 2^(-10*t)
    decay = Math.exp (-10.0 * t * Math.log 2.0)
    phase = (t - s) * 2.0 * Math.pi / safePer

-- | Apply elastic motion to a scalar value
elasticScalar :: Number -> Number -> Number -> Number -> Number
elasticScalar value t amplitude period =
  value + elasticOscillation t amplitude period

-- | Apply elastic motion to a vector value
elasticVector :: Array Number -> Number -> Number -> Number -> Array Number
elasticVector values t amplitude period =
  let oscillation = elasticOscillation t amplitude period
  in map (_ + oscillation) values

--------------------------------------------------------------------------------
-- Main API
--------------------------------------------------------------------------------

-- | Inertia expression for scalar values
inertia :: Number -> Number -> Number -> Number -> Number -> Number -> Number
inertia value velocity t amplitude frequency decay =
  inertiaScalar value velocity amplitude frequency decay t

-- | Inertia expression for vector values
inertiaVec :: Array Number -> Array Number -> Number -> Number -> Number -> Number -> Array Number
inertiaVec values velocities t amplitude frequency decay =
  inertiaVector values velocities amplitude frequency decay t

-- | Bounce expression for scalar values
bounce :: Number -> Number -> Number -> Number -> Number
bounce value t elasticity gravity =
  bounceScalar value t elasticity gravity

-- | Bounce expression for vector values
bounceVec :: Array Number -> Number -> Number -> Number -> Array Number
bounceVec values t elasticity gravity =
  bounceVector values t elasticity gravity

-- | Elastic expression for scalar values
elastic :: Number -> Number -> Number -> Number -> Number
elastic value t amplitude period =
  elasticScalar value t amplitude period

-- | Elastic expression for vector values
elasticVec :: Array Number -> Number -> Number -> Number -> Array Number
elasticVec values t amplitude period =
  elasticVector values t amplitude period
