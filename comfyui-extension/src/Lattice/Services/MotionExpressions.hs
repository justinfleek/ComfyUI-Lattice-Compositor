-- |
-- Module      : Lattice.Services.MotionExpressions
-- Description : Pure motion expression functions for momentum-based animations
-- 
-- Migrated from ui/src/services/expressions/motionExpressions.ts
-- Pure calculations for inertia, bounce, and elastic motion
-- Note: Keyframe interpolation handled separately (requires interpolation service)
--

module Lattice.Services.MotionExpressions
  ( -- Motion expressions
    inertia
  , bounce
  , elastic
  -- Types
  , MotionParams(..)
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety (safeSqrtD)
import Lattice.Utils.ArrayUtils (safeArrayGet)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Parameters for motion expressions
-- Simplified from MotionExpressionContext - only what's needed for pure calculations
data MotionParams = MotionParams
  { motionParamsTime :: Double          -- Current time
  , motionParamsKeyTime :: Double       -- Time of last keyframe
  , motionParamsValue :: [Double]       -- Current value (as array)
  , motionParamsVelocity :: [Double]    -- Current velocity (as array)
  , motionParamsFps :: Double           -- Frames per second
  } deriving (Eq, Show)

-- | Safe array element access
safeGet :: [Double] -> Int -> Double
safeGet arr idx =
  let val = safeArrayGet arr idx 0.0
  in if isFinite val then val else 0.0

-- ============================================================================
-- MOTION EXPRESSIONS
-- ============================================================================

-- | Inertia/Overshoot expression
-- Pure function: same inputs → same outputs
-- Creates momentum-based animation after keyframes
inertia ::
  MotionParams ->
  Double ->  -- amplitude (default 0.1)
  Double ->  -- frequency (default 2.0)
  Double ->  -- decay (default 2.0)
  [Double]
inertia params amplitude frequency decay =
  let safeAmplitude = if isFinite amplitude then amplitude else 0.1
      safeFrequency = if isFinite frequency then frequency else 2.0
      safeDecay = if isFinite decay && decay > 0.001 then decay else 2.0
      t = motionParamsTime params - motionParamsKeyTime params
  in if t <= 0
       then motionParamsValue params
       else
         let valueArr = motionParamsValue params
             velocityArr = motionParamsVelocity params
             maxLen = max (length valueArr) (length velocityArr)
             oscillation i =
               let componentVel = safeGet velocityArr i
                   oscillationVal =
                     (componentVel * safeAmplitude * sin (safeFrequency * t * 2 * pi)) /
                     exp (safeDecay * t)
               in safeGet valueArr i + oscillationVal
         in [oscillation i | i <- [0 .. maxLen - 1]]

-- | Bounce expression
-- Pure function: same inputs → same outputs
-- Creates bouncing settle after keyframes
bounce ::
  MotionParams ->
  Double ->  -- elasticity (default 0.7)
  Double ->  -- gravity (default 4000)
  [Double]
bounce params elasticity gravity =
  let safeElasticity = if isFinite elasticity
                         then max 0 (min 1 elasticity)
                         else 0.7
      safeGravity = if isFinite gravity && gravity > 0 then gravity else 4000
      t = motionParamsTime params - motionParamsKeyTime params
  in if t <= 0
       then motionParamsValue params
       else
         let -- Bounce physics
             maxBounces = 10
             calculateBounce bounceTime bounceHeight totalBounces
               | totalBounces >= maxBounces = (bounceTime, bounceHeight)
               | otherwise =
                   let bounceDuration = safeSqrtD ((2 * bounceHeight) / safeGravity) 0.0
                   in if bounceTime < bounceDuration * 2
                        then (bounceTime, bounceHeight)
                        else calculateBounce
                          (bounceTime - bounceDuration * 2)
                          (bounceHeight * safeElasticity * safeElasticity)
                          (totalBounces + 1)
             (remainingTime, currentHeight) = calculateBounce t 1.0 0
             bounceDuration = safeSqrtD ((2 * currentHeight) / safeGravity) 0.0
             bounceT = remainingTime / (bounceDuration * 2)
             bounceOffset = currentHeight * 4 * bounceT * (1 - bounceT)
             valueArr = motionParamsValue params
         in map (\v -> v - bounceOffset * (1 - safeElasticity)) valueArr

-- | Elastic expression
-- Pure function: same inputs → same outputs
-- Creates elastic spring-like motion
elastic ::
  MotionParams ->
  Double ->  -- amplitude (default 1)
  Double ->  -- period (default 0.3)
  [Double]
elastic params amplitude period =
  let safeAmplitude = if isFinite amplitude then amplitude else 1
      safePeriod = if isFinite period && period > 0 then period else 0.3
      t = motionParamsTime params - motionParamsKeyTime params
  in if t <= 0
       then motionParamsValue params
       else
         let s = safePeriod / 4
             decay = 2 ** (-10 * t)
             oscillation = decay * sin (((t - s) * (2 * pi)) / safePeriod)
             valueArr = motionParamsValue params
         in map (\v -> v + safeAmplitude * oscillation) valueArr
