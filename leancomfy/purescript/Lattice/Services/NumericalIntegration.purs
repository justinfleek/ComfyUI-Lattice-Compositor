-- | Lattice.Services.NumericalIntegration - Numerical integration methods
-- |
-- | Pure numerical integration algorithms:
-- | - Simpson's rule for definite integrals
-- | - Trapezoidal rule
-- | - Binary search root finding
-- | - Frame blending calculations
-- |
-- | Source: ui/src/services/timewarp.ts (numerical parts)

module Lattice.Services.NumericalIntegration
  ( -- * Constants
    defaultTolerance, minSamples
    -- * Basic Integration
  , trapezoid, simpsonsRule, optimalSampleCount
    -- * Numerical Integration
  , integrateSimpsons, integrateTrapezoidal
    -- * Binary Search
  , binarySearchIntegral
    -- * Frame Blending
  , FrameBlend
  , calculateFrameBlend, lerp, blendFrameValues
    -- * Speed Integration
  , speedToRate, integrateSpeedCurve, cumulativeSourceFrames
  ) where

import Prelude
import Data.Array (length, mapWithIndex, range, foldl, snoc)
import Data.Int (floor, ceil, toNumber)
import Math (max) as Math

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Default tolerance for binary search
defaultTolerance :: Number
defaultTolerance = 0.01

-- | Minimum samples for Simpson's rule
minSamples :: Int
minSamples = 10

--------------------------------------------------------------------------------
-- Basic Integration
--------------------------------------------------------------------------------

-- | Trapezoidal rule for very short intervals.
-- | Averages function at endpoints and multiplies by interval width.
trapezoid :: Number -> Number -> Number -> Number
trapezoid fa fb span = ((fa + fb) / 2.0) * span

-- | Array get with default
arrayGet :: Array Number -> Int -> Number
arrayGet arr i = case arr !! i of
  Just x -> x
  Nothing -> 0.0

-- | Array indexing operator
infixl 8 arrayGet as !!

-- | Simpson's rule for numerical integration.
-- |
-- | Approximates ∫ₐᵇ f(x) dx using weighted sum of samples.
-- | Formula: (h/3) * [f(a) + 4*f(a+h) + 2*f(a+2h) + 4*f(a+3h) + ... + f(b)]
simpsonsRule :: Array Number -> Number -> Number
simpsonsRule samples h
  | length samples < 3 =
      -- Fallback to trapezoidal for too few samples
      if length samples == 2
      then trapezoid (samples !! 0) (samples !! 1) h
      else if length samples == 1
      then (samples !! 0) * h
      else 0.0
  | otherwise =
      let n = length samples - 1
          indexed = mapWithIndex (\i val ->
            let coeff =
                  if i == 0 then 1.0
                  else if i == n then 1.0
                  else if i `mod` 2 == 1 then 4.0
                  else 2.0
            in coeff * val) samples
          total = foldl (+) 0.0 indexed
      in (h / 3.0) * total

-- | Calculate optimal number of samples for Simpson's rule.
-- | Ensures odd number of points (even number of intervals).
optimalSampleCount :: Number -> Int -> Int
optimalSampleCount span minPerFrame =
  let raw = max minSamples (floor span * minPerFrame)
  in if raw `mod` 2 == 0 then raw + 1 else raw

--------------------------------------------------------------------------------
-- Numerical Integration with Function
--------------------------------------------------------------------------------

-- | Integrate a function from a to b using Simpson's rule.
integrateSimpsons :: (Number -> Number) -> Number -> Number -> Int -> Number
integrateSimpsons f a b numSamples =
  let span = b - a
  in if span <= 0.0 then 0.0
     else if span < 1.0 then
       -- Very short span - use trapezoid
       trapezoid (f a) (f b) span
     else
       let n = if numSamples > 0 then numSamples else optimalSampleCount span 2
           nOdd = if n `mod` 2 == 0 then n + 1 else n
           h = span / toNumber nOdd
           samples = map (\i -> f (a + toNumber i * h)) (range 0 nOdd)
       in simpsonsRule samples h

-- | Integrate a function using the trapezoidal rule.
integrateTrapezoidal :: (Number -> Number) -> Number -> Number -> Int -> Number
integrateTrapezoidal f a b numSamples =
  let span = b - a
  in if span <= 0.0 then 0.0
     else
       let h = span / toNumber numSamples
           samples = map (\i ->
             let x = a + toNumber i * h
                 coeff = if i == 0 || i == numSamples then 0.5 else 1.0
             in coeff * f x) (range 0 numSamples)
           total = foldl (+) 0.0 samples
       in h * total

--------------------------------------------------------------------------------
-- Binary Search Root Finding
--------------------------------------------------------------------------------

-- | Binary search to find x where cumulative integral equals target.
-- |
-- | This is the inverse of integration - given ∫ₐˣ f(t) dt = target, find x.
binarySearchIntegral :: (Number -> Number) -> Number -> Number -> Number -> Number -> Number
binarySearchIntegral integrator target low high tolerance =
  let search lo hi fuel
        | fuel <= 0 = (lo + hi) / 2.0
        | hi - lo <= tolerance = (lo + hi) / 2.0
        | otherwise =
            let mid = (lo + hi) / 2.0
                valueAtMid = integrator mid
            in if valueAtMid < target
               then search mid hi (fuel - 1)
               else search lo mid (fuel - 1)
  in search low high 100

--------------------------------------------------------------------------------
-- Frame Blending
--------------------------------------------------------------------------------

-- | Result of frame blend calculation
type FrameBlend =
  { floorFrame :: Int      -- ^ Floor frame number
  , ceilFrame :: Int       -- ^ Ceiling frame number
  , blendFactor :: Number  -- ^ Blend factor (0 = all floor, 1 = all ceiling)
  }

-- | Calculate frame blend information from fractional frame number
calculateFrameBlend :: Number -> FrameBlend
calculateFrameBlend fractionalFrame =
  let clamped = Math.max 0.0 fractionalFrame
      floorF = floor clamped
      ceilF = ceil clamped
      blend = clamped - toNumber floorF
  in { floorFrame: floorF
     , ceilFrame: ceilF
     , blendFactor: blend
     }

-- | Linear interpolation between two values
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Blend two frames based on blend factor
blendFrameValues :: Number -> Number -> FrameBlend -> Number
blendFrameValues valueAtFloor valueAtCeil blend =
  lerp valueAtFloor valueAtCeil blend.blendFactor

--------------------------------------------------------------------------------
-- Speed-Based Integration (Timewarp)
--------------------------------------------------------------------------------

-- | Convert speed percentage to rate multiplier.
-- | 100% = 1x, 200% = 2x, 50% = 0.5x
speedToRate :: Number -> Number
speedToRate speedPercent = speedPercent / 100.0

-- | Integrate speed curve to find source frame.
-- |
-- | speedSamples: Array of speed values (as percentages) at evenly spaced comp frames
-- | h: Step size (usually 1 frame or less)
-- |
-- | Returns: Cumulative source frames (integral of speed/100)
integrateSpeedCurve :: Array Number -> Number -> Number
integrateSpeedCurve speedSamples h =
  let rateSamples = map speedToRate speedSamples
  in simpsonsRule rateSamples h

-- | Calculate cumulative source frames at each sample point.
-- | Useful for building a lookup table.
cumulativeSourceFrames :: Array Number -> Number -> Array Number
cumulativeSourceFrames speedSamples h =
  let rates = map speedToRate speedSamples
      scanl' :: forall a b. (b -> a -> b) -> b -> Array a -> Array b
      scanl' f init arr = foldl (\acc x -> snoc acc (f (lastOrDefault init acc) x)) [init] arr
      lastOrDefault :: forall a. a -> Array a -> a
      lastOrDefault def arr = case arr !! (length arr - 1) of
        Just x -> x
        Nothing -> def
  in scanl' (\acc r -> acc + r * h) 0.0 rates
