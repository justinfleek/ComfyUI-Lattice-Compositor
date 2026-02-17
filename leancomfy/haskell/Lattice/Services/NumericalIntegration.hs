{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.NumericalIntegration
Description : Numerical integration methods
Copyright   : (c) Lattice, 2026
License     : MIT

Pure numerical integration algorithms:
- Simpson's rule for definite integrals
- Trapezoidal rule
- Binary search root finding
- Frame blending calculations

Source: ui/src/services/timewarp.ts (numerical parts)
-}

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
  , FrameBlend(..)
  , calculateFrameBlend, lerp, blendFrameValues
    -- * Speed Integration
  , speedToRate, integrateSpeedCurve, cumulativeSourceFrames
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Default tolerance for binary search
defaultTolerance :: Double
defaultTolerance = 0.01

-- | Minimum samples for Simpson's rule
minSamples :: Int
minSamples = 10

--------------------------------------------------------------------------------
-- Basic Integration
--------------------------------------------------------------------------------

-- | Trapezoidal rule for very short intervals.
-- Averages function at endpoints and multiplies by interval width.
trapezoid :: Double -> Double -> Double -> Double
trapezoid fa fb span = ((fa + fb) / 2) * span

-- | Simpson's rule for numerical integration.
--
-- Approximates ∫ₐᵇ f(x) dx using weighted sum of samples.
-- Formula: (h/3) * [f(a) + 4*f(a+h) + 2*f(a+2h) + 4*f(a+3h) + ... + f(b)]
--
-- samples: Vector of function values at evenly spaced points
-- h: Step size between samples
simpsonsRule :: Vector Double -> Double -> Double
simpsonsRule samples h
  | V.length samples < 3 =
      -- Fallback to trapezoidal for too few samples
      if V.length samples == 2
      then trapezoid (samples V.! 0) (samples V.! 1) h
      else if V.length samples == 1
      then (samples V.! 0) * h
      else 0
  | otherwise =
      let n = V.length samples - 1
          indexed = V.imap (\i val ->
            let coeff
                  | i == 0 = 1
                  | i == n = 1
                  | i `mod` 2 == 1 = 4
                  | otherwise = 2
            in fromIntegral coeff * val) samples
          total = V.sum indexed
      in (h / 3) * total

-- | Calculate optimal number of samples for Simpson's rule.
-- Ensures odd number of points (even number of intervals).
optimalSampleCount :: Double -> Int -> Int
optimalSampleCount span minPerFrame =
  let raw = max minSamples (floor span * minPerFrame)
  in if raw `mod` 2 == 0 then raw + 1 else raw

--------------------------------------------------------------------------------
-- Numerical Integration with Function
--------------------------------------------------------------------------------

-- | Integrate a function from a to b using Simpson's rule.
integrateSimpsons :: (Double -> Double) -> Double -> Double -> Int -> Double
integrateSimpsons f a b numSamples =
  let span = b - a
  in if span <= 0 then 0
     else if span < 1 then
       -- Very short span - use trapezoid
       trapezoid (f a) (f b) span
     else
       let n = if numSamples > 0 then numSamples else optimalSampleCount span 2
           nOdd = if n `mod` 2 == 0 then n + 1 else n
           h = span / fromIntegral nOdd
           samples = V.generate (nOdd + 1) (\i -> f (a + fromIntegral i * h))
       in simpsonsRule samples h

-- | Integrate a function using the trapezoidal rule.
integrateTrapezoidal :: (Double -> Double) -> Double -> Double -> Int -> Double
integrateTrapezoidal f a b numSamples =
  let span = b - a
  in if span <= 0 then 0
     else
       let h = span / fromIntegral numSamples
           samples = V.generate (numSamples + 1) (\i ->
             let x = a + fromIntegral i * h
                 coeff = if i == 0 || i == numSamples then 0.5 else 1.0
             in coeff * f x)
           total = V.sum samples
       in h * total

--------------------------------------------------------------------------------
-- Binary Search Root Finding
--------------------------------------------------------------------------------

-- | Binary search to find x where cumulative integral equals target.
--
-- This is the inverse of integration - given ∫ₐˣ f(t) dt = target, find x.
binarySearchIntegral :: (Double -> Double) -> Double -> Double -> Double -> Double -> Double
binarySearchIntegral integrator target low high tolerance =
  let search lo hi fuel
        | fuel <= 0 = (lo + hi) / 2
        | hi - lo <= tolerance = (lo + hi) / 2
        | otherwise =
            let mid = (lo + hi) / 2
                valueAtMid = integrator mid
            in if valueAtMid < target
               then search mid hi (fuel - 1)
               else search lo mid (fuel - 1)
  in search low high (100 :: Int)

--------------------------------------------------------------------------------
-- Frame Blending
--------------------------------------------------------------------------------

-- | Result of frame blend calculation
data FrameBlend = FrameBlend
  { floorFrame   :: Int      -- ^ Floor frame number
  , ceilFrame    :: Int      -- ^ Ceiling frame number
  , blendFactor  :: Double   -- ^ Blend factor (0 = all floor, 1 = all ceiling)
  } deriving (Show, Eq)

-- | Calculate frame blend information from fractional frame number
calculateFrameBlend :: Double -> FrameBlend
calculateFrameBlend fractionalFrame =
  let clamped = max 0 fractionalFrame
      floorF = floor clamped
      ceilF = ceiling clamped
      blend = clamped - fromIntegral floorF
  in FrameBlend
    { floorFrame = floorF
    , ceilFrame = ceilF
    , blendFactor = blend
    }

-- | Linear interpolation between two values
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * t

-- | Blend two frames based on blend factor
blendFrameValues :: Double -> Double -> FrameBlend -> Double
blendFrameValues valueAtFloor valueAtCeil blend =
  lerp valueAtFloor valueAtCeil (blendFactor blend)

--------------------------------------------------------------------------------
-- Speed-Based Integration (Timewarp)
--------------------------------------------------------------------------------

-- | Convert speed percentage to rate multiplier.
-- 100% = 1x, 200% = 2x, 50% = 0.5x
speedToRate :: Double -> Double
speedToRate speedPercent = speedPercent / 100

-- | Integrate speed curve to find source frame.
--
-- speedSamples: Vector of speed values (as percentages) at evenly spaced comp frames
-- h: Step size (usually 1 frame or less)
--
-- Returns: Cumulative source frames (integral of speed/100)
integrateSpeedCurve :: Vector Double -> Double -> Double
integrateSpeedCurve speedSamples h =
  let rateSamples = V.map speedToRate speedSamples
  in simpsonsRule rateSamples h

-- | Calculate cumulative source frames at each sample point.
-- Useful for building a lookup table.
cumulativeSourceFrames :: Vector Double -> Double -> Vector Double
cumulativeSourceFrames speedSamples h =
  let rates = V.map speedToRate speedSamples
  in V.scanl (\acc r -> acc + r * h) 0 rates
