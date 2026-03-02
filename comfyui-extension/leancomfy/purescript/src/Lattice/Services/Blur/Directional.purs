{-
  Lattice.Services.Blur.Directional - Directional/Motion Blur Mathematics

  Pure mathematical functions for directional blur calculations:
  - Direction vector from angle
  - Sample position calculation
  - Motion blur trajectory

  Source: ui/src/services/effects/blurRenderer.ts (lines 1106-1148)
-}

module Lattice.Services.Blur.Directional
  ( directionVector
  , degreesToRadians
  , directionVectorDeg
  , samplePosition
  , directionalSamplePosition
  , sampleWeight
  , optimalSampleCount
  , clampSamplePosition
  ) where

import Prelude

import Data.Int (toNumber, ceil) as Int
import Data.Tuple (Tuple(..))
import Math (cos, sin, abs, pi)

--------------------------------------------------------------------------------
-- Direction Vector
--------------------------------------------------------------------------------

-- | Calculate direction vector from angle in radians.
directionVector :: Number -> Tuple Number Number
directionVector angleRad = Tuple (cos angleRad) (sin angleRad)

-- | Convert degrees to radians.
degreesToRadians :: Number -> Number
degreesToRadians degrees = degrees * pi / 180.0

-- | Calculate direction vector from angle in degrees.
directionVectorDeg :: Number -> Tuple Number Number
directionVectorDeg angleDeg = directionVector (degreesToRadians angleDeg)

--------------------------------------------------------------------------------
-- Sample Position Calculation
--------------------------------------------------------------------------------

-- | Calculate sample position along blur direction.
samplePosition :: Number -> Number -> Number -> Number -> Number -> Tuple Number Number
samplePosition x y dx dy offset = Tuple (x + dx * offset) (y + dy * offset)

-- | Calculate sample position for directional blur.
directionalSamplePosition
  :: Number -> Number -> Number -> Number -> Number -> Int -> Int -> Tuple Number Number
directionalSamplePosition x y dx dy blurLength sampleCount sampleIndex =
  let halfSamples = Int.toNumber sampleCount / 2.0
      i = Int.toNumber sampleIndex - halfSamples
      step = blurLength / Int.toNumber sampleCount
      offset = i * step
  in samplePosition x y dx dy offset

--------------------------------------------------------------------------------
-- Sample Weight
--------------------------------------------------------------------------------

-- | Calculate weight for directional blur sample.
sampleWeight :: Int -> Int -> Boolean -> Number
sampleWeight sampleIndex sampleCount tapered
  | tapered =
      let center = Int.toNumber sampleCount / 2.0
          dist = abs (Int.toNumber sampleIndex - center)
          maxDist = center
      in if maxDist < 0.0001
         then 1.0
         else 1.0 - (dist / maxDist) * 0.5
  | otherwise = 1.0

-- | Calculate optimal sample count for blur length.
optimalSampleCount :: Number -> Int
optimalSampleCount blurLength =
  let samples = Int.ceil blurLength
  in max 3 samples

--------------------------------------------------------------------------------
-- Bounds Clamping
--------------------------------------------------------------------------------

-- | Clamp sample position to image bounds.
clampSamplePosition :: Number -> Number -> Int -> Int -> Tuple Number Number
clampSamplePosition sampleX sampleY width height =
  let clampedX = max 0.0 (min (Int.toNumber width - 1.0) sampleX)
      clampedY = max 0.0 (min (Int.toNumber height - 1.0) sampleY)
  in Tuple clampedX clampedY
