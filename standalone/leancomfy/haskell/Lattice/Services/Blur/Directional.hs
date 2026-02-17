{-|
  Lattice.Services.Blur.Directional - Directional/Motion Blur Mathematics

  Pure mathematical functions for directional blur calculations:
  - Direction vector from angle
  - Sample position calculation
  - Motion blur trajectory

  Source: ui/src/services/effects/blurRenderer.ts (lines 1106-1148)
-}

module Lattice.Services.Blur.Directional
  ( -- * Direction Vector
    directionVector
  , degreesToRadians
  , directionVectorDeg
    -- * Sample Position Calculation
  , samplePosition
  , directionalSamplePosition
    -- * Sample Weight
  , sampleWeight
  , optimalSampleCount
    -- * Bounds Clamping
  , clampSamplePosition
  ) where

--------------------------------------------------------------------------------
-- Direction Vector
--------------------------------------------------------------------------------

-- | Calculate direction vector from angle in radians.
--
--   @param angleRad Angle in radians (0 = right, π/2 = down)
--   @return (dx, dy) unit direction vector
directionVector :: Double -> (Double, Double)
directionVector angleRad = (cos angleRad, sin angleRad)

-- | Convert degrees to radians.
--
--   @param degrees Angle in degrees
--   @return Angle in radians
degreesToRadians :: Double -> Double
degreesToRadians degrees = degrees * pi / 180.0

-- | Calculate direction vector from angle in degrees.
--
--   @param angleDeg Angle in degrees (0 = right, 90 = down)
--   @return (dx, dy) unit direction vector
directionVectorDeg :: Double -> (Double, Double)
directionVectorDeg angleDeg = directionVector (degreesToRadians angleDeg)

--------------------------------------------------------------------------------
-- Sample Position Calculation
--------------------------------------------------------------------------------

-- | Calculate sample position along blur direction.
--
--   For motion blur, samples are taken along a line in the direction
--   of motion. This calculates where to sample for a given offset.
--
--   @param x Current pixel X
--   @param y Current pixel Y
--   @param dx Direction X component
--   @param dy Direction Y component
--   @param offset Sample offset along direction
--   @return (sampleX, sampleY) position
samplePosition :: Double -> Double -> Double -> Double -> Double -> (Double, Double)
samplePosition x y dx dy offset = (x + dx * offset, y + dy * offset)

-- | Calculate all sample positions for directional blur.
--
--   Samples are distributed evenly from -halfLength to +halfLength
--   along the blur direction.
--
--   @param x Pixel X coordinate
--   @param y Pixel Y coordinate
--   @param dx Direction X
--   @param dy Direction Y
--   @param blurLength Total blur length in pixels
--   @param sampleCount Number of samples
--   @param sampleIndex Index of sample (0 to sampleCount-1)
--   @return (sampleX, sampleY) position for this sample
directionalSamplePosition
  :: Double -> Double -> Double -> Double -> Double -> Int -> Int -> (Double, Double)
directionalSamplePosition x y dx dy blurLength sampleCount sampleIndex =
  let halfSamples = fromIntegral sampleCount / 2.0
      i = fromIntegral sampleIndex - halfSamples
      step = blurLength / fromIntegral sampleCount
      offset = i * step
  in samplePosition x y dx dy offset

--------------------------------------------------------------------------------
-- Sample Weight
--------------------------------------------------------------------------------

-- | Calculate weight for directional blur sample.
--
--   For basic motion blur, all samples have equal weight.
--   For tapered motion blur, central samples have higher weight.
--
--   @param sampleIndex Index of sample
--   @param sampleCount Total number of samples
--   @param tapered Whether to use tapered weights
--   @return Weight for this sample (normalized)
sampleWeight :: Int -> Int -> Bool -> Double
sampleWeight sampleIndex sampleCount tapered
  | tapered =
      -- Triangular weighting (central samples weighted more)
      let center = fromIntegral sampleCount / 2.0
          dist = abs (fromIntegral sampleIndex - center)
          maxDist = center
      in if maxDist < 0.0001
         then 1.0
         else 1.0 - (dist / maxDist) * 0.5  -- 50% tapering
  | otherwise = 1.0  -- Uniform weighting

-- | Calculate optimal sample count for blur length.
--
--   More samples = smoother blur, but slower.
--   We use at least 3 samples, and scale with blur length.
--
--   @param blurLength Blur length in pixels
--   @return Recommended sample count
optimalSampleCount :: Double -> Int
optimalSampleCount blurLength =
  let samples = ceiling blurLength
  in max 3 samples

--------------------------------------------------------------------------------
-- Bounds Clamping
--------------------------------------------------------------------------------

-- | Clamp sample position to image bounds.
--
--   @param sampleX Sample X position
--   @param sampleY Sample Y position
--   @param width Image width
--   @param height Image height
--   @return Clamped (x, y) position
clampSamplePosition :: Double -> Double -> Int -> Int -> (Double, Double)
clampSamplePosition sampleX sampleY width height =
  let clampedX = max 0.0 (min (fromIntegral width - 1.0) sampleX)
      clampedY = max 0.0 (min (fromIntegral height - 1.0) sampleY)
  in (clampedX, clampedY)
