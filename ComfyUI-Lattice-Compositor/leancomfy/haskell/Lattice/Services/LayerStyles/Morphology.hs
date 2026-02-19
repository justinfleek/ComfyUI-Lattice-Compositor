{-|
{-# LANGUAGE OverloadedStrings #-}
  Lattice.Services.LayerStyles.Morphology - Alpha Morphology Operations

  Pure mathematical functions for morphological operations on alpha:
  - Dilate (expand) alpha channel
  - Erode (shrink) alpha channel
  - Used for spread/choke in shadows, strokes

  Source: ui/src/services/effects/layerStyleRenderer.ts (lines 160-229)
-}

module Lattice.Services.LayerStyles.Morphology
  ( distance
  , withinRadius
  , clampCoord
  , pixelIndex
  , dilateKernel
  , erodeKernel
  , dilationRadius
  , erosionRadius
  , blurAfterMorphology
  ) where

--------------------------------------------------------------------------------
-- Distance Calculation
--------------------------------------------------------------------------------

-- | Calculate Euclidean distance between two points.
--
--   @param dx X offset
--   @param dy Y offset
--   @return Distance
distance :: Double -> Double -> Double
distance dx dy = sqrt (dx * dx + dy * dy)

-- | Check if a point is within circular radius.
--
--   @param dx X offset from center
--   @param dy Y offset from center
--   @param radius Maximum radius
--   @return True if within radius
withinRadius :: Double -> Double -> Double -> Bool
withinRadius dx dy radius = distance dx dy <= radius

--------------------------------------------------------------------------------
-- Coordinate Bounds
--------------------------------------------------------------------------------

-- | Clamp coordinate to valid range.
--
--   @param coord Coordinate value
--   @param maxVal Maximum valid value (dimension - 1)
--   @return Clamped coordinate in [0, maxVal]
clampCoord :: Int -> Int -> Int
clampCoord coord maxVal
  | coord < 0 = 0
  | coord > maxVal = maxVal
  | otherwise = coord

-- | Calculate pixel index from 2D coordinates.
--
--   @param x X coordinate
--   @param y Y coordinate
--   @param width Image width
--   @return Linear pixel index
pixelIndex :: Int -> Int -> Int -> Int
pixelIndex x y width = y * width + x

--------------------------------------------------------------------------------
-- Dilation (Expand Alpha)
--------------------------------------------------------------------------------

-- | Dilation kernel value at a single neighbor.
--
--   For dilation, we take the maximum alpha value of all
--   neighbors within the radius.
--
--   @param neighborAlpha Alpha value of neighbor
--   @param currentMax Current maximum alpha
--   @return Updated maximum
dilateKernel :: Int -> Int -> Int
dilateKernel neighborAlpha currentMax = max currentMax neighborAlpha

-- | Calculate dilation kernel radius.
--
--   @param spreadPercent Spread amount (0-100)
--   @param size Effect size
--   @return Pixel radius for dilation
dilationRadius :: Double -> Double -> Double
dilationRadius spreadPercent size = (spreadPercent / 100.0) * size

--------------------------------------------------------------------------------
-- Erosion (Shrink Alpha)
--------------------------------------------------------------------------------

-- | Erosion kernel value at a single neighbor.
--
--   For erosion, we take the minimum alpha value of all
--   neighbors within the radius.
--
--   @param neighborAlpha Alpha value of neighbor
--   @param currentMin Current minimum alpha
--   @return Updated minimum
erodeKernel :: Int -> Int -> Int
erodeKernel neighborAlpha currentMin = min currentMin neighborAlpha

-- | Calculate erosion (choke) kernel radius.
--
--   @param chokePercent Choke amount (0-100)
--   @param size Effect size
--   @return Pixel radius for erosion
erosionRadius :: Double -> Double -> Double
erosionRadius chokePercent size = (chokePercent / 100.0) * size

--------------------------------------------------------------------------------
-- Blur After Morphology
--------------------------------------------------------------------------------

-- | Calculate blur radius after spread/choke.
--
--   The blur is reduced proportionally to the spread/choke amount
--   to maintain apparent size.
--
--   @param size Total effect size
--   @param spreadOrChokePercent Spread/choke percentage (0-100)
--   @return Blur radius
blurAfterMorphology :: Double -> Double -> Double
blurAfterMorphology size spreadOrChokePercent =
  size * (1.0 - spreadOrChokePercent / 100.0)
