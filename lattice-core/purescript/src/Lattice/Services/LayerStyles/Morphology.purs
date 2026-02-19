{-
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

import Prelude

import Math (sqrt)

--------------------------------------------------------------------------------
-- Distance Calculation
--------------------------------------------------------------------------------

-- | Calculate Euclidean distance between two points.
distance :: Number -> Number -> Number
distance dx dy = sqrt (dx * dx + dy * dy)

-- | Check if a point is within circular radius.
withinRadius :: Number -> Number -> Number -> Boolean
withinRadius dx dy radius = distance dx dy <= radius

--------------------------------------------------------------------------------
-- Coordinate Bounds
--------------------------------------------------------------------------------

-- | Clamp coordinate to valid range.
clampCoord :: Int -> Int -> Int
clampCoord coord maxVal
  | coord < 0 = 0
  | coord > maxVal = maxVal
  | otherwise = coord

-- | Calculate pixel index from 2D coordinates.
pixelIndex :: Int -> Int -> Int -> Int
pixelIndex x y width = y * width + x

--------------------------------------------------------------------------------
-- Dilation (Expand Alpha)
--------------------------------------------------------------------------------

-- | Dilation kernel value at a single neighbor.
dilateKernel :: Int -> Int -> Int
dilateKernel neighborAlpha currentMax = max currentMax neighborAlpha

-- | Calculate dilation kernel radius.
dilationRadius :: Number -> Number -> Number
dilationRadius spreadPercent size = (spreadPercent / 100.0) * size

--------------------------------------------------------------------------------
-- Erosion (Shrink Alpha)
--------------------------------------------------------------------------------

-- | Erosion kernel value at a single neighbor.
erodeKernel :: Int -> Int -> Int
erodeKernel neighborAlpha currentMin = min currentMin neighborAlpha

-- | Calculate erosion (choke) kernel radius.
erosionRadius :: Number -> Number -> Number
erosionRadius chokePercent size = (chokePercent / 100.0) * size

--------------------------------------------------------------------------------
-- Blur After Morphology
--------------------------------------------------------------------------------

-- | Calculate blur radius after spread/choke.
blurAfterMorphology :: Number -> Number -> Number
blurAfterMorphology size spreadOrChokePercent =
  size * (1.0 - spreadOrChokePercent / 100.0)
