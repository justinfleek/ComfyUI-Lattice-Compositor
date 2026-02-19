{-
  Lattice.Services.Distort.Interpolation - Bilinear Interpolation Mathematics

  Pure mathematical functions for pixel interpolation:
  - Bilinear interpolation weights
  - Coordinate clamping
  - Index calculation

  This is used by all distortion effects for smooth pixel sampling.

  Source: ui/src/services/effects/distortRenderer.ts (lines 376-401, 792-816)
-}

module Lattice.Services.Distort.Interpolation
  ( BilinearCoords
  , BilinearWeights
  , clampCoord
  , clampToBounds
  , bilinearCoords
  , bilinearWeights
  , weightsFromCoords
  , pixelIndex
  , rgbaOffset
  , cornerIndices
  , interpolateValue
  , interpolateRound
  ) where

import Prelude

import Data.Int (floor, round, toNumber) as Int
import Data.Tuple (Tuple(..))

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Bilinear sample coordinates
type BilinearCoords =
  { x0 :: Int       -- Floor X
  , y0 :: Int       -- Floor Y
  , x1 :: Int       -- Ceil X (clamped)
  , y1 :: Int       -- Ceil Y (clamped)
  , fx :: Number    -- Fractional X [0, 1)
  , fy :: Number    -- Fractional Y [0, 1)
  }

-- | Bilinear weights for 4 corners
type BilinearWeights =
  { w00 :: Number   -- Top-left weight
  , w10 :: Number   -- Top-right weight
  , w01 :: Number   -- Bottom-left weight
  , w11 :: Number   -- Bottom-right weight
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Coordinate Clamping
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp coordinate to valid pixel range.
--
--   @param coord Coordinate value
--   @param maxVal Maximum valid value (width-1 or height-1)
--   @return Clamped coordinate in [0, maxVal]
clampCoord :: Number -> Int -> Number
clampCoord coord maxVal =
  max 0.0 (min (toNumber maxVal) coord)

-- | Clamp source coordinates to image bounds.
--
--   @param srcX Source X coordinate
--   @param srcY Source Y coordinate
--   @param width Image width
--   @param height Image height
--   @return (clampedX, clampedY)
clampToBounds :: Number -> Number -> Int -> Int -> Tuple Number Number
clampToBounds srcX srcY width height =
  let maxX = if width > 0 then width - 1 else 0
      maxY = if height > 0 then height - 1 else 0
  in Tuple (clampCoord srcX maxX) (clampCoord srcY maxY)

-- ────────────────────────────────────────────────────────────────────────────
-- Bilinear Coordinate Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate bilinear interpolation coordinates.
--
--   @param srcX Source X (floating point)
--   @param srcY Source Y (floating point)
--   @param width Image width
--   @param height Image height
--   @return Bilinear sampling coordinates
bilinearCoords :: Number -> Number -> Int -> Int -> BilinearCoords
bilinearCoords srcX srcY width height =
  let maxX = if width > 0 then width - 1 else 0
      maxY = if height > 0 then height - 1 else 0

      x0f = toNumber (Int.floor srcX)
      y0f = toNumber (Int.floor srcY)

      x0 = min maxX (max 0 (Int.floor srcX))
      y0 = min maxY (max 0 (Int.floor srcY))
      x1 = min maxX (x0 + 1)
      y1 = min maxY (y0 + 1)

      fx = srcX - x0f
      fy = srcY - y0f

  in { x0, y0, x1, y1, fx, fy }

-- ────────────────────────────────────────────────────────────────────────────
-- Bilinear Weights
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate bilinear interpolation weights from fractional parts.
--
--   Weights sum to 1.0 for proper interpolation.
--
--   @param fx Fractional X [0, 1)
--   @param fy Fractional Y [0, 1)
--   @return Weights for 4 corners
bilinearWeights :: Number -> Number -> BilinearWeights
bilinearWeights fx fy =
  let invFx = 1.0 - fx
      invFy = 1.0 - fy
  in { w00: invFx * invFy   -- Top-left
     , w10: fx * invFy      -- Top-right
     , w01: invFx * fy      -- Bottom-left
     , w11: fx * fy         -- Bottom-right
     }

-- | Get weights from bilinear coordinates.
--
--   @param coords Bilinear coordinates
--   @return Interpolation weights
weightsFromCoords :: BilinearCoords -> BilinearWeights
weightsFromCoords coords = bilinearWeights coords.fx coords.fy

-- ────────────────────────────────────────────────────────────────────────────
-- Pixel Index Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate linear pixel index from 2D coordinates.
--
--   @param x X coordinate
--   @param y Y coordinate
--   @param width Image width (stride)
--   @return Linear index for RGBA data (multiply by 4 for byte offset)
pixelIndex :: Int -> Int -> Int -> Int
pixelIndex x y width = y * width + x

-- | Calculate RGBA byte offset from pixel index.
--
--   @param pixelIdx Pixel index
--   @return Byte offset for first channel (R)
rgbaOffset :: Int -> Int
rgbaOffset pixelIdx = pixelIdx * 4

-- | Get all 4 corner indices for bilinear sampling.
--
--   @param coords Bilinear coordinates
--   @param width Image width
--   @return { idx00, idx10, idx01, idx11 } pixel indices
cornerIndices :: BilinearCoords -> Int -> { idx00 :: Int, idx10 :: Int, idx01 :: Int, idx11 :: Int }
cornerIndices coords width =
  let idx00 = pixelIndex coords.x0 coords.y0 width
      idx10 = pixelIndex coords.x1 coords.y0 width
      idx01 = pixelIndex coords.x0 coords.y1 width
      idx11 = pixelIndex coords.x1 coords.y1 width
  in { idx00, idx10, idx01, idx11 }

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Interpolate a single value using bilinear weights.
--
--   @param v00 Top-left value
--   @param v10 Top-right value
--   @param v01 Bottom-left value
--   @param v11 Bottom-right value
--   @param weights Bilinear weights
--   @return Interpolated value
interpolateValue :: Number -> Number -> Number -> Number -> BilinearWeights -> Number
interpolateValue v00 v10 v01 v11 weights =
  v00 * weights.w00 + v10 * weights.w10 + v01 * weights.w01 + v11 * weights.w11

-- | Interpolate and round to nearest integer (for 8-bit pixel values).
--
--   @param v00 v10 v01 v11 Corner values
--   @param weights Bilinear weights
--   @return Rounded interpolated value
interpolateRound :: Number -> Number -> Number -> Number -> BilinearWeights -> Int
interpolateRound v00 v10 v01 v11 weights =
  Int.round (interpolateValue v00 v10 v01 v11 weights)

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

toNumber :: Int -> Number
toNumber = Int.toNumber
