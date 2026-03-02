{-|
  Lattice.Services.Distort.Interpolation - Bilinear Interpolation Mathematics

  Pure mathematical functions for pixel interpolation:
  - Bilinear interpolation weights
  - Coordinate clamping
  - Index calculation

  This is used by all distortion effects for smooth pixel sampling.

  Source: ui/src/services/effects/distortRenderer.ts (lines 376-401, 792-816)
-}

module Lattice.Services.Distort.Interpolation
  ( BilinearCoords(..)
  , BilinearWeights(..)
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

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Bilinear sample coordinates
data BilinearCoords = BilinearCoords
  { bcX0 :: !Int       -- ^ Floor X
  , bcY0 :: !Int       -- ^ Floor Y
  , bcX1 :: !Int       -- ^ Ceil X (clamped)
  , bcY1 :: !Int       -- ^ Ceil Y (clamped)
  , bcFx :: !Double    -- ^ Fractional X [0, 1)
  , bcFy :: !Double    -- ^ Fractional Y [0, 1)
  } deriving (Show, Eq)

-- | Bilinear weights for 4 corners
data BilinearWeights = BilinearWeights
  { bwW00 :: !Double   -- ^ Top-left weight
  , bwW10 :: !Double   -- ^ Top-right weight
  , bwW01 :: !Double   -- ^ Bottom-left weight
  , bwW11 :: !Double   -- ^ Bottom-right weight
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Coordinate Clamping
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp coordinate to valid pixel range.
--
--   @param coord Coordinate value
--   @param maxVal Maximum valid value (width-1 or height-1)
--   @return Clamped coordinate in [0, maxVal]
clampCoord :: Double -> Int -> Double
clampCoord coord maxVal =
  max 0.0 (min (fromIntegral maxVal) coord)

-- | Clamp source coordinates to image bounds.
--
--   @param srcX Source X coordinate
--   @param srcY Source Y coordinate
--   @param width Image width
--   @param height Image height
--   @return (clampedX, clampedY)
clampToBounds :: Double -> Double -> Int -> Int -> (Double, Double)
clampToBounds srcX srcY width height =
  let maxX = if width > 0 then width - 1 else 0
      maxY = if height > 0 then height - 1 else 0
  in (clampCoord srcX maxX, clampCoord srcY maxY)

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
bilinearCoords :: Double -> Double -> Int -> Int -> BilinearCoords
bilinearCoords srcX srcY width height =
  let maxX = if width > 0 then width - 1 else 0
      maxY = if height > 0 then height - 1 else 0

      x0f = fromIntegral (floor srcX :: Int)
      y0f = fromIntegral (floor srcY :: Int)

      x0 = min maxX (max 0 (floor srcX))
      y0 = min maxY (max 0 (floor srcY))
      x1 = min maxX (x0 + 1)
      y1 = min maxY (y0 + 1)

      fx = srcX - x0f
      fy = srcY - y0f

  in BilinearCoords
      { bcX0 = x0
      , bcY0 = y0
      , bcX1 = x1
      , bcY1 = y1
      , bcFx = fx
      , bcFy = fy
      }

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
bilinearWeights :: Double -> Double -> BilinearWeights
bilinearWeights fx fy =
  let invFx = 1.0 - fx
      invFy = 1.0 - fy
  in BilinearWeights
      { bwW00 = invFx * invFy   -- Top-left
      , bwW10 = fx * invFy      -- Top-right
      , bwW01 = invFx * fy      -- Bottom-left
      , bwW11 = fx * fy         -- Bottom-right
      }

-- | Get weights from bilinear coordinates.
--
--   @param coords Bilinear coordinates
--   @return Interpolation weights
weightsFromCoords :: BilinearCoords -> BilinearWeights
weightsFromCoords coords = bilinearWeights (bcFx coords) (bcFy coords)

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
--   @return (idx00, idx10, idx01, idx11) pixel indices
cornerIndices :: BilinearCoords -> Int -> (Int, Int, Int, Int)
cornerIndices coords width =
  let idx00 = pixelIndex (bcX0 coords) (bcY0 coords) width
      idx10 = pixelIndex (bcX1 coords) (bcY0 coords) width
      idx01 = pixelIndex (bcX0 coords) (bcY1 coords) width
      idx11 = pixelIndex (bcX1 coords) (bcY1 coords) width
  in (idx00, idx10, idx01, idx11)

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
interpolateValue :: Double -> Double -> Double -> Double -> BilinearWeights -> Double
interpolateValue v00 v10 v01 v11 weights =
  v00 * bwW00 weights + v10 * bwW10 weights + v01 * bwW01 weights + v11 * bwW11 weights

-- | Interpolate and round to nearest integer (for 8-bit pixel values).
--
--   @param v00 v10 v01 v11 Corner values
--   @param weights Bilinear weights
--   @return Rounded interpolated value
interpolateRound :: Double -> Double -> Double -> Double -> BilinearWeights -> Int
interpolateRound v00 v10 v01 v11 weights =
  round (interpolateValue v00 v10 v01 v11 weights)
