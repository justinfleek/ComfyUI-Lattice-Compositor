{-|
{-# LANGUAGE OverloadedStrings #-}
  Lattice.Services.Stylize.Dither - Dithering Mathematics

  Pure mathematical functions for dithering:
  - Bayer matrices (2x2, 4x4, 8x8)
  - Ordered dithering threshold calculation
  - Color quantization
  - Error diffusion coefficients

  Source: ui/src/services/effects/stylizeRenderer.ts (lines 790-948)
-}

module Lattice.Services.Stylize.Dither
  ( DitherMethod(..)
  , bayer2
  , bayer4
  , bayer8
  , bayerValue
  , orderedThreshold
  , quantize
  , clamp255
  , FloydSteinbergCoeffs(..)
  , floydSteinbergCoeffs
  , distributeErrorFS
  , atkinsonErrorPerNeighbor
  , atkinsonOffsets
  ) where

import Data.Array ((!), listArray, Array)

--------------------------------------------------------------------------------
-- Dither Method Types
--------------------------------------------------------------------------------

-- | Dithering algorithm type
data DitherMethod
  = Ordered          -- ^ Bayer matrix ordered dithering
  | FloydSteinberg   -- ^ Floyd-Steinberg error diffusion
  | Atkinson         -- ^ Atkinson error diffusion
  deriving (Show, Eq, Enum, Bounded)

--------------------------------------------------------------------------------
-- Bayer Matrices
--------------------------------------------------------------------------------

-- | Bayer 2x2 matrix values (divide by 4 for threshold).
--   Pattern: [[0, 2], [3, 1]]
bayer2 :: Int -> Int -> Int
bayer2 x y =
  let row = y `mod` 2
      col = x `mod` 2
  in if row == 0
     then if col == 0 then 0 else 2
     else if col == 0 then 3 else 1

-- | Bayer 4x4 matrix as array
bayer4Matrix :: Array (Int, Int) Int
bayer4Matrix = listArray ((0,0), (3,3))
  [ 0, 8, 2, 10
  , 12, 4, 14, 6
  , 3, 11, 1, 9
  , 15, 7, 13, 5
  ]

-- | Bayer 4x4 matrix values (divide by 16 for threshold).
bayer4 :: Int -> Int -> Int
bayer4 x y = bayer4Matrix ! (y `mod` 4, x `mod` 4)

-- | Bayer 8x8 matrix as array
bayer8Matrix :: Array (Int, Int) Int
bayer8Matrix = listArray ((0,0), (7,7))
  [ 0, 32, 8, 40, 2, 34, 10, 42
  , 48, 16, 56, 24, 50, 18, 58, 26
  , 12, 44, 4, 36, 14, 46, 6, 38
  , 60, 28, 52, 20, 62, 30, 54, 22
  , 3, 35, 11, 43, 1, 33, 9, 41
  , 51, 19, 59, 27, 49, 17, 57, 25
  , 15, 47, 7, 39, 13, 45, 5, 37
  , 63, 31, 55, 23, 61, 29, 53, 21
  ]

-- | Bayer 8x8 matrix values (divide by 64 for threshold).
bayer8 :: Int -> Int -> Int
bayer8 x y = bayer8Matrix ! (y `mod` 8, x `mod` 8)

-- | Get Bayer matrix value for any supported size (2, 4, or 8).
--
--   @param matrixSize Size of matrix (2, 4, or 8)
--   @param x X coordinate
--   @param y Y coordinate
--   @return Matrix value at position
bayerValue :: Int -> Int -> Int -> Int
bayerValue matrixSize x y
  | matrixSize == 2 = bayer2 x y
  | matrixSize == 8 = bayer8 x y
  | otherwise       = bayer4 x y

--------------------------------------------------------------------------------
-- Ordered Dithering
--------------------------------------------------------------------------------

-- | Calculate ordered dithering threshold offset.
--
--   @param x X coordinate
--   @param y Y coordinate
--   @param matrixSize Bayer matrix size (2, 4, or 8)
--   @param levels Number of color levels
--   @return Threshold offset to add to pixel value before quantization
orderedThreshold :: Int -> Int -> Int -> Int -> Double
orderedThreshold x y matrixSize levels =
  let matrixMax = fromIntegral (matrixSize * matrixSize) :: Double
      matrixVal = fromIntegral (bayerValue matrixSize x y) :: Double
  in (matrixVal / matrixMax - 0.5) * (256.0 / fromIntegral levels)

--------------------------------------------------------------------------------
-- Quantization
--------------------------------------------------------------------------------

-- | Quantize a color value to a reduced number of levels.
--
--   @param val Original value (0-255)
--   @param levels Number of output levels (2-256)
--   @return Quantized value (0-255)
quantize :: Double -> Int -> Double
quantize val levels =
  let step = 255.0 / fromIntegral (levels - 1)
  in fromIntegral (round (val / step) :: Int) * step

-- | Clamp value to 0-255 range.
--
--   @param val Input value
--   @return Clamped value in [0, 255]
clamp255 :: Double -> Double
clamp255 val = max 0.0 (min 255.0 val)

--------------------------------------------------------------------------------
-- Floyd-Steinberg Error Diffusion
--------------------------------------------------------------------------------

-- | Floyd-Steinberg error distribution coefficients.
data FloydSteinbergCoeffs = FloydSteinbergCoeffs
  { fsRight       :: !Double  -- ^ 7/16
  , fsBottomLeft  :: !Double  -- ^ 3/16
  , fsBottom      :: !Double  -- ^ 5/16
  , fsBottomRight :: !Double  -- ^ 1/16
  } deriving (Show, Eq)

-- | Standard Floyd-Steinberg coefficients
floydSteinbergCoeffs :: FloydSteinbergCoeffs
floydSteinbergCoeffs = FloydSteinbergCoeffs
  { fsRight       = 7.0 / 16.0
  , fsBottomLeft  = 3.0 / 16.0
  , fsBottom      = 5.0 / 16.0
  , fsBottomRight = 1.0 / 16.0
  }

-- | Calculate distributed error for Floyd-Steinberg.
--
--   @param error The quantization error (oldVal - newVal)
--   @return (right, bottomLeft, bottom, bottomRight) errors
distributeErrorFS :: Double -> (Double, Double, Double, Double)
distributeErrorFS err =
  let c = floydSteinbergCoeffs
  in (err * fsRight c, err * fsBottomLeft c, err * fsBottom c, err * fsBottomRight c)

--------------------------------------------------------------------------------
-- Atkinson Error Diffusion
--------------------------------------------------------------------------------

-- | Atkinson error distribution.
--
--   Distributes only 6/8 of error (more contrast than Floyd-Steinberg).
--   Each of 6 neighbors gets 1/8 of error.
--
--   @param error The quantization error
--   @return Error per neighbor (same for all 6)
atkinsonErrorPerNeighbor :: Double -> Double
atkinsonErrorPerNeighbor err = err / 8.0

-- | Atkinson neighbor offsets relative to current pixel.
--
--   Returns list of (dx, dy) offsets for the 6 neighbors.
atkinsonOffsets :: [(Int, Int)]
atkinsonOffsets = [(1, 0), (2, 0), (-1, 1), (0, 1), (1, 1), (0, 2)]
