{-
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
  , FloydSteinbergCoeffs
  , floydSteinbergCoeffs
  , distributeErrorFS
  , atkinsonErrorPerNeighbor
  , atkinsonOffsets
  ) where

import Prelude

import Data.Array ((!!) )
import Data.Int (round, toNumber) as Int
import Data.Maybe (fromMaybe)
import Data.Tuple (Tuple(..))

--------------------------------------------------------------------------------
-- Dither Method Types
--------------------------------------------------------------------------------

-- | Dithering algorithm type
data DitherMethod
  = Ordered          -- Bayer matrix ordered dithering
  | FloydSteinberg   -- Floyd-Steinberg error diffusion
  | Atkinson         -- Atkinson error diffusion

derive instance eqDitherMethod :: Eq DitherMethod

instance showDitherMethod :: Show DitherMethod where
  show Ordered = "Ordered"
  show FloydSteinberg = "FloydSteinberg"
  show Atkinson = "Atkinson"

--------------------------------------------------------------------------------
-- Bayer Matrices
--------------------------------------------------------------------------------

-- | Bayer 2x2 matrix values (divide by 4 for threshold).
bayer2 :: Int -> Int -> Int
bayer2 x y =
  let row = y `mod` 2
      col = x `mod` 2
  in if row == 0
     then if col == 0 then 0 else 2
     else if col == 0 then 3 else 1

-- | Bayer 4x4 matrix
bayer4Matrix :: Array (Array Int)
bayer4Matrix =
  [ [0, 8, 2, 10]
  , [12, 4, 14, 6]
  , [3, 11, 1, 9]
  , [15, 7, 13, 5]
  ]

-- | Bayer 4x4 matrix values (divide by 16 for threshold).
bayer4 :: Int -> Int -> Int
bayer4 x y =
  let row = y `mod` 4
      col = x `mod` 4
      rowArr = fromMaybe [] (bayer4Matrix !! row)
  in fromMaybe 0 (rowArr !! col)

-- | Bayer 8x8 matrix
bayer8Matrix :: Array (Array Int)
bayer8Matrix =
  [ [0, 32, 8, 40, 2, 34, 10, 42]
  , [48, 16, 56, 24, 50, 18, 58, 26]
  , [12, 44, 4, 36, 14, 46, 6, 38]
  , [60, 28, 52, 20, 62, 30, 54, 22]
  , [3, 35, 11, 43, 1, 33, 9, 41]
  , [51, 19, 59, 27, 49, 17, 57, 25]
  , [15, 47, 7, 39, 13, 45, 5, 37]
  , [63, 31, 55, 23, 61, 29, 53, 21]
  ]

-- | Bayer 8x8 matrix values (divide by 64 for threshold).
bayer8 :: Int -> Int -> Int
bayer8 x y =
  let row = y `mod` 8
      col = x `mod` 8
      rowArr = fromMaybe [] (bayer8Matrix !! row)
  in fromMaybe 0 (rowArr !! col)

-- | Get Bayer matrix value for any supported size (2, 4, or 8).
bayerValue :: Int -> Int -> Int -> Int
bayerValue matrixSize x y
  | matrixSize == 2 = bayer2 x y
  | matrixSize == 8 = bayer8 x y
  | otherwise       = bayer4 x y

--------------------------------------------------------------------------------
-- Ordered Dithering
--------------------------------------------------------------------------------

-- | Calculate ordered dithering threshold offset.
orderedThreshold :: Int -> Int -> Int -> Int -> Number
orderedThreshold x y matrixSize levels =
  let matrixMax = Int.toNumber (matrixSize * matrixSize)
      matrixVal = Int.toNumber (bayerValue matrixSize x y)
  in (matrixVal / matrixMax - 0.5) * (256.0 / Int.toNumber levels)

--------------------------------------------------------------------------------
-- Quantization
--------------------------------------------------------------------------------

-- | Quantize a color value to a reduced number of levels.
quantize :: Number -> Int -> Number
quantize val levels =
  let step = 255.0 / Int.toNumber (levels - 1)
  in Int.toNumber (Int.round (val / step)) * step

-- | Clamp value to 0-255 range.
clamp255 :: Number -> Number
clamp255 val = max 0.0 (min 255.0 val)

--------------------------------------------------------------------------------
-- Floyd-Steinberg Error Diffusion
--------------------------------------------------------------------------------

-- | Floyd-Steinberg error distribution coefficients.
type FloydSteinbergCoeffs =
  { right       :: Number
  , bottomLeft  :: Number
  , bottom      :: Number
  , bottomRight :: Number
  }

-- | Standard Floyd-Steinberg coefficients
floydSteinbergCoeffs :: FloydSteinbergCoeffs
floydSteinbergCoeffs =
  { right:       7.0 / 16.0
  , bottomLeft:  3.0 / 16.0
  , bottom:      5.0 / 16.0
  , bottomRight: 1.0 / 16.0
  }

-- | Calculate distributed error for Floyd-Steinberg.
distributeErrorFS :: Number -> { right :: Number, bottomLeft :: Number, bottom :: Number, bottomRight :: Number }
distributeErrorFS err =
  let c = floydSteinbergCoeffs
  in { right:       err * c.right
     , bottomLeft:  err * c.bottomLeft
     , bottom:      err * c.bottom
     , bottomRight: err * c.bottomRight
     }

--------------------------------------------------------------------------------
-- Atkinson Error Diffusion
--------------------------------------------------------------------------------

-- | Atkinson error distribution.
atkinsonErrorPerNeighbor :: Number -> Number
atkinsonErrorPerNeighbor err = err / 8.0

-- | Atkinson neighbor offsets relative to current pixel.
atkinsonOffsets :: Array (Tuple Int Int)
atkinsonOffsets =
  [ Tuple 1 0
  , Tuple 2 0
  , Tuple (-1) 1
  , Tuple 0 1
  , Tuple 1 1
  , Tuple 0 2
  ]
