{-
  Lattice.Services.Stylize.EdgeDetection - Edge Detection Mathematics

  Pure mathematical functions for edge detection:
  - Sobel operator kernels
  - Gradient magnitude calculation
  - Emboss direction vectors

  Source: ui/src/services/effects/stylizeRenderer.ts (lines 1065-1210)
-}

module Lattice.Services.Stylize.EdgeDetection
  ( sobelX
  , sobelY
  , sobelWeights
  , gradientMagnitude
  , gradientDirection
  , applyInversion
  , blendWithOriginal
  , embossOffset
  , embossValue
  , kernelIndex
  ) where

import Prelude

import Data.Int (round) as Int
import Data.Tuple (Tuple(..))
import Math (atan2, cos, pi, sin, sqrt)

--------------------------------------------------------------------------------
-- Sobel Kernels
--------------------------------------------------------------------------------

-- | Sobel X kernel for horizontal gradient detection.
sobelX :: Int -> Int -> Int
sobelX kx ky =
  let col = kx + 1
      row = ky + 1
  in case row of
       0 -> if col == 0 then -1 else if col == 1 then 0 else 1
       1 -> if col == 0 then -2 else if col == 1 then 0 else 2
       2 -> if col == 0 then -1 else if col == 1 then 0 else 1
       _ -> 0

-- | Sobel Y kernel for vertical gradient detection.
sobelY :: Int -> Int -> Int
sobelY kx ky =
  let col = kx + 1
      row = ky + 1
  in case row of
       0 -> if col == 0 then -1 else if col == 1 then -2 else -1
       1 -> 0
       2 -> if col == 0 then 1 else if col == 1 then 2 else 1
       _ -> 0

-- | Get both Sobel kernel values at a position.
sobelWeights :: Int -> Int -> Tuple Int Int
sobelWeights kx ky = Tuple (sobelX kx ky) (sobelY kx ky)

--------------------------------------------------------------------------------
-- Gradient Calculation
--------------------------------------------------------------------------------

-- | Calculate gradient magnitude from X and Y components.
gradientMagnitude :: Number -> Number -> Number
gradientMagnitude gx gy = sqrt (gx * gx + gy * gy)

-- | Calculate gradient direction in radians.
gradientDirection :: Number -> Number -> Number
gradientDirection gx gy = atan2 gy gx

-- | Apply inversion to edge magnitude.
applyInversion :: Number -> Boolean -> Number
applyInversion magnitude invert =
  if invert then 255.0 - magnitude else magnitude

-- | Blend edge magnitude with original pixel value.
blendWithOriginal :: Number -> Number -> Number -> Number
blendWithOriginal edgeMag original blend =
  min 255.0 (edgeMag * (1.0 - blend) + original * blend)

--------------------------------------------------------------------------------
-- Emboss
--------------------------------------------------------------------------------

-- | Calculate emboss sample offset from light direction.
embossOffset :: Number -> Number -> Tuple Int Int
embossOffset directionDeg height =
  let direction = directionDeg * pi / 180.0
      dx = Int.round (cos direction * height)
      dy = Int.round (sin direction * height)
  in Tuple dx dy

-- | Calculate emboss value from sample difference.
embossValue :: Number -> Number -> Number -> Number
embossValue sample1 sample2 factor =
  let diff = (sample1 - sample2) * factor
  in max 0.0 (min 255.0 (128.0 + diff))

--------------------------------------------------------------------------------
-- Kernel Index Helpers
--------------------------------------------------------------------------------

-- | Convert kernel offset (-1, 0, 1) to flat index (0-8).
kernelIndex :: Int -> Int -> Int
kernelIndex kx ky =
  let row = ky + 1
      col = kx + 1
  in row * 3 + col
