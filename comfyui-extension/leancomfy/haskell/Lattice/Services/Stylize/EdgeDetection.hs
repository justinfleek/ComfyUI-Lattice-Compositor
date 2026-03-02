{-|
{-# LANGUAGE OverloadedStrings #-}
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

--------------------------------------------------------------------------------
-- Sobel Kernels
--------------------------------------------------------------------------------

-- | Sobel X kernel for horizontal gradient detection.
--
--   3x3 convolution kernel:
--   [-1  0  1]
--   [-2  0  2]
--   [-1  0  1]
--
--   @param kx Kernel X offset (-1, 0, or 1)
--   @param ky Kernel Y offset (-1, 0, or 1)
--   @return Kernel weight
sobelX :: Int -> Int -> Int
sobelX kx ky =
  let col = kx + 1  -- 0, 1, 2
      row = ky + 1  -- 0, 1, 2
  in case row of
       0 -> if col == 0 then -1 else if col == 1 then 0 else 1
       1 -> if col == 0 then -2 else if col == 1 then 0 else 2
       2 -> if col == 0 then -1 else if col == 1 then 0 else 1
       _ -> 0

-- | Sobel Y kernel for vertical gradient detection.
--
--   3x3 convolution kernel:
--   [-1 -2 -1]
--   [ 0  0  0]
--   [ 1  2  1]
--
--   @param kx Kernel X offset (-1, 0, or 1)
--   @param ky Kernel Y offset (-1, 0, or 1)
--   @return Kernel weight
sobelY :: Int -> Int -> Int
sobelY kx ky =
  let col = kx + 1  -- 0, 1, 2
      row = ky + 1  -- 0, 1, 2
  in case row of
       0 -> if col == 0 then -1 else if col == 1 then -2 else -1
       1 -> 0
       2 -> if col == 0 then 1 else if col == 1 then 2 else 1
       _ -> 0

-- | Get both Sobel kernel values at a position.
--
--   @param kx Kernel X offset (-1, 0, or 1)
--   @param ky Kernel Y offset (-1, 0, or 1)
--   @return (sobelX, sobelY) weights
sobelWeights :: Int -> Int -> (Int, Int)
sobelWeights kx ky = (sobelX kx ky, sobelY kx ky)

--------------------------------------------------------------------------------
-- Gradient Calculation
--------------------------------------------------------------------------------

-- | Calculate gradient magnitude from X and Y components.
--
--   magnitude = sqrt(gx² + gy²)
--
--   @param gx X gradient component
--   @param gy Y gradient component
--   @return Gradient magnitude
gradientMagnitude :: Double -> Double -> Double
gradientMagnitude gx gy = sqrt (gx * gx + gy * gy)

-- | Calculate gradient direction in radians.
--
--   @param gx X gradient component
--   @param gy Y gradient component
--   @return Angle in radians [-π, π]
gradientDirection :: Double -> Double -> Double
gradientDirection gx gy = atan2 gy gx

-- | Apply inversion to edge magnitude.
--
--   Inverted edges show bright on dark instead of dark on bright.
--
--   @param magnitude Edge magnitude
--   @param invert Whether to invert
--   @return Adjusted magnitude
applyInversion :: Double -> Bool -> Double
applyInversion magnitude invert =
  if invert then 255.0 - magnitude else magnitude

-- | Blend edge magnitude with original pixel value.
--
--   @param edgeMag Edge magnitude (0-255)
--   @param original Original pixel value (0-255)
--   @param blend Blend factor (0 = all edge, 1 = all original)
--   @return Blended value
blendWithOriginal :: Double -> Double -> Double -> Double
blendWithOriginal edgeMag original blend =
  min 255.0 (edgeMag * (1.0 - blend) + original * blend)

--------------------------------------------------------------------------------
-- Emboss
--------------------------------------------------------------------------------

-- | Calculate emboss sample offset from light direction.
--
--   @param directionDeg Light direction in degrees
--   @param height Emboss depth
--   @return (dx, dy) sample offset
embossOffset :: Double -> Double -> (Int, Int)
embossOffset directionDeg height =
  let direction = directionDeg * pi / 180.0
      dx = round (cos direction * height)
      dy = round (sin direction * height)
  in (dx, dy)

-- | Calculate emboss value from sample difference.
--
--   Emboss creates relief effect by comparing offset pixels.
--   Result is centered at 128 (gray).
--
--   @param sample1 First sample value
--   @param sample2 Second sample value (opposite offset)
--   @param factor Intensity factor (amount / 100)
--   @return Embossed value centered at 128
embossValue :: Double -> Double -> Double -> Double
embossValue sample1 sample2 factor =
  let diff = (sample1 - sample2) * factor
  in max 0.0 (min 255.0 (128.0 + diff))

--------------------------------------------------------------------------------
-- Kernel Index Helpers
--------------------------------------------------------------------------------

-- | Convert kernel offset (-1, 0, 1) to flat index (0-8).
--
--   Layout: 0 1 2
--           3 4 5
--           6 7 8
--
--   @param kx X offset (-1, 0, 1)
--   @param ky Y offset (-1, 0, 1)
--   @return Flat index (0-8)
kernelIndex :: Int -> Int -> Int
kernelIndex kx ky =
  let row = ky + 1
      col = kx + 1
  in row * 3 + col
