{-
  Lattice.Services.Blur.Sharpen - Unsharp Mask Mathematics

  Pure mathematical functions for image sharpening:
  - Unsharp mask formula
  - High-pass filter simulation
  - Threshold application

  Unsharp masking: sharpened = original + amount * (original - blurred)

  Source: ui/src/services/effects/blurRenderer.ts (lines 1476-1487)
-}

module Lattice.Services.Blur.Sharpen
  ( unsharpMask
  , highPassComponent
  , exceedsThreshold
  , unsharpMaskWithThreshold
  , percentToMultiplier
  , clampAmount
  , edgeStrength
  , isEdgePixel
  , adaptiveAmount
  ) where

import Prelude

import Math (abs)

--------------------------------------------------------------------------------
-- Unsharp Mask
--------------------------------------------------------------------------------

-- | Apply unsharp mask formula to a single value.
--
--   Formula: sharpened = original + amount * (original - blurred)
unsharpMask :: Number -> Number -> Number -> Number
unsharpMask original blurred amount =
  let difference = original - blurred
      sharpened = original + difference * amount
  in max 0.0 (min 255.0 sharpened)

-- | Calculate the difference (high-pass) component.
highPassComponent :: Number -> Number -> Number
highPassComponent original blurred = original - blurred

--------------------------------------------------------------------------------
-- Threshold Application
--------------------------------------------------------------------------------

-- | Check if difference exceeds threshold.
exceedsThreshold :: Number -> Number -> Number -> Boolean
exceedsThreshold original blurred threshold =
  abs (original - blurred) >= threshold

-- | Apply unsharp mask with threshold.
unsharpMaskWithThreshold :: Number -> Number -> Number -> Number -> Number
unsharpMaskWithThreshold original blurred amount threshold
  | exceedsThreshold original blurred threshold = unsharpMask original blurred amount
  | otherwise = original

--------------------------------------------------------------------------------
-- Amount Conversion
--------------------------------------------------------------------------------

-- | Convert percentage amount to multiplier.
percentToMultiplier :: Number -> Number
percentToMultiplier percent = percent / 100.0

-- | Clamp amount to valid range.
clampAmount :: Number -> Number
clampAmount amount = max 0.0 (min 5.0 amount)

--------------------------------------------------------------------------------
-- Edge Detection Estimation
--------------------------------------------------------------------------------

-- | Estimate edge strength at a pixel.
edgeStrength :: Number -> Number -> Number
edgeStrength original blurred = abs (original - blurred)

-- | Check if pixel is likely on an edge.
isEdgePixel :: Number -> Number -> Number -> Boolean
isEdgePixel original blurred edgeThreshold =
  edgeStrength original blurred >= edgeThreshold

--------------------------------------------------------------------------------
-- Adaptive Sharpening
--------------------------------------------------------------------------------

-- | Calculate adaptive sharpening amount based on local contrast.
adaptiveAmount :: Number -> Number -> Number -> Number
adaptiveAmount original blurred baseAmount =
  let contrast = edgeStrength original blurred
      contrastNorm = min 1.0 (contrast / 128.0)
  in baseAmount * (1.0 - contrastNorm * 0.5)
