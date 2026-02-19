{-|
  Lattice.Services.Blur.Sharpen - Unsharp Mask Mathematics

  Pure mathematical functions for image sharpening:
  - Unsharp mask formula
  - High-pass filter simulation
  - Threshold application

  Unsharp masking: sharpened = original + amount * (original - blurred)

  Source: ui/src/services/effects/blurRenderer.ts (lines 1476-1487)
-}

module Lattice.Services.Blur.Sharpen
  ( -- * Unsharp Mask
    unsharpMask
  , highPassComponent
    -- * Threshold Application
  , exceedsThreshold
  , unsharpMaskWithThreshold
    -- * Amount Conversion
  , percentToMultiplier
  , clampAmount
    -- * Edge Detection Estimation
  , edgeStrength
  , isEdgePixel
    -- * Adaptive Sharpening
  , adaptiveAmount
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Unsharp Mask
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply unsharp mask formula to a single value.
--
--   Formula: sharpened = original + amount * (original - blurred)
--
--   This enhances edges by amplifying the difference between
--   original and blurred (which represents high-frequency detail).
--
--   @param original Original pixel value (0-255)
--   @param blurred Blurred pixel value (0-255)
--   @param amount Sharpening amount (0-5, where 1 = 100%)
--   @return Sharpened value (clamped to 0-255)
unsharpMask :: Double -> Double -> Double -> Double
unsharpMask original blurred amount =
  let difference = original - blurred
      sharpened = original + difference * amount
  in max 0.0 (min 255.0 sharpened)

-- | Calculate the difference (high-pass) component.
--
--   This represents the edge/detail information that will be amplified.
--
--   @param original Original value
--   @param blurred Blurred value
--   @return Difference (can be negative)
highPassComponent :: Double -> Double -> Double
highPassComponent original blurred = original - blurred

-- ────────────────────────────────────────────────────────────────────────────
-- Threshold Application
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if difference exceeds threshold.
--
--   Thresholding prevents sharpening of subtle noise/texture.
--
--   @param original Original value
--   @param blurred Blurred value
--   @param threshold Minimum difference to sharpen
--   @return True if should be sharpened
exceedsThreshold :: Double -> Double -> Double -> Bool
exceedsThreshold original blurred threshold =
  abs (original - blurred) >= threshold

-- | Apply unsharp mask with threshold.
--
--   Only applies sharpening when the difference exceeds threshold.
--
--   @param original Original pixel value
--   @param blurred Blurred pixel value
--   @param amount Sharpening amount
--   @param threshold Minimum difference to sharpen
--   @return Sharpened value (or original if below threshold)
unsharpMaskWithThreshold :: Double -> Double -> Double -> Double -> Double
unsharpMaskWithThreshold original blurred amount threshold
  | exceedsThreshold original blurred threshold = unsharpMask original blurred amount
  | otherwise = original

-- ────────────────────────────────────────────────────────────────────────────
-- Amount Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert percentage amount to multiplier.
--
--   100% = 1.0 multiplier (normal sharpening)
--   200% = 2.0 multiplier (aggressive sharpening)
--
--   @param percent Amount as percentage (0-500)
--   @return Multiplier (0-5)
percentToMultiplier :: Double -> Double
percentToMultiplier percent = percent / 100.0

-- | Clamp amount to valid range.
--
--   @param amount Raw amount
--   @return Clamped amount (0-5)
clampAmount :: Double -> Double
clampAmount amount = max 0.0 (min 5.0 amount)

-- ────────────────────────────────────────────────────────────────────────────
-- Edge Detection Estimation
-- ────────────────────────────────────────────────────────────────────────────

-- | Estimate edge strength at a pixel.
--
--   This is a simplified measure based on how different
--   the pixel is from its blurred neighborhood.
--
--   @param original Original value
--   @param blurred Blurred value
--   @return Edge strength (0-255)
edgeStrength :: Double -> Double -> Double
edgeStrength original blurred = abs (original - blurred)

-- | Check if pixel is likely on an edge.
--
--   @param original Original value
--   @param blurred Blurred value
--   @param edgeThreshold Minimum difference to consider as edge
--   @return True if on edge
isEdgePixel :: Double -> Double -> Double -> Bool
isEdgePixel original blurred edgeThreshold =
  edgeStrength original blurred >= edgeThreshold

-- ────────────────────────────────────────────────────────────────────────────
-- Adaptive Sharpening
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate adaptive sharpening amount based on local contrast.
--
--   Areas with more contrast (edges) get less additional sharpening
--   to prevent over-sharpening. Flat areas get more.
--
--   @param original Original value
--   @param blurred Blurred value
--   @param baseAmount Base sharpening amount
--   @return Adapted amount
adaptiveAmount :: Double -> Double -> Double -> Double
adaptiveAmount original blurred baseAmount =
  let contrast = edgeStrength original blurred
      contrastNorm = min 1.0 (contrast / 128.0)  -- Normalize to 0-1
      -- Reduce amount for high contrast areas
  in baseAmount * (1.0 - contrastNorm * 0.5)
