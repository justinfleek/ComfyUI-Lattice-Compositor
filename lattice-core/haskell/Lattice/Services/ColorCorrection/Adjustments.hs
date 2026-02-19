{-|
Module      : Lattice.Services.ColorCorrection.Adjustments
Description : Pixel Adjustment Formulas
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for color adjustment calculations:
- Brightness/Contrast formulas
- Levels mapping
- Exposure calculation
- Vibrance with skin protection

All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts
-}

module Lattice.Services.ColorCorrection.Adjustments
  ( -- * Brightness & Contrast
    contrastFactor
  , contrastFactorLegacy
  , applyBrightnessContrast
    -- * Levels
  , applyLevels
    -- * Exposure
  , applyExposure
    -- * Vibrance
  , skinProtection
  , vibranceAmount
  , applySaturationAdjustment
    -- * Color Balance
  , shadowWeight
  , highlightWeight
  , midtoneWeight
    -- * Posterize
  , posterize
    -- * Threshold
  , threshold
  ) where

--------------------------------------------------------------------------------
-- Brightness & Contrast
--------------------------------------------------------------------------------

-- | Calculate contrast factor using standard formula.
--
-- Formula: (259 * (c * 255 + 255)) / (255 * (259 - c * 255))
contrastFactor :: Double -> Double
contrastFactor contrast =
  let c255 = contrast * 255
  in (259 * (c255 + 255)) / (255 * (259 - c255))

-- | Legacy contrast factor (simple linear).
contrastFactorLegacy :: Double -> Double
contrastFactorLegacy contrast = 1 + contrast

-- | Apply brightness and contrast to a channel value.
applyBrightnessContrast :: Double  -- ^ value (0-255)
                        -> Double  -- ^ brightness (-1 to 1)
                        -> Double  -- ^ factor (from contrastFactor)
                        -> Double  -- ^ result (0-255)
applyBrightnessContrast value brightness factor =
  let withBrightness = value + brightness * 255
      withContrast = factor * (withBrightness - 128) + 128
  in max 0 (min 255 withContrast)

--------------------------------------------------------------------------------
-- Levels
--------------------------------------------------------------------------------

-- | Apply levels adjustment.
applyLevels :: Double  -- ^ value (0-255)
            -> Double  -- ^ inputBlack (0-255)
            -> Double  -- ^ inputWhite (0-255)
            -> Double  -- ^ gamma (0.01-10)
            -> Double  -- ^ outputBlack (0-255)
            -> Double  -- ^ outputWhite (0-255)
            -> Double  -- ^ result (0-255)
applyLevels value inputBlack inputWhite gamma outputBlack outputWhite =
  let inputRange = inputWhite - inputBlack
      normalized = if inputRange < 0.01
                   then 0
                   else (value - inputBlack) / inputRange
      clamped = max 0 (min 1 normalized)
      gammaInv = 1 / gamma
      gammaCorrected = clamped ** gammaInv
      outputRange = outputWhite - outputBlack
      output = outputBlack + gammaCorrected * outputRange
  in max 0 (min 255 output)

--------------------------------------------------------------------------------
-- Exposure
--------------------------------------------------------------------------------

-- | Apply photographic exposure adjustment.
applyExposure :: Double  -- ^ value (0-1)
              -> Double  -- ^ exposure (stops)
              -> Double  -- ^ offset
              -> Double  -- ^ gamma
              -> Double  -- ^ result (0-1)
applyExposure value exposure offset gamma =
  let exposureMultiplier = 2 ** exposure
      withExposure = value * exposureMultiplier
      withOffset = withExposure + offset
      clamped = max 0 (min 1 withOffset)
      gammaInv = 1 / gamma
  in clamped ** gammaInv

--------------------------------------------------------------------------------
-- Vibrance
--------------------------------------------------------------------------------

-- | Calculate skin protection factor.
skinProtection :: Double -> Double -> Double -> Double
skinProtection r g b =
  let distance = abs (r - 0.8) * 2 +
                 abs (g - 0.5) * 2 +
                 abs (b - 0.3) * 3
  in 1 - max 0 (min 1 distance)

-- | Calculate adaptive vibrance adjustment.
vibranceAmount :: Double  -- ^ currentSaturation
               -> Double  -- ^ skinProtectionFactor
               -> Double  -- ^ vibrance
               -> Double
vibranceAmount currentSat skinProt vibrance =
  vibrance * (1 - currentSat) * (1 - skinProt * 0.5)

-- | Apply saturation adjustment to RGB.
applySaturationAdjustment :: Double  -- ^ r (0-1)
                          -> Double  -- ^ g (0-1)
                          -> Double  -- ^ b (0-1)
                          -> Double  -- ^ luminance (0-1)
                          -> Double  -- ^ satAdjust
                          -> (Double, Double, Double)
applySaturationAdjustment r g b lum satAdjust =
  let r' = lum + (r - lum) * satAdjust
      g' = lum + (g - lum) * satAdjust
      b' = lum + (b - lum) * satAdjust
  in (max 0 (min 1 r'), max 0 (min 1 g'), max 0 (min 1 b'))

--------------------------------------------------------------------------------
-- Color Balance
--------------------------------------------------------------------------------

-- | Calculate shadow weight (peaks at luminance 0).
shadowWeight :: Double -> Double
shadowWeight luminance = max 0 (1 - luminance * 3)

-- | Calculate highlight weight (peaks at luminance 1).
highlightWeight :: Double -> Double
highlightWeight luminance = max 0 ((luminance - 0.67) * 3)

-- | Calculate midtone weight.
midtoneWeight :: Double -> Double -> Double
midtoneWeight shadowW highlightW = 1 - shadowW - highlightW

--------------------------------------------------------------------------------
-- Posterize
--------------------------------------------------------------------------------

-- | Calculate posterized value.
posterize :: Double -> Int -> Double
posterize value levels
  | levels < 2 = value
  | otherwise =
      let levelsF = fromIntegral levels :: Double
          step = 255 / (levelsF - 1)
          level = fromIntegral (round ((value / 255) * (levelsF - 1)) :: Int)
      in fromIntegral (round (level * step) :: Int)

--------------------------------------------------------------------------------
-- Threshold
--------------------------------------------------------------------------------

-- | Apply binary threshold.
threshold :: Double -> Double -> Double
threshold luminance thresh = if luminance >= thresh then 255 else 0
