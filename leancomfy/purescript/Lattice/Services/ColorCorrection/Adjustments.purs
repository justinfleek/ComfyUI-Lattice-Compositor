-- | Lattice.Services.ColorCorrection.Adjustments - Pixel Adjustment Formulas
-- |
-- | Pure mathematical functions for color adjustment calculations:
-- | - Brightness/Contrast formulas
-- | - Levels mapping
-- | - Exposure calculation
-- | - Vibrance with skin protection
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts

module Lattice.Services.ColorCorrection.Adjustments
  ( contrastFactor
  , contrastFactorLegacy
  , applyBrightnessContrast
  , applyLevels
  , applyExposure
  , skinProtection
  , vibranceAmount
  , applySaturationAdjustment
  , shadowWeight
  , highlightWeight
  , midtoneWeight
  , posterize
  , threshold
  ) where

import Prelude

import Data.Int (toNumber, round) as Int
import Data.Tuple (Tuple(..))
import Math (abs, max, min, pow, round)

--------------------------------------------------------------------------------
-- Brightness & Contrast
--------------------------------------------------------------------------------

-- | Calculate contrast factor using standard formula.
-- |
-- | Formula: (259 * (c * 255 + 255)) / (255 * (259 - c * 255))
contrastFactor :: Number -> Number
contrastFactor contrast =
  let c255 = contrast * 255.0
  in (259.0 * (c255 + 255.0)) / (255.0 * (259.0 - c255))

-- | Legacy contrast factor (simple linear).
contrastFactorLegacy :: Number -> Number
contrastFactorLegacy contrast = 1.0 + contrast

-- | Apply brightness and contrast to a channel value.
applyBrightnessContrast :: Number -> Number -> Number -> Number
applyBrightnessContrast value brightness factor =
  let withBrightness = value + brightness * 255.0
      withContrast = factor * (withBrightness - 128.0) + 128.0
  in max 0.0 (min 255.0 withContrast)

--------------------------------------------------------------------------------
-- Levels
--------------------------------------------------------------------------------

-- | Apply levels adjustment.
applyLevels :: Number -> Number -> Number -> Number -> Number -> Number -> Number
applyLevels value inputBlack inputWhite gamma outputBlack outputWhite =
  let inputRange = inputWhite - inputBlack
      normalized = if inputRange < 0.01
                   then 0.0
                   else (value - inputBlack) / inputRange
      clamped = max 0.0 (min 1.0 normalized)
      gammaInv = 1.0 / gamma
      gammaCorrected = pow clamped gammaInv
      outputRange = outputWhite - outputBlack
      output = outputBlack + gammaCorrected * outputRange
  in max 0.0 (min 255.0 output)

--------------------------------------------------------------------------------
-- Exposure
--------------------------------------------------------------------------------

-- | Apply photographic exposure adjustment.
applyExposure :: Number -> Number -> Number -> Number -> Number
applyExposure value exposure offset gamma =
  let exposureMultiplier = pow 2.0 exposure
      withExposure = value * exposureMultiplier
      withOffset = withExposure + offset
      clamped = max 0.0 (min 1.0 withOffset)
      gammaInv = 1.0 / gamma
  in pow clamped gammaInv

--------------------------------------------------------------------------------
-- Vibrance
--------------------------------------------------------------------------------

-- | Calculate skin protection factor.
skinProtection :: Number -> Number -> Number -> Number
skinProtection r g b =
  let distance = abs (r - 0.8) * 2.0 +
                 abs (g - 0.5) * 2.0 +
                 abs (b - 0.3) * 3.0
  in 1.0 - max 0.0 (min 1.0 distance)

-- | Calculate adaptive vibrance adjustment.
vibranceAmount :: Number -> Number -> Number -> Number
vibranceAmount currentSat skinProt vibrance =
  vibrance * (1.0 - currentSat) * (1.0 - skinProt * 0.5)

-- | Apply saturation adjustment to RGB.
applySaturationAdjustment :: Number -> Number -> Number -> Number -> Number
                          -> Tuple Number (Tuple Number Number)
applySaturationAdjustment r g b lum satAdjust =
  let r' = lum + (r - lum) * satAdjust
      g' = lum + (g - lum) * satAdjust
      b' = lum + (b - lum) * satAdjust
  in Tuple (max 0.0 (min 1.0 r')) (Tuple (max 0.0 (min 1.0 g')) (max 0.0 (min 1.0 b')))

--------------------------------------------------------------------------------
-- Color Balance
--------------------------------------------------------------------------------

-- | Calculate shadow weight (peaks at luminance 0).
shadowWeight :: Number -> Number
shadowWeight luminance = max 0.0 (1.0 - luminance * 3.0)

-- | Calculate highlight weight (peaks at luminance 1).
highlightWeight :: Number -> Number
highlightWeight luminance = max 0.0 ((luminance - 0.67) * 3.0)

-- | Calculate midtone weight.
midtoneWeight :: Number -> Number -> Number
midtoneWeight shadowW highlightW = 1.0 - shadowW - highlightW

--------------------------------------------------------------------------------
-- Posterize
--------------------------------------------------------------------------------

-- | Calculate posterized value.
posterize :: Number -> Int -> Number
posterize value levels =
  if levels < 2 then value
  else
    let levelsF = Int.toNumber levels
        step = 255.0 / (levelsF - 1.0)
        level = round ((value / 255.0) * (levelsF - 1.0))
    in round (level * step)

--------------------------------------------------------------------------------
-- Threshold
--------------------------------------------------------------------------------

-- | Apply binary threshold.
threshold :: Number -> Number -> Number
threshold luminance thresh = if luminance >= thresh then 255.0 else 0.0
