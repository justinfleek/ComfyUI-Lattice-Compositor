{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Effects.ColorCorrection
Description : Basic Color Correction Functions
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for color correction:
- Brightness & Contrast
- Levels (input/output with gamma)
- Exposure (photographic stops)

All functions operate on normalized [0,1] color values.
All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Effects.ColorCorrection
  ( -- * Types
    ColorParams(..)
  , LevelsParams(..)
  , ExposureParams(..)
    -- * Default Values
  , defaultColorParams
  , defaultLevelsParams
  , defaultExposureParams
    -- * Color Correction Functions
  , brightnessContrast
  , brightnessContrastPixel
  , levels
  , levelsPixel
  , exposure
  , exposurePixel
    -- * Lookup Table Generation
  , buildBrightnessContrastLUT
  , buildLevelsLUT
  , buildExposureLUT
  ) where

import Data.Word (Word8)
import qualified Data.Vector.Unboxed as V

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Brightness/Contrast parameters
data ColorParams = ColorParams
  { cpBrightness :: !Double  -- ^ -1.5 to 1.5 (normalized from -150 to 150)
  , cpContrast   :: !Double  -- ^ -1.0 to 1.0 (normalized from -100 to 100)
  , cpUseLegacy  :: !Bool    -- ^ Use legacy (simpler) contrast formula
  } deriving (Eq, Show)

-- | Levels parameters
data LevelsParams = LevelsParams
  { lpInputBlack  :: !Double  -- ^ 0-1 (normalized from 0-255)
  , lpInputWhite  :: !Double  -- ^ 0-1 (normalized from 0-255)
  , lpGamma       :: !Double  -- ^ 0.01-10 (gamma correction)
  , lpOutputBlack :: !Double  -- ^ 0-1 (normalized from 0-255)
  , lpOutputWhite :: !Double  -- ^ 0-1 (normalized from 0-255)
  } deriving (Eq, Show)

-- | Exposure parameters
data ExposureParams = ExposureParams
  { epExposure :: !Double  -- ^ -5 to 5 stops
  , epOffset   :: !Double  -- ^ -1 to 1 (additive)
  , epGamma    :: !Double  -- ^ 0.1 to 10 (gamma correction)
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default brightness/contrast (no change)
defaultColorParams :: ColorParams
defaultColorParams = ColorParams
  { cpBrightness = 0
  , cpContrast = 0
  , cpUseLegacy = False
  }

-- | Default levels (identity mapping)
defaultLevelsParams :: LevelsParams
defaultLevelsParams = LevelsParams
  { lpInputBlack = 0
  , lpInputWhite = 1
  , lpGamma = 1
  , lpOutputBlack = 0
  , lpOutputWhite = 1
  }

-- | Default exposure (no change)
defaultExposureParams :: ExposureParams
defaultExposureParams = ExposureParams
  { epExposure = 0
  , epOffset = 0
  , epGamma = 1
  }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1]
clamp01 :: Double -> Double
clamp01 = max 0 . min 1

-- | Clamp value to [0, 255]
clamp255 :: Double -> Double
clamp255 = max 0 . min 255

-- | Safe division with fallback
safeDiv :: Double -> Double -> Double -> Double
safeDiv _ 0 fallback = fallback
safeDiv a b _ = a / b

--------------------------------------------------------------------------------
-- Brightness & Contrast
--------------------------------------------------------------------------------

-- | Calculate contrast factor based on mode.
--
--   Legacy mode: factor = 1 + contrast
--   Standard mode: factor = (259 * (c * 255 + 255)) / (255 * (259 - c * 255))
--   where c is contrast in [-1, 1]
contrastFactor :: Bool -> Double -> Double
contrastFactor True contrast = 1 + contrast
contrastFactor False contrast =
  let c255 = contrast * 255
  in safeDiv (259 * (c255 + 255)) (255 * (259 - c255)) 1.0

-- | Apply brightness and contrast to a single pixel value [0,1].
brightnessContrastPixel :: ColorParams -> Double -> Double
brightnessContrastPixel params value =
  let brightness = cpBrightness params
      contrast = cpContrast params
      factor = contrastFactor (cpUseLegacy params) contrast
      -- Add brightness
      withBrightness = value + brightness
      -- Apply contrast (centered at 0.5)
      withContrast = factor * (withBrightness - 0.5) + 0.5
  in clamp01 withContrast

-- | Apply brightness and contrast to RGB tuple.
brightnessContrast :: ColorParams -> (Double, Double, Double) -> (Double, Double, Double)
brightnessContrast params (r, g, b) =
  ( brightnessContrastPixel params r
  , brightnessContrastPixel params g
  , brightnessContrastPixel params b
  )

-- | Build 256-entry lookup table for brightness/contrast.
buildBrightnessContrastLUT :: ColorParams -> V.Vector Word8
buildBrightnessContrastLUT params =
  V.generate 256 $ \i ->
    let normalized = fromIntegral i / 255
        result = brightnessContrastPixel params normalized
    in round (clamp255 (result * 255))

--------------------------------------------------------------------------------
-- Levels
--------------------------------------------------------------------------------

-- | Apply levels adjustment to a single pixel value [0,1].
--
--   Steps:
--   1. Map input range [inputBlack, inputWhite] to [0, 1]
--   2. Apply gamma correction: value^(1/gamma)
--   3. Map [0, 1] to output range [outputBlack, outputWhite]
levelsPixel :: LevelsParams -> Double -> Double
levelsPixel params value =
  let inputBlack = lpInputBlack params
      inputWhite = lpInputWhite params
      gamma = max 0.01 (lpGamma params)
      outputBlack = lpOutputBlack params
      outputWhite = lpOutputWhite params
      inputRange = inputWhite - inputBlack
      outputRange = outputWhite - outputBlack
      -- Step 1: Input levels
      mapped = safeDiv (value - inputBlack) inputRange 0
      clamped = clamp01 mapped
      -- Step 2: Gamma correction
      gammaApplied = clamped ** (1 / gamma)
      -- Step 3: Output levels
      output = outputBlack + gammaApplied * outputRange
  in clamp01 output

-- | Apply levels to RGB tuple.
levels :: LevelsParams -> (Double, Double, Double) -> (Double, Double, Double)
levels params (r, g, b) =
  ( levelsPixel params r
  , levelsPixel params g
  , levelsPixel params b
  )

-- | Build 256-entry lookup table for levels.
buildLevelsLUT :: LevelsParams -> V.Vector Word8
buildLevelsLUT params =
  V.generate 256 $ \i ->
    let normalized = fromIntegral i / 255
        result = levelsPixel params normalized
    in round (clamp255 (result * 255))

--------------------------------------------------------------------------------
-- Exposure
--------------------------------------------------------------------------------

-- | Apply exposure adjustment to a single pixel value [0,1].
--
--   Steps:
--   1. Multiply by 2^exposure
--   2. Add offset
--   3. Apply gamma correction: value^(1/gamma)
exposurePixel :: ExposureParams -> Double -> Double
exposurePixel params value =
  let exp' = epExposure params
      offset = epOffset params
      gamma = max 0.01 (epGamma params)
      -- Step 1: Exposure (stops)
      multiplier = 2 ** exp'
      withExposure = value * multiplier
      -- Step 2: Offset
      withOffset = withExposure + offset
      -- Step 3: Clamp before gamma
      clamped = clamp01 withOffset
      -- Step 4: Gamma
      gammaApplied = clamped ** (1 / gamma)
  in gammaApplied

-- | Apply exposure to RGB tuple.
exposure :: ExposureParams -> (Double, Double, Double) -> (Double, Double, Double)
exposure params (r, g, b) =
  ( exposurePixel params r
  , exposurePixel params g
  , exposurePixel params b
  )

-- | Build 256-entry lookup table for exposure.
buildExposureLUT :: ExposureParams -> V.Vector Word8
buildExposureLUT params =
  V.generate 256 $ \i ->
    let normalized = fromIntegral i / 255
        result = exposurePixel params normalized
    in round (clamp255 (result * 255))
