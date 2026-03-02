-- | Lattice.Services.Effects.ColorCorrection - Basic Color Correction
-- |
-- | Pure mathematical functions for color correction:
-- | - Brightness & Contrast
-- | - Levels (input/output with gamma)
-- | - Exposure (photographic stops)
-- |
-- | All functions operate on normalized [0,1] color values.
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts

module Lattice.Services.Effects.ColorCorrection
  ( ColorParams
  , LevelsParams
  , ExposureParams
  , defaultColorParams
  , defaultLevelsParams
  , defaultExposureParams
  , brightnessContrast
  , brightnessContrastPixel
  , levels
  , levelsPixel
  , exposure
  , exposurePixel
  , buildLUT
  ) where

import Prelude

import Data.Array ((..), mapWithIndex)
import Data.Int (round, toNumber)
import Data.Tuple (Tuple(..))
import Math (pow, max, min)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Brightness/Contrast parameters
type ColorParams =
  { brightness :: Number  -- -1.5 to 1.5 (normalized from -150 to 150)
  , contrast :: Number    -- -1.0 to 1.0 (normalized from -100 to 100)
  , useLegacy :: Boolean  -- Use legacy (simpler) contrast formula
  }

-- | Levels parameters
type LevelsParams =
  { inputBlack :: Number   -- 0-1 (normalized from 0-255)
  , inputWhite :: Number   -- 0-1 (normalized from 0-255)
  , gamma :: Number        -- 0.01-10 (gamma correction)
  , outputBlack :: Number  -- 0-1 (normalized from 0-255)
  , outputWhite :: Number  -- 0-1 (normalized from 0-255)
  }

-- | Exposure parameters
type ExposureParams =
  { exposure :: Number  -- -5 to 5 stops
  , offset :: Number    -- -1 to 1 (additive)
  , gamma :: Number     -- 0.1 to 10 (gamma correction)
  }

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default brightness/contrast (no change)
defaultColorParams :: ColorParams
defaultColorParams =
  { brightness: 0.0
  , contrast: 0.0
  , useLegacy: false
  }

-- | Default levels (identity mapping)
defaultLevelsParams :: LevelsParams
defaultLevelsParams =
  { inputBlack: 0.0
  , inputWhite: 1.0
  , gamma: 1.0
  , outputBlack: 0.0
  , outputWhite: 1.0
  }

-- | Default exposure (no change)
defaultExposureParams :: ExposureParams
defaultExposureParams =
  { exposure: 0.0
  , offset: 0.0
  , gamma: 1.0
  }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 = max 0.0 <<< min 1.0

-- | Clamp value to [0, 255]
clamp255 :: Number -> Number
clamp255 = max 0.0 <<< min 255.0

-- | Safe division with fallback
safeDiv :: Number -> Number -> Number -> Number
safeDiv _ 0.0 fallback = fallback
safeDiv a b _ = a / b

--------------------------------------------------------------------------------
-- Brightness & Contrast
--------------------------------------------------------------------------------

-- | Calculate contrast factor based on mode
contrastFactor :: Boolean -> Number -> Number
contrastFactor true contrast = 1.0 + contrast
contrastFactor false contrast =
  let c255 = contrast * 255.0
  in safeDiv (259.0 * (c255 + 255.0)) (255.0 * (259.0 - c255)) 1.0

-- | Apply brightness and contrast to a single pixel value [0,1]
brightnessContrastPixel :: ColorParams -> Number -> Number
brightnessContrastPixel params value =
  let factor = contrastFactor params.useLegacy params.contrast
      withBrightness = value + params.brightness
      withContrast = factor * (withBrightness - 0.5) + 0.5
  in clamp01 withContrast

-- | Apply brightness and contrast to RGB tuple
brightnessContrast :: ColorParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
brightnessContrast params (Tuple r (Tuple g b)) =
  Tuple
    (brightnessContrastPixel params r)
    (Tuple
      (brightnessContrastPixel params g)
      (brightnessContrastPixel params b))

--------------------------------------------------------------------------------
-- Levels
--------------------------------------------------------------------------------

-- | Apply levels adjustment to a single pixel value [0,1]
levelsPixel :: LevelsParams -> Number -> Number
levelsPixel params value =
  let inputRange = params.inputWhite - params.inputBlack
      outputRange = params.outputWhite - params.outputBlack
      gamma = max 0.01 params.gamma
      -- Input levels
      mapped = safeDiv (value - params.inputBlack) inputRange 0.0
      clamped = clamp01 mapped
      -- Gamma correction
      gammaApplied = pow clamped (1.0 / gamma)
      -- Output levels
      output = params.outputBlack + gammaApplied * outputRange
  in clamp01 output

-- | Apply levels to RGB tuple
levels :: LevelsParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
levels params (Tuple r (Tuple g b)) =
  Tuple
    (levelsPixel params r)
    (Tuple
      (levelsPixel params g)
      (levelsPixel params b))

--------------------------------------------------------------------------------
-- Exposure
--------------------------------------------------------------------------------

-- | Apply exposure adjustment to a single pixel value [0,1]
exposurePixel :: ExposureParams -> Number -> Number
exposurePixel params value =
  let multiplier = pow 2.0 params.exposure
      gamma = max 0.01 params.gamma
      -- Exposure (stops)
      withExposure = value * multiplier
      -- Offset
      withOffset = withExposure + params.offset
      -- Clamp before gamma
      clamped = clamp01 withOffset
      -- Gamma
      gammaApplied = pow clamped (1.0 / gamma)
  in gammaApplied

-- | Apply exposure to RGB tuple
exposure :: ExposureParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
exposure params (Tuple r (Tuple g b)) =
  Tuple
    (exposurePixel params r)
    (Tuple
      (exposurePixel params g)
      (exposurePixel params b))

--------------------------------------------------------------------------------
-- Lookup Table Generation
--------------------------------------------------------------------------------

-- | Build 256-entry lookup table using given function
buildLUT :: (Number -> Number) -> Array Int
buildLUT f =
  map (\i ->
    let normalized = toNumber i / 255.0
        result = f normalized
    in round (clamp255 (result * 255.0))
  ) (0 .. 255)
