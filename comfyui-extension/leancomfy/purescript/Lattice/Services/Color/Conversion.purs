-- | Lattice.Services.Color.Conversion - Color Space Conversions
-- |
-- | Pure mathematical functions for color space conversion:
-- | - RGB ↔ HSV conversion
-- | - BT.709 luminance (brightness)
-- | - Color sample creation with derived values
-- |
-- | Source: ui/src/services/colorDepthReactivity.ts

module Lattice.Services.Color.Conversion
  ( -- * Types
    RGB, RGBA, HSV, ColorSample, ColorFeature(..)
    -- * Color Conversion
  , rgbToHsv, hsvToRgb
    -- * Brightness
  , calculateBrightness, rgbBrightness
    -- * Color Sample
  , createColorSample, colorSampleFromRGB, colorSampleFromRGBA
  , emptyColorSample
    -- * Feature Extraction
  , getFeatureValue
    -- * Utilities
  , clamp01, clampRGB, clampRGBA, lerpRGB, lerpRGBA
  ) where

import Prelude
import Data.Int (floor, toNumber)
import Math (abs, max, min) as Math

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | RGB color with components in 0-1 range
type RGB =
  { r :: Number  -- 0-1
  , g :: Number  -- 0-1
  , b :: Number  -- 0-1
  }

-- | RGBA color with alpha
type RGBA =
  { r :: Number  -- 0-1
  , g :: Number  -- 0-1
  , b :: Number  -- 0-1
  , a :: Number  -- 0-1
  }

-- | HSV color with components in 0-1 range
type HSV =
  { h :: Number  -- 0-1 (0 = red, 0.33 = green, 0.67 = blue)
  , s :: Number  -- 0-1
  , v :: Number  -- 0-1
  }

-- | Complete color sample with all derived values
type ColorSample =
  { r :: Number          -- 0-1
  , g :: Number          -- 0-1
  , b :: Number          -- 0-1
  , a :: Number          -- 0-1
  , brightness :: Number -- 0-1 (BT.709 luminance)
  , hue :: Number        -- 0-1
  , saturation :: Number -- 0-1
  , value :: Number      -- 0-1 (HSV V)
  }

-- | Color feature type for sampling
data ColorFeature
  = FeatureBrightness
  | FeatureHue
  | FeatureSaturation
  | FeatureValue
  | FeatureRed
  | FeatureGreen
  | FeatureBlue
  | FeatureAlpha

derive instance eqColorFeature :: Eq ColorFeature

--------------------------------------------------------------------------------
-- RGB to HSV Conversion
--------------------------------------------------------------------------------

-- | Convert RGB to HSV.
-- |
-- | Algorithm:
-- | - V = max(R, G, B)
-- | - S = (V - min) / V (0 if V = 0)
-- | - H based on which channel is max
rgbToHsv :: RGB -> HSV
rgbToHsv rgb =
  let r = rgb.r
      g = rgb.g
      b = rgb.b

      maxVal = Math.max r (Math.max g b)
      minVal = Math.min r (Math.min g b)
      d = maxVal - minVal

      v = maxVal
      s = if maxVal == 0.0 then 0.0 else d / maxVal

      h = if maxVal == minVal then 0.0  -- Achromatic
          else if maxVal == r then
            let hRaw = (g - b) / d
                hAdj = if g < b then hRaw + 6.0 else hRaw
            in hAdj / 6.0
          else if maxVal == g then
            ((b - r) / d + 2.0) / 6.0
          else  -- maxVal == b
            ((r - g) / d + 4.0) / 6.0

  in { h, s, v }

-- | Convert HSV to RGB.
-- |
-- | Standard HSV to RGB conversion algorithm.
hsvToRgb :: HSV -> RGB
hsvToRgb hsv =
  if hsv.s == 0.0 then
    -- Achromatic (gray)
    { r: hsv.v, g: hsv.v, b: hsv.v }
  else
    let h6 = hsv.h * 6.0
        i = floor h6 `mod` 6
        f = h6 - toNumber (floor h6)
        p = hsv.v * (1.0 - hsv.s)
        q = hsv.v * (1.0 - hsv.s * f)
        t = hsv.v * (1.0 - hsv.s * (1.0 - f))
    in case i of
         0 -> { r: hsv.v, g: t, b: p }
         1 -> { r: q, g: hsv.v, b: p }
         2 -> { r: p, g: hsv.v, b: t }
         3 -> { r: p, g: q, b: hsv.v }
         4 -> { r: t, g: p, b: hsv.v }
         _ -> { r: hsv.v, g: p, b: q }  -- i == 5

--------------------------------------------------------------------------------
-- Brightness (Luminance)
--------------------------------------------------------------------------------

-- | Calculate brightness using ITU-R BT.709 luminance coefficients.
-- |
-- | Y = 0.2126 * R + 0.7152 * G + 0.0722 * B
-- |
-- | This is the standard formula for perceived brightness.
calculateBrightness :: Number -> Number -> Number -> Number
calculateBrightness r g b = 0.2126 * r + 0.7152 * g + 0.0722 * b

-- | Calculate brightness from RGB structure.
rgbBrightness :: RGB -> Number
rgbBrightness rgb = calculateBrightness rgb.r rgb.g rgb.b

--------------------------------------------------------------------------------
-- Color Sample Creation
--------------------------------------------------------------------------------

-- | Create a complete color sample from RGBA values.
-- |
-- | Derives all color properties:
-- | - HSV components
-- | - BT.709 brightness
createColorSample :: Number -> Number -> Number -> Number -> ColorSample
createColorSample r g b a =
  let hsv = rgbToHsv { r, g, b }
      brightness = calculateBrightness r g b
  in { r
     , g
     , b
     , a
     , brightness
     , hue: hsv.h
     , saturation: hsv.s
     , value: hsv.v
     }

-- | Create color sample from RGB.
colorSampleFromRGB :: RGB -> Number -> ColorSample
colorSampleFromRGB rgb a = createColorSample rgb.r rgb.g rgb.b a

-- | Create color sample from RGBA.
colorSampleFromRGBA :: RGBA -> ColorSample
colorSampleFromRGBA rgba = createColorSample rgba.r rgba.g rgba.b rgba.a

-- | Empty/black color sample.
emptyColorSample :: ColorSample
emptyColorSample = createColorSample 0.0 0.0 0.0 0.0

--------------------------------------------------------------------------------
-- Feature Extraction
--------------------------------------------------------------------------------

-- | Extract a specific feature value from a color sample.
getFeatureValue :: ColorSample -> ColorFeature -> Number
getFeatureValue sample feature = case feature of
  FeatureBrightness -> sample.brightness
  FeatureHue -> sample.hue
  FeatureSaturation -> sample.saturation
  FeatureValue -> sample.value
  FeatureRed -> sample.r
  FeatureGreen -> sample.g
  FeatureBlue -> sample.b
  FeatureAlpha -> sample.a

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp a value to 0-1 range.
clamp01 :: Number -> Number
clamp01 x = Math.max 0.0 (Math.min 1.0 x)

-- | Clamp RGB to valid range.
clampRGB :: RGB -> RGB
clampRGB rgb =
  { r: clamp01 rgb.r
  , g: clamp01 rgb.g
  , b: clamp01 rgb.b
  }

-- | Clamp RGBA to valid range.
clampRGBA :: RGBA -> RGBA
clampRGBA rgba =
  { r: clamp01 rgba.r
  , g: clamp01 rgba.g
  , b: clamp01 rgba.b
  , a: clamp01 rgba.a
  }

-- | Linear interpolation between two colors.
lerpRGB :: RGB -> RGB -> Number -> RGB
lerpRGB a b t =
  let tc = clamp01 t
  in { r: a.r + (b.r - a.r) * tc
     , g: a.g + (b.g - a.g) * tc
     , b: a.b + (b.b - a.b) * tc
     }

-- | Linear interpolation between two RGBA colors.
lerpRGBA :: RGBA -> RGBA -> Number -> RGBA
lerpRGBA a b t =
  let tc = clamp01 t
  in { r: a.r + (b.r - a.r) * tc
     , g: a.g + (b.g - a.g) * tc
     , b: a.b + (b.b - a.b) * tc
     , a: a.a + (b.a - a.a) * tc
     }
