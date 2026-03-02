-- | Lattice.Services.BlendModes.ColorSpace - Color space conversions
-- |
-- | Pure math functions for RGB/HSL color space conversion.
-- | Used by blend mode operations.
-- |
-- | Source: ui/src/services/blendModes.ts (lines 77-148)

module Lattice.Services.BlendModes.ColorSpace
  ( -- * Types
    RGB(..)
  , HSL(..)
    -- * Constructors
  , rgb, hsl'
    -- * Color Space Conversion
  , rgbToHsl, hslToRgb
    -- * Luminance
  , getLuminance, getLuminanceNormalized
    -- * Component Access
  , getHue, getSaturation, getLightness
    -- * Utilities
  , clamp255, clampRound
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Math (round, max, min) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | RGB color with values in 0-255 range
newtype RGB = RGB { r :: Number, g :: Number, b :: Number }

derive instance Generic RGB _
derive newtype instance Eq RGB
instance Show RGB where show = genericShow

-- | HSL color with h in 0-1, s in 0-1, l in 0-1
newtype HSL = HSL { h :: Number, s :: Number, l :: Number }

derive instance Generic HSL _
derive newtype instance Eq HSL
instance Show HSL where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Constructors
-- ────────────────────────────────────────────────────────────────────────────

-- | Create RGB from components
rgb :: Number -> Number -> Number -> RGB
rgb r g b = RGB { r, g, b }

-- | Create HSL from components (named hsl' to avoid conflict with constructor)
hsl' :: Number -> Number -> Number -> HSL
hsl' h s l = HSL { h, s, l }

-- ────────────────────────────────────────────────────────────────────────────
-- Helper Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to 0-255 range
clamp255 :: Number -> Number
clamp255 value = Math.max 0.0 (Math.min 255.0 value)

-- | Round and clamp to 0-255
clampRound :: Number -> Number
clampRound = clamp255 <<< Math.round

-- ────────────────────────────────────────────────────────────────────────────
-- Luminance
-- ────────────────────────────────────────────────────────────────────────────

-- | Get luminance of RGB color (0-255 scale)
-- | Uses ITU-R BT.601 coefficients
getLuminance :: Number -> Number -> Number -> Number
getLuminance r g b = 0.299 * r + 0.587 * g + 0.114 * b

-- | Get normalized luminance (0-1 scale)
getLuminanceNormalized :: Number -> Number -> Number -> Number
getLuminanceNormalized r g b = getLuminance r g b / 255.0

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // rgb
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert RGB (0-255) to HSL (0-1)
rgbToHsl :: Number -> Number -> Number -> HSL
rgbToHsl r g b =
  let rn = r / 255.0
      gn = g / 255.0
      bn = b / 255.0

      maxVal = Math.max rn (Math.max gn bn)
      minVal = Math.min rn (Math.min gn bn)
      l = (maxVal + minVal) / 2.0

  in if maxVal == minVal
     then HSL { h: 0.0, s: 0.0, l }  -- Achromatic
     else
       let d = maxVal - minVal
           s = if l > 0.5
               then d / (2.0 - maxVal - minVal)
               else d / (maxVal + minVal)

           h = if maxVal == rn
               then ((gn - bn) / d + (if gn < bn then 6.0 else 0.0)) / 6.0
               else if maxVal == gn
               then ((bn - rn) / d + 2.0) / 6.0
               else ((rn - gn) / d + 4.0) / 6.0

       in HSL { h, s, l }

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // hsl
-- ────────────────────────────────────────────────────────────────────────────

-- | Helper for HSL to RGB conversion
hue2rgb :: Number -> Number -> Number -> Number
hue2rgb p q t0 =
  let t = if t0 < 0.0 then t0 + 1.0
          else if t0 > 1.0 then t0 - 1.0
          else t0
  in if t < 1.0 / 6.0
     then p + (q - p) * 6.0 * t
     else if t < 1.0 / 2.0
     then q
     else if t < 2.0 / 3.0
     then p + (q - p) * (2.0 / 3.0 - t) * 6.0
     else p

-- | Convert HSL (0-1) to RGB (0-255)
hslToRgb :: HSL -> RGB
hslToRgb (HSL hsl)
  | hsl.s == 0.0 =
      -- Achromatic
      let v = Math.round (hsl.l * 255.0)
      in RGB { r: v, g: v, b: v }
  | otherwise =
      let q = if hsl.l < 0.5 then hsl.l * (1.0 + hsl.s) else hsl.l + hsl.s - hsl.l * hsl.s
          p = 2.0 * hsl.l - q
          r' = hue2rgb p q (hsl.h + 1.0 / 3.0)
          g' = hue2rgb p q hsl.h
          b' = hue2rgb p q (hsl.h - 1.0 / 3.0)
      in RGB { r: Math.round (r' * 255.0)
             , g: Math.round (g' * 255.0)
             , b: Math.round (b' * 255.0) }

-- ────────────────────────────────────────────────────────────────────────────
-- Component Access
-- ────────────────────────────────────────────────────────────────────────────

-- | Get hue component from RGB (0-1)
getHue :: Number -> Number -> Number -> Number
getHue r g b = case rgbToHsl r g b of HSL x -> x.h

-- | Get saturation component from RGB (0-1)
getSaturation :: Number -> Number -> Number -> Number
getSaturation r g b = case rgbToHsl r g b of HSL x -> x.s

-- | Get lightness component from RGB (0-1)
getLightness :: Number -> Number -> Number -> Number
getLightness r g b = case rgbToHsl r g b of HSL x -> x.l
