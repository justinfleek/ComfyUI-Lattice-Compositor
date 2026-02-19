-- | Lattice.Services.ColorCorrection.Conversions - Color Space Conversion Functions
-- |
-- | Pure mathematical functions for color space transformations:
-- | - RGB to HSL
-- | - HSL to RGB
-- | - Luminance calculation
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts (lines 131-188, 436)

module Lattice.Services.ColorCorrection.Conversions
  ( RGB
  , HSL
  , luminance
  , luminanceNormalized
  , rgbToHsl
  , hslToRgb
  , hue2rgb
  , rgbToHslTuple
  , hslToRgbTuple
  ) where

import Prelude

import Data.Tuple (Tuple(..))
import Math (max, min, round)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | RGB color with values in 0-255 range
type RGB =
  { r :: Number
  , g :: Number
  , b :: Number
  }

-- | HSL color with H in 0-1, S in 0-1, L in 0-1
type HSL =
  { h :: Number  -- ^ Hue, 0-1 (where 1 = 360°)
  , s :: Number  -- ^ Saturation, 0-1
  , l :: Number  -- ^ Lightness, 0-1
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Luminance Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate perceived luminance using Rec. 601 coefficients.
-- |
-- | Formula: L = 0.299*R + 0.587*G + 0.114*B
luminance :: Number -> Number -> Number -> Number
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

-- | Calculate normalized luminance (0-1 range).
luminanceNormalized :: Number -> Number -> Number -> Number
luminanceNormalized r g b = (r * 0.299 + g * 0.587 + b * 0.114) / 255.0

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // rgb
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert RGB (0-255) to HSL (0-1).
rgbToHsl :: Number -> Number -> Number -> HSL
rgbToHsl r g b =
  let rNorm = r / 255.0
      gNorm = g / 255.0
      bNorm = b / 255.0

      maxC = max rNorm (max gNorm bNorm)
      minC = min rNorm (min gNorm bNorm)
      l = (maxC + minC) / 2.0
  in if maxC == minC
     then { h: 0.0, s: 0.0, l: l }
     else
       let d = maxC - minC
           s = if l > 0.5
               then d / (2.0 - maxC - minC)
               else d / (maxC + minC)

           h = if maxC == rNorm
               then
                 let rawH = (gNorm - bNorm) / d
                     adjustedH = if gNorm < bNorm then rawH + 6.0 else rawH
                 in adjustedH / 6.0
               else if maxC == gNorm
               then ((bNorm - rNorm) / d + 2.0) / 6.0
               else ((rNorm - gNorm) / d + 4.0) / 6.0
       in { h: h, s: s, l: l }

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // hsl
-- ────────────────────────────────────────────────────────────────────────────

-- | Helper function for HSL to RGB conversion.
hue2rgb :: Number -> Number -> Number -> Number
hue2rgb p q t =
  let t' = if t < 0.0 then t + 1.0 else if t > 1.0 then t - 1.0 else t
  in if t' < 1.0 / 6.0 then p + (q - p) * 6.0 * t'
     else if t' < 0.5 then q
     else if t' < 2.0 / 3.0 then p + (q - p) * (2.0 / 3.0 - t') * 6.0
     else p

-- | Convert HSL (0-1) to RGB (0-255).
hslToRgb :: HSL -> RGB
hslToRgb hsl =
  if hsl.s == 0.0
  then
    let v = round (hsl.l * 255.0)
    in { r: v, g: v, b: v }
  else
    let q = if hsl.l < 0.5
            then hsl.l * (1.0 + hsl.s)
            else hsl.l + hsl.s - hsl.l * hsl.s
        p = 2.0 * hsl.l - q
        r = hue2rgb p q (hsl.h + 1.0 / 3.0)
        g = hue2rgb p q hsl.h
        b = hue2rgb p q (hsl.h - 1.0 / 3.0)
    in { r: round (r * 255.0)
       , g: round (g * 255.0)
       , b: round (b * 255.0)
       }

-- ────────────────────────────────────────────────────────────────────────────
-- Convenience Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert RGB tuple to HSL tuple.
rgbToHslTuple :: Number -> Number -> Number -> Tuple Number (Tuple Number Number)
rgbToHslTuple r g b =
  let hsl = rgbToHsl r g b
  in Tuple hsl.h (Tuple hsl.s hsl.l)

-- | Convert HSL tuple to RGB tuple.
hslToRgbTuple :: Number -> Number -> Number -> Tuple Number (Tuple Number Number)
hslToRgbTuple h s l =
  let rgb = hslToRgb { h: h, s: s, l: l }
  in Tuple rgb.r (Tuple rgb.g rgb.b)
