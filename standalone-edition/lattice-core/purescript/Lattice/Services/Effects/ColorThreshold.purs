-- | Lattice.Services.Effects.ColorThreshold - Threshold-based Color Effects
-- |
-- | Pure mathematical functions for threshold-based color effects:
-- | - Invert (with channel selection)
-- | - Posterize (reduce color levels)
-- | - Threshold (black and white)
-- |
-- | All functions operate on normalized [0,1] color values.
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts

module Lattice.Services.Effects.ColorThreshold
  ( InvertChannel(..)
  , InvertParams
  , PosterizeParams
  , ThresholdParams
  , defaultInvertParams
  , defaultPosterizeParams
  , defaultThresholdParams
  , invert
  , posterize
  , posterizePixel
  , threshold
  , buildPosterizeLUT
  ) where

import Prelude

import Data.Array ((..), mapWithIndex)
import Data.Int (round, toNumber)
import Data.Tuple (Tuple(..))

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Channel to invert
data InvertChannel
  = InvertRGB     -- Invert all RGB channels
  | InvertRed     -- Invert red channel only
  | InvertGreen   -- Invert green channel only
  | InvertBlue    -- Invert blue channel only
  | InvertHue     -- Invert hue (shift by 180 degrees)
  | InvertSat     -- Invert saturation
  | InvertLight   -- Invert lightness

derive instance eqInvertChannel :: Eq InvertChannel

instance showInvertChannel :: Show InvertChannel where
  show InvertRGB = "InvertRGB"
  show InvertRed = "InvertRed"
  show InvertGreen = "InvertGreen"
  show InvertBlue = "InvertBlue"
  show InvertHue = "InvertHue"
  show InvertSat = "InvertSat"
  show InvertLight = "InvertLight"

-- | Invert parameters
type InvertParams =
  { channel :: InvertChannel  -- Which channel(s) to invert
  , blend :: Number           -- Blend with original 0-1
  }

-- | Posterize parameters
type PosterizeParams =
  { levels :: Int  -- Number of levels per channel (2-256)
  }

-- | Threshold parameters
type ThresholdParams =
  { threshold :: Number  -- Threshold value [0,1]
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Default Values
-- ────────────────────────────────────────────────────────────────────────────

-- | Default invert (full RGB inversion)
defaultInvertParams :: InvertParams
defaultInvertParams =
  { channel: InvertRGB
  , blend: 1.0
  }

-- | Default posterize (6 levels)
defaultPosterizeParams :: PosterizeParams
defaultPosterizeParams =
  { levels: 6
  }

-- | Default threshold (0.5)
defaultThresholdParams :: ThresholdParams
defaultThresholdParams =
  { threshold: 0.5
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Utility Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 = max 0.0 <<< min 1.0

-- | Calculate luminance from RGB [0,1]
luminance :: Number -> Number -> Number -> Number
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

-- | Linear interpolation
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Maximum of three numbers
max3 :: Number -> Number -> Number -> Number
max3 a b c = max a (max b c)

-- | Minimum of three numbers
min3 :: Number -> Number -> Number -> Number
min3 a b c = min a (min b c)

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // hsl // c
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert RGB [0,1] to HSL [0,1]
rgbToHsl :: Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
rgbToHsl (Tuple r (Tuple g b)) =
  let maxC = max3 r g b
      minC = min3 r g b
      l = (maxC + minC) / 2.0
      d = maxC - minC
      { h, s } =
        if d == 0.0 then { h: 0.0, s: 0.0 }
        else
          let s' = if l > 0.5 then d / (2.0 - maxC - minC) else d / (maxC + minC)
              h' = if maxC == r then ((g - b) / d + (if g < b then 6.0 else 0.0)) / 6.0
                   else if maxC == g then ((b - r) / d + 2.0) / 6.0
                   else ((r - g) / d + 4.0) / 6.0
          in { h: h', s: s' }
  in Tuple h (Tuple s l)

-- | Convert HSL [0,1] to RGB [0,1]
hslToRgb :: Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
hslToRgb (Tuple h (Tuple s l)) =
  if s == 0.0 then Tuple l (Tuple l l)
  else
    let q = if l < 0.5 then l * (1.0 + s) else l + s - l * s
        p = 2.0 * l - q
        hue2rgb t
          | t < 0.0 = hue2rgb (t + 1.0)
          | t > 1.0 = hue2rgb (t - 1.0)
          | t < 1.0/6.0 = p + (q - p) * 6.0 * t
          | t < 1.0/2.0 = q
          | t < 2.0/3.0 = p + (q - p) * (2.0/3.0 - t) * 6.0
          | otherwise = p
    in Tuple (hue2rgb (h + 1.0/3.0)) (Tuple (hue2rgb h) (hue2rgb (h - 1.0/3.0)))

-- ────────────────────────────────────────────────────────────────────────────
-- Invert
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply invert effect with channel selection
invert :: InvertParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
invert params (Tuple r (Tuple g b)) =
  let blend = params.blend
      Tuple r' (Tuple g' b') = case params.channel of
        InvertRGB -> Tuple (1.0 - r) (Tuple (1.0 - g) (1.0 - b))
        InvertRed -> Tuple (1.0 - r) (Tuple g b)
        InvertGreen -> Tuple r (Tuple (1.0 - g) b)
        InvertBlue -> Tuple r (Tuple g (1.0 - b))
        InvertHue ->
          let Tuple h (Tuple s l) = rgbToHsl (Tuple r (Tuple g b))
              h' = let hNew = h + 0.5 in if hNew > 1.0 then hNew - 1.0 else hNew
          in hslToRgb (Tuple h' (Tuple s l))
        InvertSat ->
          let Tuple h (Tuple s l) = rgbToHsl (Tuple r (Tuple g b))
          in hslToRgb (Tuple h (Tuple (1.0 - s) l))
        InvertLight ->
          let Tuple h (Tuple s l) = rgbToHsl (Tuple r (Tuple g b))
          in hslToRgb (Tuple h (Tuple s (1.0 - l)))
      -- Blend with original
      rFinal = lerp r r' blend
      gFinal = lerp g g' blend
      bFinal = lerp b b' blend
  in Tuple (clamp01 rFinal) (Tuple (clamp01 gFinal) (clamp01 bFinal))

-- ────────────────────────────────────────────────────────────────────────────
-- Posterize
-- ────────────────────────────────────────────────────────────────────────────

-- | Posterize a single pixel value
posterizePixel :: Int -> Number -> Number
posterizePixel levels value
  | levels >= 256 = value
  | levels <= 1 = 0.0
  | otherwise =
      let lvls = toNumber (max 2 (min 256 levels))
          level = toNumber (round (value * (lvls - 1.0)))
          step = 1.0 / (lvls - 1.0)
      in level * step

-- | Apply posterize effect
posterize :: PosterizeParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
posterize params (Tuple r (Tuple g b)) =
  let lvls = params.levels
  in Tuple (posterizePixel lvls r) (Tuple (posterizePixel lvls g) (posterizePixel lvls b))

-- | Build 256-entry lookup table for posterize
buildPosterizeLUT :: Int -> Array Int
buildPosterizeLUT levels =
  map (\i ->
    let normalized = toNumber i / 255.0
        result = posterizePixel levels normalized
    in round (max 0.0 (min 255.0 (result * 255.0)))
  ) (0 .. 255)

-- ────────────────────────────────────────────────────────────────────────────
-- Threshold
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply threshold effect (convert to black and white)
threshold :: ThresholdParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
threshold params (Tuple r (Tuple g b)) =
  let thresh = params.threshold
      lum = luminance r g b
      value = if lum >= thresh then 1.0 else 0.0
  in Tuple value (Tuple value value)
