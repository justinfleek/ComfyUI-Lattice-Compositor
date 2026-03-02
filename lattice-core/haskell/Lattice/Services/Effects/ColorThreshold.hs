{-|
Module      : Lattice.Services.Effects.ColorThreshold
Description : Threshold-based Color Effects
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for threshold-based color effects:
- Invert (with channel selection)
- Posterize (reduce color levels)
- Threshold (black and white)

All functions operate on normalized [0,1] color values.
All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Effects.ColorThreshold
  ( -- * Types
    InvertChannel(..)
  , InvertParams(..)
  , PosterizeParams(..)
  , ThresholdParams(..)
    -- * Default Values
  , defaultInvertParams
  , defaultPosterizeParams
  , defaultThresholdParams
    -- * Color Threshold Functions
  , invert
  , invertChannel
  , posterize
  , posterizePixel
  , threshold
    -- * Lookup Table Generation
  , buildPosterizeLUT
  ) where

import Data.Word (Word8)
import qualified Data.Vector.Unboxed as V

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Channel to invert
data InvertChannel
  = InvertRGB       -- ^ Invert all RGB channels
  | InvertRed       -- ^ Invert red channel only
  | InvertGreen     -- ^ Invert green channel only
  | InvertBlue      -- ^ Invert blue channel only
  | InvertHue       -- ^ Invert hue (shift by 180 degrees)
  | InvertSat       -- ^ Invert saturation
  | InvertLight     -- ^ Invert lightness
  deriving (Eq, Show)

-- | Invert parameters
data InvertParams = InvertParams
  { ipChannel :: !InvertChannel  -- ^ Which channel(s) to invert
  , ipBlend   :: !Double         -- ^ Blend with original 0-1
  } deriving (Eq, Show)

-- | Posterize parameters
data PosterizeParams = PosterizeParams
  { ppLevels :: !Int  -- ^ Number of levels per channel (2-256)
  } deriving (Eq, Show)

-- | Threshold parameters
data ThresholdParams = ThresholdParams
  { tpThreshold :: !Double  -- ^ Threshold value [0,1]
  } deriving (Eq, Show)

-- ────────────────────────────────────────────────────────────────────────────
-- Default Values
-- ────────────────────────────────────────────────────────────────────────────

-- | Default invert (full RGB inversion)
defaultInvertParams :: InvertParams
defaultInvertParams = InvertParams
  { ipChannel = InvertRGB
  , ipBlend = 1
  }

-- | Default posterize (6 levels)
defaultPosterizeParams :: PosterizeParams
defaultPosterizeParams = PosterizeParams
  { ppLevels = 6
  }

-- | Default threshold (0.5)
defaultThresholdParams :: ThresholdParams
defaultThresholdParams = ThresholdParams
  { tpThreshold = 0.5
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Utility Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to [0, 1]
clamp01 :: Double -> Double
clamp01 = max 0 . min 1

-- | Calculate luminance from RGB [0,1]
luminance :: Double -> Double -> Double -> Double
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

-- | Linear interpolation
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * t

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // hsl // c
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert RGB [0,1] to HSL [0,1]
rgbToHsl :: (Double, Double, Double) -> (Double, Double, Double)
rgbToHsl (r, g, b) =
  let maxC = maximum [r, g, b]
      minC = minimum [r, g, b]
      l = (maxC + minC) / 2
      d = maxC - minC
      (h, s)
        | d == 0 = (0, 0)
        | otherwise =
            let s' = if l > 0.5 then d / (2 - maxC - minC) else d / (maxC + minC)
                h' | maxC == r = ((g - b) / d + (if g < b then 6 else 0)) / 6
                   | maxC == g = ((b - r) / d + 2) / 6
                   | otherwise = ((r - g) / d + 4) / 6
            in (h', s')
  in (h, s, l)

-- | Convert HSL [0,1] to RGB [0,1]
hslToRgb :: (Double, Double, Double) -> (Double, Double, Double)
hslToRgb (h, s, l)
  | s == 0 = (l, l, l)
  | otherwise =
      let q = if l < 0.5 then l * (1 + s) else l + s - l * s
          p = 2 * l - q
          hue2rgb t
            | t < 0 = hue2rgb (t + 1)
            | t > 1 = hue2rgb (t - 1)
            | t < 1/6 = p + (q - p) * 6 * t
            | t < 1/2 = q
            | t < 2/3 = p + (q - p) * (2/3 - t) * 6
            | otherwise = p
      in (hue2rgb (h + 1/3), hue2rgb h, hue2rgb (h - 1/3))

-- ────────────────────────────────────────────────────────────────────────────
-- Invert
-- ────────────────────────────────────────────────────────────────────────────

-- | Invert a single channel value
invertChannel :: Double -> Double
invertChannel = (1 -)

-- | Apply invert effect with channel selection.
invert :: InvertParams -> (Double, Double, Double) -> (Double, Double, Double)
invert params (r, g, b) =
  let blend = ipBlend params
      (r', g', b') = case ipChannel params of
        InvertRGB -> (1 - r, 1 - g, 1 - b)
        InvertRed -> (1 - r, g, b)
        InvertGreen -> (r, 1 - g, b)
        InvertBlue -> (r, g, 1 - b)
        InvertHue ->
          let (h, s, l) = rgbToHsl (r, g, b)
              h' = let hNew = h + 0.5 in if hNew > 1 then hNew - 1 else hNew
          in hslToRgb (h', s, l)
        InvertSat ->
          let (h, s, l) = rgbToHsl (r, g, b)
          in hslToRgb (h, 1 - s, l)
        InvertLight ->
          let (h, s, l) = rgbToHsl (r, g, b)
          in hslToRgb (h, s, 1 - l)
      -- Blend with original
      rFinal = lerp r r' blend
      gFinal = lerp g g' blend
      bFinal = lerp b b' blend
  in (clamp01 rFinal, clamp01 gFinal, clamp01 bFinal)

-- ────────────────────────────────────────────────────────────────────────────
-- Posterize
-- ────────────────────────────────────────────────────────────────────────────

-- | Posterize a single pixel value.
--
--   Reduces continuous 0-1 range to discrete levels.
posterizePixel :: Int -> Double -> Double
posterizePixel levels value
  | levels >= 256 = value  -- No change at 256 levels
  | levels <= 1 = 0        -- Single level
  | otherwise =
      let lvls = fromIntegral (max 2 (min 256 levels))
          level = fromIntegral (round (value * (lvls - 1)) :: Int)
          step = 1 / (lvls - 1)
      in level * step

-- | Apply posterize effect.
posterize :: PosterizeParams -> (Double, Double, Double) -> (Double, Double, Double)
posterize params (r, g, b) =
  let lvls = ppLevels params
  in (posterizePixel lvls r, posterizePixel lvls g, posterizePixel lvls b)

-- | Build 256-entry lookup table for posterize.
buildPosterizeLUT :: Int -> V.Vector Word8
buildPosterizeLUT levels =
  V.generate 256 $ \i ->
    let normalized = fromIntegral i / 255
        result = posterizePixel levels normalized
    in round (max 0 (min 255 (result * 255)))

-- ────────────────────────────────────────────────────────────────────────────
-- Threshold
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply threshold effect (convert to black and white).
threshold :: ThresholdParams -> (Double, Double, Double) -> (Double, Double, Double)
threshold params (r, g, b) =
  let thresh = tpThreshold params
      lum = luminance r g b
      value = if lum >= thresh then 1 else 0
  in (value, value, value)
