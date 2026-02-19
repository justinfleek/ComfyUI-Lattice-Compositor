{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Services.BlendModes.ColorSpace
Description : Color space conversions
Copyright   : (c) Lattice, 2026
License     : MIT

Pure math functions for RGB/HSL color space conversion.
Used by blend mode operations.

Source: ui/src/services/blendModes.ts (lines 77-148)
-}

module Lattice.Services.BlendModes.ColorSpace
  ( -- * Types
    RGB(..)
  , HSL(..)
    -- * Constructors
  , rgb, hsl
    -- * Color Space Conversion
  , rgbToHsl, hslToRgb
    -- * Luminance
  , getLuminance, getLuminanceNormalized
    -- * Component Access
  , getHue, getSaturation, getLightness
    -- * Utilities
  , clamp255, clampRound
  ) where

import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | RGB color with values in 0-255 range
data RGB = RGB
  { rgbR :: Double
  , rgbG :: Double
  , rgbB :: Double
  } deriving stock (Eq, Show, Generic)

-- | HSL color with h in 0-1, s in 0-1, l in 0-1
data HSL = HSL
  { hslH :: Double
  , hslS :: Double
  , hslL :: Double
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Create RGB from components
rgb :: Double -> Double -> Double -> RGB
rgb = RGB

-- | Create HSL from components
hsl :: Double -> Double -> Double -> HSL
hsl = HSL

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Clamp value to 0-255 range
clamp255 :: Double -> Double
clamp255 = max 0 . min 255

-- | Round and clamp to 0-255
clampRound :: Double -> Double
clampRound = clamp255 . fromIntegral . (round :: Double -> Int)

--------------------------------------------------------------------------------
-- Luminance
--------------------------------------------------------------------------------

-- | Get luminance of RGB color (0-255 scale)
--   Uses ITU-R BT.601 coefficients
getLuminance :: Double -> Double -> Double -> Double
getLuminance r g b = 0.299 * r + 0.587 * g + 0.114 * b

-- | Get normalized luminance (0-1 scale)
getLuminanceNormalized :: Double -> Double -> Double -> Double
getLuminanceNormalized r g b = getLuminance r g b / 255.0

--------------------------------------------------------------------------------
-- RGB to HSL
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) to HSL (0-1)
rgbToHsl :: Double -> Double -> Double -> HSL
rgbToHsl r g b =
  let rn = r / 255.0
      gn = g / 255.0
      bn = b / 255.0

      maxVal = max rn (max gn bn)
      minVal = min rn (min gn bn)
      l = (maxVal + minVal) / 2.0

  in if maxVal == minVal
     then HSL 0.0 0.0 l  -- Achromatic
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

       in HSL h s l

--------------------------------------------------------------------------------
-- HSL to RGB
--------------------------------------------------------------------------------

-- | Helper for HSL to RGB conversion
hue2rgb :: Double -> Double -> Double -> Double
hue2rgb p q t0 =
  let t = if t0 < 0 then t0 + 1
          else if t0 > 1 then t0 - 1
          else t0
  in if t < 1 / 6
     then p + (q - p) * 6 * t
     else if t < 1 / 2
     then q
     else if t < 2 / 3
     then p + (q - p) * (2 / 3 - t) * 6
     else p

-- | Convert HSL (0-1) to RGB (0-255)
hslToRgb :: HSL -> RGB
hslToRgb (HSL h s l)
  | s == 0 =
      -- Achromatic
      let v = fromIntegral (round (l * 255.0) :: Int)
      in RGB v v v
  | otherwise =
      let q = if l < 0.5 then l * (1 + s) else l + s - l * s
          p = 2 * l - q
          r' = hue2rgb p q (h + 1 / 3)
          g' = hue2rgb p q h
          b' = hue2rgb p q (h - 1 / 3)
      in RGB (fromIntegral (round (r' * 255.0) :: Int))
             (fromIntegral (round (g' * 255.0) :: Int))
             (fromIntegral (round (b' * 255.0) :: Int))

--------------------------------------------------------------------------------
-- Component Access
--------------------------------------------------------------------------------

-- | Get hue component from RGB (0-1)
getHue :: Double -> Double -> Double -> Double
getHue r g b = hslH (rgbToHsl r g b)

-- | Get saturation component from RGB (0-1)
getSaturation :: Double -> Double -> Double -> Double
getSaturation r g b = hslS (rgbToHsl r g b)

-- | Get lightness component from RGB (0-1)
getLightness :: Double -> Double -> Double -> Double
getLightness r g b = hslL (rgbToHsl r g b)
