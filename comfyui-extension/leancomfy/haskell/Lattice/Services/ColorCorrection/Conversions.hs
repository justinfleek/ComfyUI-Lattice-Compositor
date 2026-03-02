{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.ColorCorrection.Conversions
Description : Color Space Conversion Functions
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for color space transformations:
- RGB to HSL
- HSL to RGB
- Luminance calculation

All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts (lines 131-188, 436)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.ColorCorrection.Conversions
  ( -- * Types
    RGB(..)
  , HSL(..)
    -- * Luminance
  , luminance
  , luminanceNormalized
    -- * Color Conversions
  , rgbToHsl
  , hslToRgb
  , hue2rgb
    -- * Tuple Versions
  , rgbToHslTuple
  , hslToRgbTuple
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | RGB color with values in 0-255 range
data RGB = RGB
  { rgbR :: Double
  , rgbG :: Double
  , rgbB :: Double
  } deriving (Show, Eq)

-- | HSL color with H in 0-1, S in 0-1, L in 0-1
data HSL = HSL
  { hslH :: Double  -- ^ Hue, 0-1 (where 1 = 360°)
  , hslS :: Double  -- ^ Saturation, 0-1
  , hslL :: Double  -- ^ Lightness, 0-1
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Luminance Calculation
--------------------------------------------------------------------------------

-- | Calculate perceived luminance using Rec. 601 coefficients.
--
-- Formula: L = 0.299*R + 0.587*G + 0.114*B
luminance :: Double  -- ^ Red (0-255)
          -> Double  -- ^ Green (0-255)
          -> Double  -- ^ Blue (0-255)
          -> Double  -- ^ Luminance (0-255)
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

-- | Calculate normalized luminance (0-1 range).
luminanceNormalized :: Double -> Double -> Double -> Double
luminanceNormalized r g b = (r * 0.299 + g * 0.587 + b * 0.114) / 255

--------------------------------------------------------------------------------
-- RGB to HSL Conversion
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) to HSL (0-1).
rgbToHsl :: Double -> Double -> Double -> HSL
rgbToHsl r g b =
  let rNorm = r / 255
      gNorm = g / 255
      bNorm = b / 255

      maxC = max rNorm (max gNorm bNorm)
      minC = min rNorm (min gNorm bNorm)
      l = (maxC + minC) / 2
  in if maxC == minC
     then HSL 0 0 l  -- Achromatic
     else
       let d = maxC - minC
           s = if l > 0.5
               then d / (2 - maxC - minC)
               else d / (maxC + minC)

           h | maxC == rNorm =
                 let rawH = (gNorm - bNorm) / d
                     adjustedH = if gNorm < bNorm then rawH + 6 else rawH
                 in adjustedH / 6
             | maxC == gNorm = ((bNorm - rNorm) / d + 2) / 6
             | otherwise = ((rNorm - gNorm) / d + 4) / 6
       in HSL h s l

--------------------------------------------------------------------------------
-- HSL to RGB Conversion
--------------------------------------------------------------------------------

-- | Helper function for HSL to RGB conversion.
hue2rgb :: Double  -- ^ p (lower bound)
        -> Double  -- ^ q (upper bound)
        -> Double  -- ^ t (hue offset)
        -> Double  -- ^ RGB component value (0-1)
hue2rgb p q t =
  let t' | t < 0     = t + 1
         | t > 1     = t - 1
         | otherwise = t
  in if t' < 1/6 then p + (q - p) * 6 * t'
     else if t' < 0.5 then q
     else if t' < 2/3 then p + (q - p) * (2/3 - t') * 6
     else p

-- | Convert HSL (0-1) to RGB (0-255).
hslToRgb :: HSL -> RGB
hslToRgb (HSL h s l)
  | s == 0 =
      let v = round' (l * 255)
      in RGB v v v
  | otherwise =
      let q = if l < 0.5 then l * (1 + s) else l + s - l * s
          p = 2 * l - q
          r = hue2rgb p q (h + 1/3)
          g = hue2rgb p q h
          b = hue2rgb p q (h - 1/3)
      in RGB (round' (r * 255)) (round' (g * 255)) (round' (b * 255))
  where
    round' x = fromIntegral (round x :: Int)

--------------------------------------------------------------------------------
-- Convenience Functions
--------------------------------------------------------------------------------

-- | Convert RGB tuple to HSL tuple.
rgbToHslTuple :: Double -> Double -> Double -> (Double, Double, Double)
rgbToHslTuple r g b =
  let HSL h s l = rgbToHsl r g b
  in (h, s, l)

-- | Convert HSL tuple to RGB tuple.
hslToRgbTuple :: Double -> Double -> Double -> (Double, Double, Double)
hslToRgbTuple h s l =
  let RGB r g b = hslToRgb (HSL h s l)
  in (r, g, b)
