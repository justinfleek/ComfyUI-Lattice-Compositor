{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}

{-|
Module      : Lattice.Utils.LabColorUtils
Description : LAB Color Space Utilities
Copyright   : (c) Lattice, 2026
License     : MIT

Provides CIE LAB, XYZ, and YUV color space conversions
for professional color correction and analysis.

Uses D65 illuminant (standard for sRGB)
LAB L* range: 0-100, a* and b* range: -128 to +127

Source: leancomfy/lean/Lattice/Utils/LabColorUtils.lean
-}

module Lattice.Utils.LabColorUtils
  ( -- * Constants
    d65X, d65Y, d65Z
  , bt709R, bt709G, bt709B
    -- * Color Types
  , LAB(..)
  , XYZ(..)
  , YUV(..)
  , HSL(..)
  , RGB(..)
    -- * sRGB <-> Linear RGB
  , sRGBToLinear
  , linearToSRGB
    -- * RGB <-> XYZ
  , rgbToXyz
  , xyzToRgb
    -- * XYZ <-> LAB
  , xyzToLab
  , labToXyz
    -- * RGB <-> LAB
  , rgbToLab
  , labToRgb
    -- * Color Difference
  , deltaE76
  , deltaE94
    -- * RGB <-> YUV
  , rgbToYuv
  , yuvToRgb
    -- * RGB <-> HSL
  , rgbToHsl
  , hslToRgb
    -- * Utilities
  , rgbToLuminance
  , isNeutral
  , complementary
  , clamp
  , lerp
  , smoothstep
  ) where

import GHC.Generics (Generic)
import Data.Word (Word8)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | D65 white point X reference value
d65X :: Double
d65X = 95.047

-- | D65 white point Y reference value
d65Y :: Double
d65Y = 100.0

-- | D65 white point Z reference value
d65Z :: Double
d65Z = 108.883

-- | BT.709 luminance coefficient for red
bt709R :: Double
bt709R = 0.2126

-- | BT.709 luminance coefficient for green
bt709G :: Double
bt709G = 0.7152

-- | BT.709 luminance coefficient for blue
bt709B :: Double
bt709B = 0.0722

--------------------------------------------------------------------------------
-- Color Types
--------------------------------------------------------------------------------

-- | LAB color type
data LAB = LAB
  { labL :: !Double -- ^ 0-100 (lightness)
  , labA :: !Double -- ^ -128 to +127 (green to red)
  , labB :: !Double -- ^ -128 to +127 (blue to yellow)
  } deriving stock (Eq, Show, Generic)

-- | XYZ color type
data XYZ = XYZ
  { xyzX :: !Double
  , xyzY :: !Double
  , xyzZ :: !Double
  } deriving stock (Eq, Show, Generic)

-- | YUV color type (for vectorscope)
data YUV = YUV
  { yuvY :: !Double -- ^ Luminance (0-1)
  , yuvU :: !Double -- ^ Blue-Yellow chrominance (-0.5 to +0.5)
  , yuvV :: !Double -- ^ Red-Cyan chrominance (-0.5 to +0.5)
  } deriving stock (Eq, Show, Generic)

-- | HSL color type
data HSL = HSL
  { hslH :: !Double -- ^ 0-360 (hue)
  , hslS :: !Double -- ^ 0-1 (saturation)
  , hslL :: !Double -- ^ 0-1 (lightness)
  } deriving stock (Eq, Show, Generic)

-- | RGB color type (0-255)
data RGB = RGB
  { rgbR :: !Word8
  , rgbG :: !Word8
  , rgbB :: !Word8
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- sRGB <-> Linear RGB Conversion
--------------------------------------------------------------------------------

-- | Convert sRGB component (0-255) to linear RGB (0-1)
sRGBToLinear :: Double -> Double
sRGBToLinear value =
  let v = value / 255.0
  in if v <= 0.04045
     then v / 12.92
     else ((v + 0.055) / 1.055) ** 2.4

-- | Convert linear RGB (0-1) to sRGB component (0-255)
linearToSRGB :: Double -> Word8
linearToSRGB value =
  let v = if value <= 0.0031308
          then value * 12.92
          else 1.055 * (value ** (1.0 / 2.4)) - 0.055
  in round $ max 0 $ min 255 $ v * 255.0

--------------------------------------------------------------------------------
-- Conversion Matrices
--------------------------------------------------------------------------------

-- | sRGB to XYZ matrix coefficients (D65)
srgbToXyzMatrix :: ((Double, Double, Double), (Double, Double, Double), (Double, Double, Double))
srgbToXyzMatrix =
  ( (0.4124564, 0.3575761, 0.1804375)
  , (0.2126729, 0.7151522, 0.072175)
  , (0.0193339, 0.119192, 0.9503041)
  )

-- | XYZ to sRGB matrix coefficients (D65)
xyzToSrgbMatrix :: ((Double, Double, Double), (Double, Double, Double), (Double, Double, Double))
xyzToSrgbMatrix =
  ( (3.2404542, -1.5371385, -0.4985314)
  , (-0.969266, 1.8760108, 0.041556)
  , (0.0556434, -0.2040259, 1.0572252)
  )

--------------------------------------------------------------------------------
-- RGB <-> XYZ Conversion
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) to XYZ color space
rgbToXyz :: Double -> Double -> Double -> XYZ
rgbToXyz r g b =
  let rLinear = sRGBToLinear r
      gLinear = sRGBToLinear g
      bLinear = sRGBToLinear b
      ((r0, r1, r2), (g0, g1, g2), (b0, b1, b2)) = srgbToXyzMatrix
  in XYZ
       { xyzX = (rLinear * r0 + gLinear * r1 + bLinear * r2) * 100.0
       , xyzY = (rLinear * g0 + gLinear * g1 + bLinear * g2) * 100.0
       , xyzZ = (rLinear * b0 + gLinear * b1 + bLinear * b2) * 100.0
       }

-- | Convert XYZ to RGB (0-255)
xyzToRgb :: Double -> Double -> Double -> RGB
xyzToRgb xVal yVal zVal =
  let x = xVal / 100.0
      y = yVal / 100.0
      z = zVal / 100.0
      ((r0, r1, r2), (g0, g1, g2), (b0, b1, b2)) = xyzToSrgbMatrix
      rLinear = x * r0 + y * r1 + z * r2
      gLinear = x * g0 + y * g1 + z * g2
      bLinear = x * b0 + y * b1 + z * b2
  in RGB (linearToSRGB rLinear) (linearToSRGB gLinear) (linearToSRGB bLinear)

--------------------------------------------------------------------------------
-- XYZ <-> LAB Conversion
--------------------------------------------------------------------------------

-- | Lab f(t) function for XYZ to LAB conversion
labF :: Double -> Double
labF t =
  let delta = 6.0 / 29.0
      delta3 = delta * delta * delta
  in if t > delta3
     then t ** (1.0 / 3.0)
     else t / (3.0 * delta * delta) + 4.0 / 29.0

-- | Inverse Lab f(t) function for LAB to XYZ conversion
labFInverse :: Double -> Double
labFInverse t =
  let delta = 6.0 / 29.0
  in if t > delta
     then t * t * t
     else 3.0 * delta * delta * (t - 4.0 / 29.0)

-- | Convert XYZ to CIE LAB
xyzToLab :: Double -> Double -> Double -> LAB
xyzToLab xVal yVal zVal =
  let xn = xVal / d65X
      yn = yVal / d65Y
      zn = zVal / d65Z
      fx = labF xn
      fy = labF yn
      fz = labF zn
  in LAB
       { labL = 116.0 * fy - 16.0
       , labA = 500.0 * (fx - fy)
       , labB = 200.0 * (fy - fz)
       }

-- | Convert CIE LAB to XYZ
labToXyz :: Double -> Double -> Double -> XYZ
labToXyz lVal aVal bVal =
  let fy = (lVal + 16.0) / 116.0
      fx = aVal / 500.0 + fy
      fz = fy - bVal / 200.0
  in XYZ
       { xyzX = d65X * labFInverse fx
       , xyzY = d65Y * labFInverse fy
       , xyzZ = d65Z * labFInverse fz
       }

--------------------------------------------------------------------------------
-- RGB <-> LAB Direct Conversion
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) directly to CIE LAB
rgbToLab :: Double -> Double -> Double -> LAB
rgbToLab r g b =
  let xyz = rgbToXyz r g b
  in xyzToLab (xyzX xyz) (xyzY xyz) (xyzZ xyz)

-- | Convert CIE LAB directly to RGB (0-255)
labToRgb :: Double -> Double -> Double -> RGB
labToRgb lVal aVal bVal =
  let xyz = labToXyz lVal aVal bVal
  in xyzToRgb (xyzX xyz) (xyzY xyz) (xyzZ xyz)

--------------------------------------------------------------------------------
-- Color Difference (Delta E)
--------------------------------------------------------------------------------

-- | Calculate Delta E (CIE76) - basic Euclidean distance in LAB space
deltaE76 :: LAB -> LAB -> Double
deltaE76 lab1 lab2 =
  let dL = labL lab1 - labL lab2
      da = labA lab1 - labA lab2
      db = labB lab1 - labB lab2
  in sqrt (dL * dL + da * da + db * db)

-- | Calculate Delta E (CIE94) - weighted formula for graphics applications
deltaE94 :: LAB -> LAB -> Double
deltaE94 lab1 lab2 =
  let kL = 1.0
      kC = 1.0
      kH = 1.0
      k1 = 0.045
      k2 = 0.015
      dL = labL lab1 - labL lab2
      c1 = sqrt (labA lab1 * labA lab1 + labB lab1 * labB lab1)
      c2 = sqrt (labA lab2 * labA lab2 + labB lab2 * labB lab2)
      dC = c1 - c2
      da = labA lab1 - labA lab2
      db = labB lab1 - labB lab2
      dH2 = da * da + db * db - dC * dC
      dH = if dH2 > 0 then sqrt dH2 else 0
      sL = 1.0
      sC = 1.0 + k1 * c1
      sH = 1.0 + k2 * c1
      term1 = dL / (kL * sL)
      term2 = dC / (kC * sC)
      term3 = dH / (kH * sH)
  in sqrt (term1 * term1 + term2 * term2 + term3 * term3)

--------------------------------------------------------------------------------
-- RGB <-> YUV Conversion
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) to YUV (BT.709)
rgbToYuv :: Double -> Double -> Double -> YUV
rgbToYuv r g b =
  let rn = r / 255.0
      gn = g / 255.0
      bn = b / 255.0
      y = bt709R * rn + bt709G * gn + bt709B * bn
      u = (0.5 * (bn - y)) / (1.0 - bt709B)
      v = (0.5 * (rn - y)) / (1.0 - bt709R)
  in YUV y u v

-- | Convert YUV to RGB (0-255)
yuvToRgb :: Double -> Double -> Double -> RGB
yuvToRgb y u v =
  let r = y + 2.0 * v * (1.0 - bt709R)
      g = y - (2.0 * u * bt709B * (1.0 - bt709B)) / bt709G -
              (2.0 * v * bt709R * (1.0 - bt709R)) / bt709G
      b = y + 2.0 * u * (1.0 - bt709B)
      clampRgb val = round $ max 0 $ min 255 $ val * 255.0
  in RGB (clampRgb r) (clampRgb g) (clampRgb b)

--------------------------------------------------------------------------------
-- RGB <-> HSL Conversion
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) to HSL
rgbToHsl :: Double -> Double -> Double -> HSL
rgbToHsl r g b =
  let rn = r / 255.0
      gn = g / 255.0
      bn = b / 255.0
      maxC = max rn (max gn bn)
      minC = min rn (min gn bn)
      l = (maxC + minC) / 2.0
  in if maxC == minC
     then HSL 0 0 l
     else
       let d = maxC - minC
           s = if l > 0.5 then d / (2.0 - maxC - minC) else d / (maxC + minC)
           h | maxC == rn = ((gn - bn) / d + (if gn < bn then 6.0 else 0.0)) / 6.0
             | maxC == gn = ((bn - rn) / d + 2.0) / 6.0
             | otherwise  = ((rn - gn) / d + 4.0) / 6.0
       in HSL (h * 360.0) s l

-- | Helper for HSL to RGB conversion
hue2rgb :: Double -> Double -> Double -> Double
hue2rgb p q t' =
  let t = if t' < 0 then t' + 1 else if t' > 1 then t' - 1 else t'
  in if t < 1.0 / 6.0 then p + (q - p) * 6.0 * t
     else if t < 0.5 then q
     else if t < 2.0 / 3.0 then p + (q - p) * (2.0 / 3.0 - t) * 6.0
     else p

-- | Convert HSL to RGB (0-255)
hslToRgb :: Double -> Double -> Double -> RGB
hslToRgb h s l =
  let h' = (((h `mod'` 360.0) + 360.0) `mod'` 360.0) / 360.0
  in if s == 0
     then let v = round (l * 255.0) in RGB v v v
     else
       let q = if l < 0.5 then l * (1.0 + s) else l + s - l * s
           p = 2.0 * l - q
       in RGB
            (round $ hue2rgb p q (h' + 1.0 / 3.0) * 255.0)
            (round $ hue2rgb p q h' * 255.0)
            (round $ hue2rgb p q (h' - 1.0 / 3.0) * 255.0)
  where
    mod' :: Double -> Double -> Double
    mod' a b = a - b * fromIntegral (floor (a / b) :: Int)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Calculate luminance (BT.709) from RGB (0-255)
rgbToLuminance :: Double -> Double -> Double -> Double
rgbToLuminance r g b = bt709R * r + bt709G * g + bt709B * b

-- | Check if a color is within a tolerance of neutral gray
isNeutral :: Double -> Double -> Double -> Double -> Bool
isNeutral r g b tolerance =
  let lab = rgbToLab r g b
  in abs (labA lab) < tolerance && abs (labB lab) < tolerance

-- | Get the complementary color
complementary :: Double -> Double -> Double -> RGB
complementary r g b =
  let hsl = rgbToHsl r g b
  in hslToRgb (mod' (hslH hsl + 180.0) 360.0) (hslS hsl) (hslL hsl)
  where
    mod' :: Double -> Double -> Double
    mod' a m = a - m * fromIntegral (floor (a / m) :: Int)

-- | Clamp a value between min and max
clamp :: Double -> Double -> Double -> Double
clamp val minVal maxVal = max minVal (min maxVal val)

-- | Linear interpolation between two values
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * t

-- | Smoothstep function for smooth transitions
smoothstep :: Double -> Double -> Double -> Double
smoothstep edge0 edge1 x =
  let t = clamp ((x - edge0) / (edge1 - edge0)) 0 1
  in t * t * (3 - 2 * t)
