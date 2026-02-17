-- | Lattice.Utils.LabColorUtils - LAB Color Space Utilities
-- |
-- | Provides CIE LAB, XYZ, and YUV color space conversions
-- | for professional color correction and analysis.
-- |
-- | Uses D65 illuminant (standard for sRGB)
-- | LAB L* range: 0-100, a* and b* range: -128 to +127
-- |
-- | Source: leancomfy/lean/Lattice/Utils/LabColorUtils.lean

module Lattice.Utils.LabColorUtils
  ( -- Constants
    d65X, d65Y, d65Z
  , bt709R, bt709G, bt709B
    -- Color Types
  , LAB
  , XYZ
  , YUV
  , HSL
  , RGB
    -- sRGB <-> Linear RGB
  , sRGBToLinear
  , linearToSRGB
    -- RGB <-> XYZ
  , rgbToXyz
  , xyzToRgb
    -- XYZ <-> LAB
  , xyzToLab
  , labToXyz
    -- RGB <-> LAB
  , rgbToLab
  , labToRgb
    -- Color Difference
  , deltaE76
  , deltaE94
    -- RGB <-> YUV
  , rgbToYuv
  , yuvToRgb
    -- RGB <-> HSL
  , rgbToHsl
  , hslToRgb
    -- Utilities
  , rgbToLuminance
  , isNeutral
  , complementary
  , clamp
  , lerp
  , smoothstep
  ) where

import Prelude
import Data.Int (floor, round)
import Data.Number (pow, sqrt, abs) as Number
import Math (floor) as Math

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | D65 white point X reference value
d65X :: Number
d65X = 95.047

-- | D65 white point Y reference value
d65Y :: Number
d65Y = 100.0

-- | D65 white point Z reference value
d65Z :: Number
d65Z = 108.883

-- | BT.709 luminance coefficient for red
bt709R :: Number
bt709R = 0.2126

-- | BT.709 luminance coefficient for green
bt709G :: Number
bt709G = 0.7152

-- | BT.709 luminance coefficient for blue
bt709B :: Number
bt709B = 0.0722

--------------------------------------------------------------------------------
-- Color Types
--------------------------------------------------------------------------------

-- | LAB color type
type LAB =
  { l :: Number -- 0-100 (lightness)
  , a :: Number -- -128 to +127 (green to red)
  , b :: Number -- -128 to +127 (blue to yellow)
  }

-- | XYZ color type
type XYZ =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | YUV color type (for vectorscope)
type YUV =
  { y :: Number -- Luminance (0-1)
  , u :: Number -- Blue-Yellow chrominance (-0.5 to +0.5)
  , v :: Number -- Red-Cyan chrominance (-0.5 to +0.5)
  }

-- | HSL color type
type HSL =
  { h :: Number -- 0-360 (hue)
  , s :: Number -- 0-1 (saturation)
  , l :: Number -- 0-1 (lightness)
  }

-- | RGB color type (0-255)
type RGB =
  { r :: Int
  , g :: Int
  , b :: Int
  }

--------------------------------------------------------------------------------
-- sRGB <-> Linear RGB Conversion
--------------------------------------------------------------------------------

-- | Convert sRGB component (0-255) to linear RGB (0-1)
sRGBToLinear :: Number -> Number
sRGBToLinear value =
  let v = value / 255.0
  in if v <= 0.04045
     then v / 12.92
     else Number.pow ((v + 0.055) / 1.055) 2.4

-- | Convert linear RGB (0-1) to sRGB component (0-255)
linearToSRGB :: Number -> Int
linearToSRGB value =
  let v = if value <= 0.0031308
          then value * 12.92
          else 1.055 * Number.pow value (1.0 / 2.4) - 0.055
  in round (max 0.0 (min 255.0 (v * 255.0)))

--------------------------------------------------------------------------------
-- Conversion Matrices
--------------------------------------------------------------------------------

-- | sRGB to XYZ matrix coefficients (D65)
srgbToXyzR :: { c0 :: Number, c1 :: Number, c2 :: Number }
srgbToXyzR = { c0: 0.4124564, c1: 0.3575761, c2: 0.1804375 }

srgbToXyzG :: { c0 :: Number, c1 :: Number, c2 :: Number }
srgbToXyzG = { c0: 0.2126729, c1: 0.7151522, c2: 0.072175 }

srgbToXyzB :: { c0 :: Number, c1 :: Number, c2 :: Number }
srgbToXyzB = { c0: 0.0193339, c1: 0.119192, c2: 0.9503041 }

-- | XYZ to sRGB matrix coefficients (D65)
xyzToSrgbR :: { c0 :: Number, c1 :: Number, c2 :: Number }
xyzToSrgbR = { c0: 3.2404542, c1: -1.5371385, c2: -0.4985314 }

xyzToSrgbG :: { c0 :: Number, c1 :: Number, c2 :: Number }
xyzToSrgbG = { c0: -0.969266, c1: 1.8760108, c2: 0.041556 }

xyzToSrgbB :: { c0 :: Number, c1 :: Number, c2 :: Number }
xyzToSrgbB = { c0: 0.0556434, c1: -0.2040259, c2: 1.0572252 }

--------------------------------------------------------------------------------
-- RGB <-> XYZ Conversion
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) to XYZ color space
rgbToXyz :: Number -> Number -> Number -> XYZ
rgbToXyz r g b =
  let rLinear = sRGBToLinear r
      gLinear = sRGBToLinear g
      bLinear = sRGBToLinear b
  in { x: (rLinear * srgbToXyzR.c0 + gLinear * srgbToXyzR.c1 + bLinear * srgbToXyzR.c2) * 100.0
     , y: (rLinear * srgbToXyzG.c0 + gLinear * srgbToXyzG.c1 + bLinear * srgbToXyzG.c2) * 100.0
     , z: (rLinear * srgbToXyzB.c0 + gLinear * srgbToXyzB.c1 + bLinear * srgbToXyzB.c2) * 100.0
     }

-- | Convert XYZ to RGB (0-255)
xyzToRgb :: Number -> Number -> Number -> RGB
xyzToRgb xVal yVal zVal =
  let x = xVal / 100.0
      y = yVal / 100.0
      z = zVal / 100.0
      rLinear = x * xyzToSrgbR.c0 + y * xyzToSrgbR.c1 + z * xyzToSrgbR.c2
      gLinear = x * xyzToSrgbG.c0 + y * xyzToSrgbG.c1 + z * xyzToSrgbG.c2
      bLinear = x * xyzToSrgbB.c0 + y * xyzToSrgbB.c1 + z * xyzToSrgbB.c2
  in { r: linearToSRGB rLinear
     , g: linearToSRGB gLinear
     , b: linearToSRGB bLinear
     }

--------------------------------------------------------------------------------
-- XYZ <-> LAB Conversion
--------------------------------------------------------------------------------

-- | Lab f(t) function for XYZ to LAB conversion
labF :: Number -> Number
labF t =
  let delta = 6.0 / 29.0
      delta3 = delta * delta * delta
  in if t > delta3
     then Number.pow t (1.0 / 3.0)
     else t / (3.0 * delta * delta) + 4.0 / 29.0

-- | Inverse Lab f(t) function for LAB to XYZ conversion
labFInverse :: Number -> Number
labFInverse t =
  let delta = 6.0 / 29.0
  in if t > delta
     then t * t * t
     else 3.0 * delta * delta * (t - 4.0 / 29.0)

-- | Convert XYZ to CIE LAB
xyzToLab :: Number -> Number -> Number -> LAB
xyzToLab xVal yVal zVal =
  let xn = xVal / d65X
      yn = yVal / d65Y
      zn = zVal / d65Z
      fx = labF xn
      fy = labF yn
      fz = labF zn
  in { l: 116.0 * fy - 16.0
     , a: 500.0 * (fx - fy)
     , b: 200.0 * (fy - fz)
     }

-- | Convert CIE LAB to XYZ
labToXyz :: Number -> Number -> Number -> XYZ
labToXyz lVal aVal bVal =
  let fy = (lVal + 16.0) / 116.0
      fx = aVal / 500.0 + fy
      fz = fy - bVal / 200.0
  in { x: d65X * labFInverse fx
     , y: d65Y * labFInverse fy
     , z: d65Z * labFInverse fz
     }

--------------------------------------------------------------------------------
-- RGB <-> LAB Direct Conversion
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) directly to CIE LAB
rgbToLab :: Number -> Number -> Number -> LAB
rgbToLab r g b =
  let xyz = rgbToXyz r g b
  in xyzToLab xyz.x xyz.y xyz.z

-- | Convert CIE LAB directly to RGB (0-255)
labToRgb :: Number -> Number -> Number -> RGB
labToRgb lVal aVal bVal =
  let xyz = labToXyz lVal aVal bVal
  in xyzToRgb xyz.x xyz.y xyz.z

--------------------------------------------------------------------------------
-- Color Difference (Delta E)
--------------------------------------------------------------------------------

-- | Calculate Delta E (CIE76) - basic Euclidean distance in LAB space
deltaE76 :: LAB -> LAB -> Number
deltaE76 lab1 lab2 =
  let dL = lab1.l - lab2.l
      da = lab1.a - lab2.a
      db = lab1.b - lab2.b
  in Number.sqrt (dL * dL + da * da + db * db)

-- | Calculate Delta E (CIE94) - weighted formula for graphics applications
deltaE94 :: LAB -> LAB -> Number
deltaE94 lab1 lab2 =
  let kL = 1.0
      kC = 1.0
      kH = 1.0
      k1 = 0.045
      k2 = 0.015
      dL = lab1.l - lab2.l
      c1 = Number.sqrt (lab1.a * lab1.a + lab1.b * lab1.b)
      c2 = Number.sqrt (lab2.a * lab2.a + lab2.b * lab2.b)
      dC = c1 - c2
      da = lab1.a - lab2.a
      db = lab1.b - lab2.b
      dH2 = da * da + db * db - dC * dC
      dH = if dH2 > 0.0 then Number.sqrt dH2 else 0.0
      sL = 1.0
      sC = 1.0 + k1 * c1
      sH = 1.0 + k2 * c1
      term1 = dL / (kL * sL)
      term2 = dC / (kC * sC)
      term3 = dH / (kH * sH)
  in Number.sqrt (term1 * term1 + term2 * term2 + term3 * term3)

--------------------------------------------------------------------------------
-- RGB <-> YUV Conversion
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) to YUV (BT.709)
rgbToYuv :: Number -> Number -> Number -> YUV
rgbToYuv r g b =
  let rn = r / 255.0
      gn = g / 255.0
      bn = b / 255.0
      y' = bt709R * rn + bt709G * gn + bt709B * bn
      u' = (0.5 * (bn - y')) / (1.0 - bt709B)
      v' = (0.5 * (rn - y')) / (1.0 - bt709R)
  in { y: y', u: u', v: v' }

-- | Convert YUV to RGB (0-255)
yuvToRgb :: Number -> Number -> Number -> RGB
yuvToRgb y' u' v' =
  let r = y' + 2.0 * v' * (1.0 - bt709R)
      g = y' - (2.0 * u' * bt709B * (1.0 - bt709B)) / bt709G -
              (2.0 * v' * bt709R * (1.0 - bt709R)) / bt709G
      b = y' + 2.0 * u' * (1.0 - bt709B)
      clampRgb val = round (max 0.0 (min 255.0 (val * 255.0)))
  in { r: clampRgb r, g: clampRgb g, b: clampRgb b }

--------------------------------------------------------------------------------
-- RGB <-> HSL Conversion
--------------------------------------------------------------------------------

-- | Convert RGB (0-255) to HSL
rgbToHsl :: Number -> Number -> Number -> HSL
rgbToHsl r g b =
  let rn = r / 255.0
      gn = g / 255.0
      bn = b / 255.0
      maxC = max rn (max gn bn)
      minC = min rn (min gn bn)
      l = (maxC + minC) / 2.0
  in if maxC == minC
     then { h: 0.0, s: 0.0, l }
     else
       let d = maxC - minC
           s = if l > 0.5 then d / (2.0 - maxC - minC) else d / (maxC + minC)
           h = if maxC == rn then ((gn - bn) / d + (if gn < bn then 6.0 else 0.0)) / 6.0
               else if maxC == gn then ((bn - rn) / d + 2.0) / 6.0
               else ((rn - gn) / d + 4.0) / 6.0
       in { h: h * 360.0, s, l }

-- | Helper for HSL to RGB conversion
hue2rgb :: Number -> Number -> Number -> Number
hue2rgb p q t' =
  let t = if t' < 0.0 then t' + 1.0 else if t' > 1.0 then t' - 1.0 else t'
  in if t < 1.0 / 6.0 then p + (q - p) * 6.0 * t
     else if t < 0.5 then q
     else if t < 2.0 / 3.0 then p + (q - p) * (2.0 / 3.0 - t) * 6.0
     else p

-- | Float modulo helper
fmod :: Number -> Number -> Number
fmod a m = a - m * Math.floor (a / m)

-- | Convert HSL to RGB (0-255)
hslToRgb :: Number -> Number -> Number -> RGB
hslToRgb h s l =
  let h' = fmod (fmod h 360.0 + 360.0) 360.0 / 360.0
  in if s == 0.0
     then let v = round (l * 255.0) in { r: v, g: v, b: v }
     else
       let q = if l < 0.5 then l * (1.0 + s) else l + s - l * s
           p = 2.0 * l - q
       in { r: round (hue2rgb p q (h' + 1.0 / 3.0) * 255.0)
          , g: round (hue2rgb p q h' * 255.0)
          , b: round (hue2rgb p q (h' - 1.0 / 3.0) * 255.0)
          }

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Calculate luminance (BT.709) from RGB (0-255)
rgbToLuminance :: Number -> Number -> Number -> Number
rgbToLuminance r g b = bt709R * r + bt709G * g + bt709B * b

-- | Check if a color is within a tolerance of neutral gray
isNeutral :: Number -> Number -> Number -> Number -> Boolean
isNeutral r g b tolerance =
  let lab = rgbToLab r g b
  in Number.abs lab.a < tolerance && Number.abs lab.b < tolerance

-- | Get the complementary color
complementary :: Number -> Number -> Number -> RGB
complementary r g b =
  let hsl = rgbToHsl r g b
  in hslToRgb (fmod (hsl.h + 180.0) 360.0) hsl.s hsl.l

-- | Clamp a value between min and max
clamp :: Number -> Number -> Number -> Number
clamp val minVal maxVal = max minVal (min maxVal val)

-- | Linear interpolation between two values
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Smoothstep function for smooth transitions
smoothstep :: Number -> Number -> Number -> Number
smoothstep edge0 edge1 x =
  let t = clamp ((x - edge0) / (edge1 - edge0)) 0.0 1.0
  in t * t * (3.0 - 2.0 * t)
