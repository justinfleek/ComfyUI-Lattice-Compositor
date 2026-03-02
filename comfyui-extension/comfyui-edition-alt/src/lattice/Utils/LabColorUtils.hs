-- |
-- Module      : Lattice.Utils.LabColorUtils
-- Description : LAB Color Space Utilities for CIE LAB, XYZ, and YUV conversions
-- 
-- Migrated from ui/src/utils/labColorUtils.ts
-- Pure color space conversion functions for professional color correction
-- Uses D65 illuminant (standard for sRGB)
--                                                                  // lab // l
--

module Lattice.Utils.LabColorUtils
  ( -- Types
    LAB(..)
  , XYZ(..)
  , YUV(..)
  -- Constants
  , bt709R
  , bt709G
  , bt709B
  -- sRGB <-> Linear RGB
  , sRGBToLinear
  , linearToSRGB
  --                                                                       // rgb
  , rgbToXyz
  , xyzToRgb
  --                                                                       // xyz
  , xyzToLab
  , labToXyz
  --                                                                       // rgb
  , rgbToLab
  , labToRgb
  -- Color Difference (Delta E)
  , deltaE76
  , deltaE94
  , deltaE2000
  --                                                                       // rgb
  , rgbToYuv
  , yuvToRgb
  --                                                                       // rgb
  , rgbToHslLab
  , hslToRgbLab
  -- Utility Functions
  , rgbToLuminance
  , isNeutral
  , complementary
  ) where

import Lattice.Utils.NumericSafety
  ( clamp
  , safeMod
  )
import Lattice.Utils.ArrayUtils (safeArrayGet)
import Prelude hiding (pi)
import qualified Prelude as P

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | LAB color type
data LAB = LAB
  { labL :: Double  -- 0-100
  , labA :: Double  -- -128 to +127 (green to red)
  , labB :: Double  -- -128 to +127 (blue to yellow)
  } deriving (Eq, Show)

-- | XYZ color type
data XYZ = XYZ
  { xyzX :: Double
  , xyzY :: Double
  , xyzZ :: Double
  } deriving (Eq, Show)

-- | YUV color type (for vectorscope)
data YUV = YUV
  { yuvY :: Double  -- Luminance (0-1)
  , yuvU :: Double  -- Blue-Yellow chrominance (-0.5 to +0.5)
  , yuvV :: Double  -- Red-Cyan chrominance (-0.5 to +0.5)
  } deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // constants
-- ════════════════════════════════════════════════════════════════════════════

--                                                                       // d65
d65_X :: Double
d65_X = 95.047

d65_Y :: Double
d65_Y = 100.0

d65_Z :: Double
d65_Z = 108.883

-- sRGB to XYZ conversion matrix (D65)
sRGBToXYZMatrix :: [[Double]]
sRGBToXYZMatrix =
  [ [0.4124564, 0.3575761, 0.1804375]
  , [0.2126729, 0.7151522, 0.072175]
  , [0.0193339, 0.119192, 0.9503041]
  ]

--                                                                       // xyz
xyzToSRGBMatrix :: [[Double]]
xyzToSRGBMatrix =
  [ [3.2404542, -1.5371385, -0.4985314]
  , [-0.969266, 1.8760108, 0.041556]
  , [0.0556434, -0.2040259, 1.0572252]
  ]

--                                                                        // bt
bt709R :: Double
bt709R = 0.2126

bt709G :: Double
bt709G = 0.7152

bt709B :: Double
bt709B = 0.0722

-- ════════════════════════════════════════════════════════════════════════════
-- sRGB <-> Linear RGB Conversion
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert sRGB component (0-255) to linear RGB (0-1)
-- Applies inverse gamma correction
sRGBToLinear :: Double -> Double
sRGBToLinear value =
  let v = value / 255
  in if v <= 0.04045
    then v / 12.92
    else ((v + 0.055) / 1.055) ** 2.4

-- | Convert linear RGB (0-1) to sRGB component (0-255)
-- Applies gamma correction
linearToSRGB :: Double -> Double
linearToSRGB value =
  let v = if value <= 0.0031308
        then value * 12.92
        else 1.055 * value ** (1 / 2.4) - 0.055
  in fromIntegral (round (clamp 0 255 (v * 255)))

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // rgb
-- ════════════════════════════════════════════════════════════════════════════

-- | Safe matrix element access for 3x3 matrices
matrixGet :: [[Double]] -> Int -> Int -> Double -> Double
matrixGet matrix row col defaultVal =
  let rowList = safeArrayGet matrix row []
      element = safeArrayGet rowList col defaultVal
  in element

-- | Convert RGB (0-255) to XYZ color space
rgbToXyz :: Double -> Double -> Double -> XYZ
rgbToXyz r g b =
  let rLinear = sRGBToLinear r
      gLinear = sRGBToLinear g
      bLinear = sRGBToLinear b
      -- Apply matrix transformation
      x = rLinear * matrixGet sRGBToXYZMatrix 0 0 0.0 +
          gLinear * matrixGet sRGBToXYZMatrix 0 1 0.0 +
          bLinear * matrixGet sRGBToXYZMatrix 0 2 0.0
      y = rLinear * matrixGet sRGBToXYZMatrix 1 0 0.0 +
          gLinear * matrixGet sRGBToXYZMatrix 1 1 0.0 +
          bLinear * matrixGet sRGBToXYZMatrix 1 2 0.0
      z = rLinear * matrixGet sRGBToXYZMatrix 2 0 0.0 +
          gLinear * matrixGet sRGBToXYZMatrix 2 1 0.0 +
          bLinear * matrixGet sRGBToXYZMatrix 2 2 0.0
  in XYZ (x * 100) (y * 100) (z * 100)

-- | Convert XYZ to RGB (0-255)
xyzToRgb :: Double -> Double -> Double -> (Double, Double, Double)
xyzToRgb x y z =
  let -- Normalize XYZ values
      x' = x / 100
      y' = y / 100
      z' = z / 100
      -- Apply matrix transformation to get linear RGB
      rLinear = x' * matrixGet xyzToSRGBMatrix 0 0 0.0 +
                y' * matrixGet xyzToSRGBMatrix 0 1 0.0 +
                z' * matrixGet xyzToSRGBMatrix 0 2 0.0
      gLinear = x' * matrixGet xyzToSRGBMatrix 1 0 0.0 +
                y' * matrixGet xyzToSRGBMatrix 1 1 0.0 +
                z' * matrixGet xyzToSRGBMatrix 1 2 0.0
      bLinear = x' * matrixGet xyzToSRGBMatrix 2 0 0.0 +
                y' * matrixGet xyzToSRGBMatrix 2 1 0.0 +
                z' * matrixGet xyzToSRGBMatrix 2 2 0.0
  in (linearToSRGB rLinear, linearToSRGB gLinear, linearToSRGB bLinear)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // xyz
-- ════════════════════════════════════════════════════════════════════════════

-- | Lab f(t) function for XYZ to LAB conversion
labF :: Double -> Double
labF t =
  let delta = 6 / 29
      delta3 = delta * delta * delta
  in if t > delta3
    then t ** (1 / 3)
    else t / (3 * delta * delta) + 4 / 29

-- | Inverse Lab f(t) function for LAB to XYZ conversion
labFInverse :: Double -> Double
labFInverse t =
  let delta = 6 / 29
  in if t > delta
    then t * t * t
    else 3 * delta * delta * (t - 4 / 29)

-- | Convert XYZ to CIE LAB
xyzToLab :: Double -> Double -> Double -> LAB
xyzToLab x y z =
  let xn = x / d65_X
      yn = y / d65_Y
      zn = z / d65_Z
      fx = labF xn
      fy = labF yn
      fz = labF zn
  in LAB
    { labL = 116 * fy - 16
    , labA = 500 * (fx - fy)
    , labB = 200 * (fy - fz)
    }

-- | Convert CIE LAB to XYZ
labToXyz :: Double -> Double -> Double -> XYZ
labToXyz l a b =
  let fy = (l + 16) / 116
      fx = a / 500 + fy
      fz = fy - b / 200
  in XYZ
    { xyzX = d65_X * labFInverse fx
    , xyzY = d65_Y * labFInverse fy
    , xyzZ = d65_Z * labFInverse fz
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // rgb
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert RGB (0-255) directly to CIE LAB
rgbToLab :: Double -> Double -> Double -> LAB
rgbToLab r g b =
  let xyz = rgbToXyz r g b
  in xyzToLab (xyzX xyz) (xyzY xyz) (xyzZ xyz)

-- | Convert CIE LAB directly to RGB (0-255)
labToRgb :: Double -> Double -> Double -> (Double, Double, Double)
labToRgb l a b =
  let xyz = labToXyz l a b
  in xyzToRgb (xyzX xyz) (xyzY xyz) (xyzZ xyz)

-- ════════════════════════════════════════════════════════════════════════════
-- Color Difference (Delta E)
-- ════════════════════════════════════════════════════════════════════════════

-- | Calculate Delta E (CIE76) - basic Euclidean distance in LAB space
-- Values interpretation:
-- - 0-1: Not perceptible by human eyes
-- - 1-2: Perceptible through close observation
-- - 2-10: Perceptible at a glance
-- - 11-49: Colors are more similar than opposite
-- - 100: Colors are exact opposite
deltaE76 :: LAB -> LAB -> Double
deltaE76 lab1 lab2 =
  let dL = labL lab1 - labL lab2
      da = labA lab1 - labA lab2
      db = labB lab1 - labB lab2
  in sqrt (dL * dL + da * da + db * db)

-- | Calculate Delta E (CIE94) - weighted formula for graphics applications
-- More perceptually uniform than CIE76
deltaE94 :: LAB -> LAB -> Double
deltaE94 lab1 lab2 =
  let -- Weighting factors for graphic arts
      kL = 1
      kC = 1
      kH = 1
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
      sL = 1
      sC = 1 + k1 * c1
      sH = 1 + k2 * c1
      term1 = dL / (kL * sL)
      term2 = dC / (kC * sC)
      term3 = dH / (kH * sH)
  in sqrt (term1 * term1 + term2 * term2 + term3 * term3)

-- | Calculate Delta E (CIEDE2000) - most accurate formula
-- Best for critical color matching applications
deltaE2000 :: LAB -> LAB -> Double
deltaE2000 lab1 lab2 =
  let l1 = labL lab1
      a1 = labA lab1
      b1 = labB lab1
      l2 = labL lab2
      a2 = labA lab2
      b2 = labB lab2
      -- Step 1: Calculate C'i and h'i
      c1 = sqrt (a1 * a1 + b1 * b1)
      c2 = sqrt (a2 * a2 + b2 * b2)
      cb = (c1 + c2) / 2
      g = 0.5 * (1 - sqrt (cb ** 7 / (cb ** 7 + 25 ** 7)))
      a1p = a1 * (1 + g)
      a2p = a2 * (1 + g)
      c1p = sqrt (a1p * a1p + b1 * b1)
      c2p = sqrt (a2p * a2p + b2 * b2)
      h1p = atan2 b1 a1p * 180 / P.pi
      h1pAdj = if h1p >= 0 then h1p else h1p + 360
      h2p = atan2 b2 a2p * 180 / P.pi
      h2pAdj = if h2p >= 0 then h2p else h2p + 360
      -- Step 2: Calculate dL', dC', dH'
      dLp = l2 - l1
      dCp = c2p - c1p
      dhp = if c1p * c2p == 0
        then 0
        else if abs (h2pAdj - h1pAdj) <= 180
          then h2pAdj - h1pAdj
          else if h2pAdj - h1pAdj > 180
            then h2pAdj - h1pAdj - 360
            else h2pAdj - h1pAdj + 360
      dHp = 2 * sqrt (c1p * c2p) * sin (dhp * P.pi / 360)
      -- Step 3: Calculate CIEDE2000
      lbp = (l1 + l2) / 2
      cbp = (c1p + c2p) / 2
      hbp = if c1p * c2p == 0
        then h1pAdj + h2pAdj
        else if abs (h1pAdj - h2pAdj) <= 180
          then (h1pAdj + h2pAdj) / 2
          else if h1pAdj + h2pAdj < 360
            then (h1pAdj + h2pAdj + 360) / 2
            else (h1pAdj + h2pAdj - 360) / 2
      t = 1 -
          0.17 * cos ((hbp - 30) * P.pi / 180) +
          0.24 * cos (2 * hbp * P.pi / 180) +
          0.32 * cos ((3 * hbp + 6) * P.pi / 180) -
          0.2 * cos ((4 * hbp - 63) * P.pi / 180)
      dTheta = 30 * P.exp (-(((hbp - 275) / 25) ** 2))
      rC = 2 * sqrt (cbp ** 7 / (cbp ** 7 + 25 ** 7))
      sL = 1 + (0.015 * (lbp - 50) ** 2) / sqrt (20 + (lbp - 50) ** 2)
      sC = 1 + 0.045 * cbp
      sH = 1 + 0.015 * cbp * t
      rT = -sin (2 * dTheta * P.pi / 180) * rC
      kL = 1
      kC = 1
      kH = 1
  in sqrt
    ((dLp / (kL * sL)) ** 2 +
     (dCp / (kC * sC)) ** 2 +
     (dHp / (kH * sH)) ** 2 +
     rT * (dCp / (kC * sC)) * (dHp / (kH * sH)))

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // rgb
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert RGB (0-255) to YUV (BT.709)
-- Used for vectorscope display
rgbToYuv :: Double -> Double -> Double -> YUV
rgbToYuv r g b =
  let rn = r / 255
      gn = g / 255
      bn = b / 255
      --                                                                        // bt
      y = bt709R * rn + bt709G * gn + bt709B * bn
      u = (0.5 * (bn - y)) / (1 - bt709B)
      v = (0.5 * (rn - y)) / (1 - bt709R)
  in YUV y u v

-- | Convert YUV to RGB (0-255)
yuvToRgb :: Double -> Double -> Double -> (Double, Double, Double)
yuvToRgb y u v =
  let r = y + 2 * v * (1 - bt709R)
      g = y -
          (2 * u * bt709B * (1 - bt709B)) / bt709G -
          (2 * v * bt709R * (1 - bt709R)) / bt709G
      b = y + 2 * u * (1 - bt709B)
  in ( fromIntegral (round (clamp 0 255 (r * 255)))
     , fromIntegral (round (clamp 0 255 (g * 255)))
     , fromIntegral (round (clamp 0 255 (b * 255)))
     )

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // rgb
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert RGB (0-255) to HSL
-- H: 0-360, S: 0-1, L: 0-1
rgbToHslLab :: Double -> Double -> Double -> (Double, Double, Double)
rgbToHslLab r g b =
  let rn = r / 255
      gn = g / 255
      bn = b / 255
      maxVal = maximum [rn, gn, bn]
      minVal = minimum [rn, gn, bn]
      l = (maxVal + minVal) / 2
  in if maxVal == minVal
    then (0, 0, l)  -- achromatic
    else let d = maxVal - minVal
             s = if l > 0.5 then d / (2 - maxVal - minVal) else d / (maxVal + minVal)
             h = case () of
               _ | maxVal == rn -> ((gn - bn) / d + (if gn < bn then 6 else 0)) / 6
               _ | maxVal == gn -> ((bn - rn) / d + 2) / 6
               _ -> ((rn - gn) / d + 4) / 6
         in (h * 360, s, l)

-- | Convert HSL to RGB (0-255)
-- H: 0-360, S: 0-1, L: 0-1
hslToRgbLab :: Double -> Double -> Double -> (Double, Double, Double)
hslToRgbLab h s l =
  let h' = safeMod h 360 / 360  -- Normalize hue
  in if s == 0
    then let v = round (l * 255)
         in (fromIntegral v, fromIntegral v, fromIntegral v)
    else let
      q = if l < 0.5 then l * (1 + s) else l + s - l * s
      p = 2 * l - q
      hue2rgb p' q' t =
        let tNorm = ( (if t < 0 then t + 1 else (if t > 1 then t - 1 else t)) )
        in (if tNorm < 1 / 6 then p' + (q' - p') * 6 * tNorm
            else if tNorm < 1 / 2 then q'
            else if tNorm < 2 / 3 then p' + (q' - p') * (2 / 3 - tNorm) * 6
            else p')
    in ( fromIntegral (round (hue2rgb p q (h' + 1 / 3) * 255))
       , fromIntegral (round (hue2rgb p q h' * 255))
       , fromIntegral (round (hue2rgb p q (h' - 1 / 3) * 255))
       )

-- ════════════════════════════════════════════════════════════════════════════
-- Utility Functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Calculate luminance (BT.709) from RGB (0-255)
-- Returns 0-255
rgbToLuminance :: Double -> Double -> Double -> Double
rgbToLuminance r g b = fromIntegral (round (bt709R * r + bt709G * g + bt709B * b))

-- | Check if a color is within a tolerance of neutral gray
-- Uses LAB a* and b* components
isNeutral :: Double -> Double -> Double -> Double -> Bool
isNeutral r g b tolerance =
  let lab = rgbToLab r g b
  in abs (labA lab) < tolerance && abs (labB lab) < tolerance

-- | Get the complementary color
complementary :: Double -> Double -> Double -> (Double, Double, Double)
complementary r g b =
  let (h, s, l) = rgbToHslLab r g b
  in hslToRgbLab ((h + 180) `mod'` 360) s l
  where
    mod' :: Double -> Double -> Double
    mod' x y = fromIntegral (floor x `mod` floor y)
