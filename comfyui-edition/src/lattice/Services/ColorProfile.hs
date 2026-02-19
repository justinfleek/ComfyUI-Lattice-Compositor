-- |
-- Module      : Lattice.Services.ColorProfile
-- Description : Pure color space conversion functions
-- 
-- Migrated from ui/src/services/colorManagement/ColorProfileService.ts
-- Pure color space conversions and transfer functions
-- Note: ICC profile parsing deferred (uses ArrayBuffer)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.ColorProfile
  ( -- Transfer functions
    sRGBToLinear
  , linearToSRGB
  , gammaToLinear
  , linearToGamma
  --                                                                       // rgb
  , linearizeRGB
  , applyGammaRGB
  -- Matrix operations
  , matrixMultiply3x3
  -- Color space conversions
  , rgbToXYZ
  , xyzToRGB
  , convertColorSpace
  -- Types
  , ColorSpace(..)
  , RGB(..)
  , XYZ(..)
  , Matrix3x3
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety
  ( ensureFinite
  , safePow
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Color space enum
data ColorSpace
  = ColorSpaceSRGB
  | ColorSpaceLinearSRGB
  | ColorSpaceWideGamutRGB
  | ColorSpaceDisplayP3
  | ColorSpaceProPhotoRGB
  | ColorSpaceACEScg
  | ColorSpaceRec709
  | ColorSpaceRec2020
  deriving (Eq, Show)

-- | RGB color tuple (0-1 normalized)
data RGB = RGB
  { rgbR :: Double
  , rgbG :: Double
  , rgbB :: Double
  }
  deriving (Eq, Show)

-- | XYZ color tuple
data XYZ = XYZ
  { xyzX :: Double
  , xyzY :: Double
  , xyzZ :: Double
  }
  deriving (Eq, Show)

-- | 3x3 matrix type
type Matrix3x3 = ((Double, Double, Double), (Double, Double, Double), (Double, Double, Double))

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // transfer // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | sRGB transfer function (linearize)
sRGBToLinear :: Double -> Double
sRGBToLinear value =
  let finiteValue = ensureFinite value 0.0
  in if finiteValue <= 0.04045
     then finiteValue / 12.92
     else safePow ((finiteValue + 0.055) / 1.055) 2.4 0.0

-- | sRGB inverse transfer function (apply gamma)
linearToSRGB :: Double -> Double
linearToSRGB value =
  let finiteValue = ensureFinite value 0.0
  in if finiteValue <= 0.0031308
     then finiteValue * 12.92
     else 1.055 * safePow finiteValue (1.0 / 2.4) 0.0 - 0.055

-- | Simple gamma transfer function
gammaToLinear :: Double -> Double -> Double
gammaToLinear value gamma =
  let finiteValue = if ensureFinite value 0.0 < 0.0 then 0.0 else ensureFinite value 0.0
      finiteGamma = ensureFinite gamma 2.2
  in safePow finiteValue finiteGamma 0.0

-- | Simple gamma inverse transfer function
linearToGamma :: Double -> Double -> Double
linearToGamma value gamma =
  let finiteValue = if ensureFinite value 0.0 < 0.0 then 0.0 else ensureFinite value 0.0
      finiteGamma = ensureFinite gamma 2.2
      invGamma = if finiteGamma /= 0.0 then 1.0 / finiteGamma else 1.0
  in safePow finiteValue invGamma 0.0

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // rgb // linearization
-- ════════════════════════════════════════════════════════════════════════════

-- | Linearize RGB based on color space
linearizeRGB :: RGB -> ColorSpace -> RGB
linearizeRGB (RGB r g b) colorSpace =
  case colorSpace of
    ColorSpaceLinearSRGB -> RGB r g b
    ColorSpaceSRGB ->
      RGB (sRGBToLinear r) (sRGBToLinear g) (sRGBToLinear b)
    ColorSpaceRec709 ->
      RGB (gammaToLinear r 2.4) (gammaToLinear g 2.4) (gammaToLinear b 2.4)
    ColorSpaceWideGamutRGB ->
      RGB (gammaToLinear r 2.2) (gammaToLinear g 2.2) (gammaToLinear b 2.2)
    ColorSpaceDisplayP3 ->
      RGB (gammaToLinear r 2.2) (gammaToLinear g 2.2) (gammaToLinear b 2.2)
    ColorSpaceProPhotoRGB ->
      RGB (gammaToLinear r 1.8) (gammaToLinear g 1.8) (gammaToLinear b 1.8)
    ColorSpaceACEScg -> RGB r g b  -- Already linear
    ColorSpaceRec2020 ->
      RGB (gammaToLinear r 2.4) (gammaToLinear g 2.4) (gammaToLinear b 2.4)

-- | Apply gamma to linear RGB
applyGammaRGB :: RGB -> ColorSpace -> RGB
applyGammaRGB (RGB r g b) colorSpace =
  case colorSpace of
    ColorSpaceLinearSRGB -> RGB r g b
    ColorSpaceACEScg -> RGB r g b  -- Already linear
    ColorSpaceSRGB ->
      RGB (linearToSRGB r) (linearToSRGB g) (linearToSRGB b)
    ColorSpaceRec709 ->
      RGB (linearToGamma r 2.4) (linearToGamma g 2.4) (linearToGamma b 2.4)
    ColorSpaceWideGamutRGB ->
      RGB (linearToGamma r 2.2) (linearToGamma g 2.2) (linearToGamma b 2.2)
    ColorSpaceDisplayP3 ->
      RGB (linearToGamma r 2.2) (linearToGamma g 2.2) (linearToGamma b 2.2)
    ColorSpaceProPhotoRGB ->
      RGB (linearToGamma r 1.8) (linearToGamma g 1.8) (linearToGamma b 1.8)
    ColorSpaceRec2020 ->
      RGB (linearToGamma r 2.4) (linearToGamma g 2.4) (linearToGamma b 2.4)

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // matrix // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | 3x3 matrix-vector multiplication
matrixMultiply3x3 :: Matrix3x3 -> (Double, Double, Double) -> (Double, Double, Double)
matrixMultiply3x3 ((m00, m01, m02), (m10, m11, m12), (m20, m21, m22)) (v0, v1, v2) =
  let r0 = m00 * v0 + m01 * v1 + m02 * v2
      r1 = m10 * v0 + m11 * v1 + m12 * v2
      r2 = m20 * v0 + m21 * v1 + m22 * v2
  in (ensureFinite r0 0.0, ensureFinite r1 0.0, ensureFinite r2 0.0)

-- ════════════════════════════════════════════════════════════════════════════
--                                  // color // space // conversion // matrices
-- ════════════════════════════════════════════════════════════════════════════

-- sRGB to XYZ (D65)
sRGBToXYZMatrix :: Matrix3x3
sRGBToXYZMatrix =
  ((0.4124564, 0.3575761, 0.1804375),
   (0.2126729, 0.7151522, 0.072175),
   (0.0193339, 0.119192, 0.9503041))

--                                                                       // xyz
xyzToSRGBMatrix :: Matrix3x3
xyzToSRGBMatrix =
  ((3.2404542, -1.5371385, -0.4985314),
   (-0.969266, 1.8760108, 0.041556),
   (0.0556434, -0.2040259, 1.0572252))

-- Display P3 to XYZ (D65)
p3ToXYZMatrix :: Matrix3x3
p3ToXYZMatrix =
  ((0.4865709, 0.2656677, 0.1982173),
   (0.2289746, 0.6917385, 0.0792869),
   (0.0, 0.0451134, 1.0439444))

--                                                                       // xyz
xyzToP3Matrix :: Matrix3x3
xyzToP3Matrix =
  ((2.4934969, -0.9313836, -0.4027108),
   (-0.829489, 1.7626641, 0.0236247),
   (0.0358458, -0.0761724, 0.9568845))

-- Wide-Gamut RGB to XYZ (D65)
wideGamutRGBToXYZMatrix :: Matrix3x3
wideGamutRGBToXYZMatrix =
  ((0.5767309, 0.185554, 0.1881852),
   (0.2973769, 0.6273491, 0.0752741),
   (0.0270343, 0.0706872, 0.9911085))

--                                                                       // xyz
xyzToWideGamutRGBMatrix :: Matrix3x3
xyzToWideGamutRGBMatrix =
  ((2.041369, -0.5649464, -0.3446944),
   (-0.969266, 1.8760108, 0.041556),
   (0.0134474, -0.1183897, 1.0154096))

-- ════════════════════════════════════════════════════════════════════════════
--                                             // color // space // conversions
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to XYZ color space
rgbToXYZ :: RGB -> ColorSpace -> XYZ
rgbToXYZ rgb colorSpace =
  let linearRGB = linearizeRGB rgb colorSpace
      (r, g, b) = (rgbR linearRGB, rgbG linearRGB, rgbB linearRGB)
      (x, y, z) = case colorSpace of
        ColorSpaceSRGB -> matrixMultiply3x3 sRGBToXYZMatrix (r, g, b)
        ColorSpaceLinearSRGB -> matrixMultiply3x3 sRGBToXYZMatrix (r, g, b)
        ColorSpaceRec709 -> matrixMultiply3x3 sRGBToXYZMatrix (r, g, b)
        ColorSpaceDisplayP3 -> matrixMultiply3x3 p3ToXYZMatrix (r, g, b)
        ColorSpaceWideGamutRGB -> matrixMultiply3x3 wideGamutRGBToXYZMatrix (r, g, b)
        _ -> matrixMultiply3x3 sRGBToXYZMatrix (r, g, b)  -- Default to sRGB
  in XYZ x y z

-- | Convert XYZ to RGB color space
xyzToRGB :: XYZ -> ColorSpace -> RGB
xyzToRGB (XYZ x y z) colorSpace =
  let (linearR, linearG, linearB) = case colorSpace of
        ColorSpaceSRGB -> matrixMultiply3x3 xyzToSRGBMatrix (x, y, z)
        ColorSpaceLinearSRGB -> matrixMultiply3x3 xyzToSRGBMatrix (x, y, z)
        ColorSpaceRec709 -> matrixMultiply3x3 xyzToSRGBMatrix (x, y, z)
        ColorSpaceDisplayP3 -> matrixMultiply3x3 xyzToP3Matrix (x, y, z)
        ColorSpaceWideGamutRGB -> matrixMultiply3x3 xyzToWideGamutRGBMatrix (x, y, z)
        _ -> matrixMultiply3x3 xyzToSRGBMatrix (x, y, z)  -- Default to sRGB
      linearRGB = RGB linearR linearG linearB
  in applyGammaRGB linearRGB colorSpace

-- | Convert RGB from one color space to another
convertColorSpace :: RGB -> ColorSpace -> ColorSpace -> RGB
convertColorSpace rgb from to
  | from == to = rgb
  | from == ColorSpaceLinearSRGB && to == ColorSpaceSRGB =
      applyGammaRGB rgb ColorSpaceSRGB
  | from == ColorSpaceSRGB && to == ColorSpaceLinearSRGB =
      linearizeRGB rgb ColorSpaceSRGB
  | otherwise =
      let xyz = rgbToXYZ rgb from
      in xyzToRGB xyz to
