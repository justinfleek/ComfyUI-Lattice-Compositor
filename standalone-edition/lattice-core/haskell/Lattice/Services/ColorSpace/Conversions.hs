{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.ColorSpace.Conversions
Description : Color Space Conversions
Copyright   : (c) Lattice, 2026
License     : MIT

Pure color space conversion algorithms:
- RGB ↔ XYZ via matrix transformation
- Color space primaries and white points
- Conversion between any two color spaces

Source: ui/src/services/colorManagement/ColorProfileService.ts
-}

module Lattice.Services.ColorSpace.Conversions
  ( -- * Types
    XYZ(..), Matrix3x3(..), ColorSpaceId(..)
    -- * Matrix Operations
  , mkMatrix, matrixMultiplyRGB, matrixMultiplyXYZ
    -- * Color Space Matrices
  , srgbToXYZ, xyzToSRGB
  , p3ToXYZ, xyzToP3
  , wideGamutRGBToXYZ, xyzToWideGamutRGB
  , proPhotoToXYZ, xyzToProPhoto
  , acesCGToXYZ, xyzToACEScg
    -- * Color Space Accessors
  , getGamma, getToXYZMatrix, getFromXYZMatrix
    -- * Conversion Functions
  , rgbToXYZ, xyzToRGB, convertColorSpace
    -- * Utilities
  , getLuminance, isInGamut, clipToGamut, fromHex
  ) where

import Data.Char (digitToInt, isHexDigit)
import Lattice.Services.ColorSpace.TransferFunctions

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | XYZ tristimulus values
data XYZ = XYZ
  { xyzX :: Double
  , xyzY :: Double
  , xyzZ :: Double
  } deriving (Eq, Show)

-- | 3x3 color matrix
data Matrix3x3 = Matrix3x3
  { m00 :: Double, m01 :: Double, m02 :: Double
  , m10 :: Double, m11 :: Double, m12 :: Double
  , m20 :: Double, m21 :: Double, m22 :: Double
  } deriving (Eq, Show)

-- | Color space identifier
data ColorSpaceId
  = SRGB_CS
  | LinearSRGB
  | WideGamutRGB
  | DisplayP3
  | ProPhotoRGB
  | ACEScg
  | Rec709
  | Rec2020
  deriving (Eq, Show)

-- ────────────────────────────────────────────────────────────────────────────
-- Matrix Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Create matrix from row values
mkMatrix :: (Double, Double, Double) -> (Double, Double, Double)
         -> (Double, Double, Double) -> Matrix3x3
mkMatrix (r00, r01, r02) (r10, r11, r12) (r20, r21, r22) =
  Matrix3x3 r00 r01 r02 r10 r11 r12 r20 r21 r22

-- | Multiply matrix by RGB vector, producing XYZ
matrixMultiplyRGB :: Matrix3x3 -> RGB -> XYZ
matrixMultiplyRGB m (RGB r g b) = XYZ
  (m00 m * r + m01 m * g + m02 m * b)
  (m10 m * r + m11 m * g + m12 m * b)
  (m20 m * r + m21 m * g + m22 m * b)

-- | Multiply matrix by XYZ vector, producing RGB
matrixMultiplyXYZ :: Matrix3x3 -> XYZ -> RGB
matrixMultiplyXYZ m (XYZ x y z) = RGB
  (m00 m * x + m01 m * y + m02 m * z)
  (m10 m * x + m11 m * y + m12 m * z)
  (m20 m * x + m21 m * y + m22 m * z)

-- ────────────────────────────────────────────────────────────────────────────
-- Color Space Matrices
-- ────────────────────────────────────────────────────────────────────────────

-- | sRGB to XYZ (D65)
srgbToXYZ :: Matrix3x3
srgbToXYZ = mkMatrix
  (0.4124564, 0.3575761, 0.1804375)
  (0.2126729, 0.7151522, 0.072175)
  (0.0193339, 0.119192, 0.9503041)

-- | XYZ to sRGB (D65)
xyzToSRGB :: Matrix3x3
xyzToSRGB = mkMatrix
  (3.2404542, -1.5371385, -0.4985314)
  (-0.969266, 1.8760108, 0.041556)
  (0.0556434, -0.2040259, 1.0572252)

-- | Display P3 to XYZ (D65)
p3ToXYZ :: Matrix3x3
p3ToXYZ = mkMatrix
  (0.4865709, 0.2656677, 0.1982173)
  (0.2289746, 0.6917385, 0.0792869)
  (0.0, 0.0451134, 1.0439444)

-- | XYZ to Display P3 (D65)
xyzToP3 :: Matrix3x3
xyzToP3 = mkMatrix
  (2.4934969, -0.9313836, -0.4027108)
  (-0.829489, 1.7626641, 0.0236247)
  (0.0358458, -0.0761724, 0.9568845)

-- | Wide-Gamut RGB to XYZ (D65)
wideGamutRGBToXYZ :: Matrix3x3
wideGamutRGBToXYZ = mkMatrix
  (0.5767309, 0.185554, 0.1881852)
  (0.2973769, 0.6273491, 0.0752741)
  (0.0270343, 0.0706872, 0.9911085)

-- | XYZ to Wide-Gamut RGB (D65)
xyzToWideGamutRGB :: Matrix3x3
xyzToWideGamutRGB = mkMatrix
  (2.041369, -0.5649464, -0.3446944)
  (-0.969266, 1.8760108, 0.041556)
  (0.0134474, -0.1183897, 1.0154096)

-- | ProPhoto RGB to XYZ (D50)
proPhotoToXYZ :: Matrix3x3
proPhotoToXYZ = mkMatrix
  (0.7976749, 0.1351917, 0.0313534)
  (0.2880402, 0.7118741, 0.0000857)
  (0.0, 0.0, 0.8252100)

-- | XYZ to ProPhoto RGB (D50)
xyzToProPhoto :: Matrix3x3
xyzToProPhoto = mkMatrix
  (1.3459433, -0.2556075, -0.0511118)
  (-0.5445989, 1.5081673, 0.0205351)
  (0.0, 0.0, 1.2118128)

-- | ACEScg to XYZ
acesCGToXYZ :: Matrix3x3
acesCGToXYZ = mkMatrix
  (0.6624542, 0.1340042, 0.1561877)
  (0.2722287, 0.6740818, 0.0536895)
  (-0.0055746, 0.0040607, 1.0103391)

-- | XYZ to ACEScg
xyzToACEScg :: Matrix3x3
xyzToACEScg = mkMatrix
  (1.6410234, -0.3248033, -0.2364247)
  (-0.6636629, 1.6153316, 0.0167563)
  (0.0117219, -0.0082844, 0.9883948)

-- ────────────────────────────────────────────────────────────────────────────
-- Color Space Accessors
-- ────────────────────────────────────────────────────────────────────────────

-- | Get gamma type for color space
getGamma :: ColorSpaceId -> GammaType
getGamma cs = case cs of
  SRGB_CS -> SRGB
  LinearSRGB -> Linear
  WideGamutRGB -> Power 2.2
  DisplayP3 -> SRGB
  ProPhotoRGB -> Power 1.8
  ACEScg -> Linear
  Rec709 -> Power 2.4
  Rec2020 -> Power 2.4

-- | Get RGB to XYZ matrix for color space
getToXYZMatrix :: ColorSpaceId -> Matrix3x3
getToXYZMatrix cs = case cs of
  SRGB_CS -> srgbToXYZ
  LinearSRGB -> srgbToXYZ
  WideGamutRGB -> wideGamutRGBToXYZ
  DisplayP3 -> p3ToXYZ
  ProPhotoRGB -> proPhotoToXYZ
  ACEScg -> acesCGToXYZ
  Rec709 -> srgbToXYZ
  Rec2020 -> srgbToXYZ

-- | Get XYZ to RGB matrix for color space
getFromXYZMatrix :: ColorSpaceId -> Matrix3x3
getFromXYZMatrix cs = case cs of
  SRGB_CS -> xyzToSRGB
  LinearSRGB -> xyzToSRGB
  WideGamutRGB -> xyzToWideGamutRGB
  DisplayP3 -> xyzToP3
  ProPhotoRGB -> xyzToProPhoto
  ACEScg -> xyzToACEScg
  Rec709 -> xyzToSRGB
  Rec2020 -> xyzToSRGB

-- ────────────────────────────────────────────────────────────────────────────
-- Conversion Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert RGB to XYZ
rgbToXYZ :: RGB -> ColorSpaceId -> XYZ
rgbToXYZ rgb colorSpace =
  let gamma = getGamma colorSpace
      linear = linearizeRGB rgb gamma
      matrix = getToXYZMatrix colorSpace
  in matrixMultiplyRGB matrix linear

-- | Convert XYZ to RGB
xyzToRGB :: XYZ -> ColorSpaceId -> RGB
xyzToRGB xyz colorSpace =
  let matrix = getFromXYZMatrix colorSpace
      linear = matrixMultiplyXYZ matrix xyz
      gamma = getGamma colorSpace
  in applyGammaRGB linear gamma

-- | Convert RGB from one color space to another
convertColorSpace :: RGB -> ColorSpaceId -> ColorSpaceId -> RGB
convertColorSpace rgb from to
  | from == to = rgb
  | otherwise = case (from, to) of
      (LinearSRGB, SRGB_CS) -> applyGammaRGB rgb SRGB
      (SRGB_CS, LinearSRGB) -> linearizeRGB rgb SRGB
      _ -> let xyz = rgbToXYZ rgb from
           in xyzToRGB xyz to

-- ────────────────────────────────────────────────────────────────────────────
-- Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Get luminance (Y component) from RGB
getLuminance :: RGB -> ColorSpaceId -> Double
getLuminance rgb colorSpace = xyzY (rgbToXYZ rgb colorSpace)

-- | Check if color is within gamut (all components 0-1)
isInGamut :: RGB -> Bool
isInGamut (RGB r g b) =
  r >= 0 && r <= 1 && g >= 0 && g <= 1 && b >= 0 && b <= 1

-- | Clip color to gamut by clamping
clipToGamut :: RGB -> RGB
clipToGamut = clampRGB

-- | Create RGB from hex color code (RRGGBB or RGB)
fromHex :: String -> Maybe RGB
fromHex s =
  let hex = if head s == '#' then tail s else s
  in case length hex of
       6 -> parseHex6 hex
       3 -> parseHex3 hex
       _ -> Nothing
  where
    parseHex6 h =
      let (r, rest1) = splitAt 2 h
          (g, b) = splitAt 2 rest1
      in do rv <- parseHexPair r
            gv <- parseHexPair g
            bv <- parseHexPair b
            return $ RGB (fromIntegral rv / 255) (fromIntegral gv / 255) (fromIntegral bv / 255)

    parseHex3 h =
      let [r, g, b] = h
      in do rv <- parseHexDigit r
            gv <- parseHexDigit g
            bv <- parseHexDigit b
            return $ RGB (fromIntegral (rv * 17) / 255)
                         (fromIntegral (gv * 17) / 255)
                         (fromIntegral (bv * 17) / 255)

    parseHexPair [h, l]
      | isHexDigit h && isHexDigit l = Just (digitToInt h * 16 + digitToInt l)
    parseHexPair _ = Nothing

    parseHexDigit c
      | isHexDigit c = Just (digitToInt c)
      | otherwise = Nothing
