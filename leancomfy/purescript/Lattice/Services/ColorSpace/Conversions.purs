-- | Lattice.Services.ColorSpace.Conversions - Color Space Conversions
-- |
-- | Pure color space conversion algorithms:
-- | - RGB ↔ XYZ via matrix transformation
-- | - Color space primaries and white points
-- | - Conversion between any two color spaces
-- |
-- | Source: ui/src/services/colorManagement/ColorProfileService.ts

module Lattice.Services.ColorSpace.Conversions
  ( -- * Types
    XYZ, Matrix3x3, ColorSpaceId(..)
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

import Prelude
import Data.Int (fromStringAs, hexadecimal, toNumber)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), drop, length, split, take)
import Data.String.CodeUnits (charAt)

import Lattice.Services.ColorSpace.TransferFunctions (RGB, GammaType(..), linearizeRGB, applyGammaRGB, clampRGB)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | XYZ tristimulus values
type XYZ =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | 3x3 color matrix
type Matrix3x3 =
  { m00 :: Number, m01 :: Number, m02 :: Number
  , m10 :: Number, m11 :: Number, m12 :: Number
  , m20 :: Number, m21 :: Number, m22 :: Number
  }

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

derive instance eqColorSpaceId :: Eq ColorSpaceId

--------------------------------------------------------------------------------
-- Matrix Operations
--------------------------------------------------------------------------------

-- | Create matrix from row values
mkMatrix :: { r0 :: { a :: Number, b :: Number, c :: Number }
            , r1 :: { a :: Number, b :: Number, c :: Number }
            , r2 :: { a :: Number, b :: Number, c :: Number }
            } -> Matrix3x3
mkMatrix { r0, r1, r2 } =
  { m00: r0.a, m01: r0.b, m02: r0.c
  , m10: r1.a, m11: r1.b, m12: r1.c
  , m20: r2.a, m21: r2.b, m22: r2.c
  }

-- | Multiply matrix by RGB vector, producing XYZ
matrixMultiplyRGB :: Matrix3x3 -> RGB -> XYZ
matrixMultiplyRGB m rgb =
  { x: m.m00 * rgb.r + m.m01 * rgb.g + m.m02 * rgb.b
  , y: m.m10 * rgb.r + m.m11 * rgb.g + m.m12 * rgb.b
  , z: m.m20 * rgb.r + m.m21 * rgb.g + m.m22 * rgb.b
  }

-- | Multiply matrix by XYZ vector, producing RGB
matrixMultiplyXYZ :: Matrix3x3 -> XYZ -> RGB
matrixMultiplyXYZ m xyz =
  { r: m.m00 * xyz.x + m.m01 * xyz.y + m.m02 * xyz.z
  , g: m.m10 * xyz.x + m.m11 * xyz.y + m.m12 * xyz.z
  , b: m.m20 * xyz.x + m.m21 * xyz.y + m.m22 * xyz.z
  }

--------------------------------------------------------------------------------
-- Color Space Matrices
--------------------------------------------------------------------------------

-- | sRGB to XYZ (D65)
srgbToXYZ :: Matrix3x3
srgbToXYZ = mkMatrix
  { r0: { a: 0.4124564, b: 0.3575761, c: 0.1804375 }
  , r1: { a: 0.2126729, b: 0.7151522, c: 0.072175 }
  , r2: { a: 0.0193339, b: 0.119192, c: 0.9503041 }
  }

-- | XYZ to sRGB (D65)
xyzToSRGB :: Matrix3x3
xyzToSRGB = mkMatrix
  { r0: { a: 3.2404542, b: -1.5371385, c: -0.4985314 }
  , r1: { a: -0.969266, b: 1.8760108, c: 0.041556 }
  , r2: { a: 0.0556434, b: -0.2040259, c: 1.0572252 }
  }

-- | Display P3 to XYZ (D65)
p3ToXYZ :: Matrix3x3
p3ToXYZ = mkMatrix
  { r0: { a: 0.4865709, b: 0.2656677, c: 0.1982173 }
  , r1: { a: 0.2289746, b: 0.6917385, c: 0.0792869 }
  , r2: { a: 0.0, b: 0.0451134, c: 1.0439444 }
  }

-- | XYZ to Display P3 (D65)
xyzToP3 :: Matrix3x3
xyzToP3 = mkMatrix
  { r0: { a: 2.4934969, b: -0.9313836, c: -0.4027108 }
  , r1: { a: -0.829489, b: 1.7626641, c: 0.0236247 }
  , r2: { a: 0.0358458, b: -0.0761724, c: 0.9568845 }
  }

-- | Wide-Gamut RGB to XYZ (D65)
wideGamutRGBToXYZ :: Matrix3x3
wideGamutRGBToXYZ = mkMatrix
  { r0: { a: 0.5767309, b: 0.185554, c: 0.1881852 }
  , r1: { a: 0.2973769, b: 0.6273491, c: 0.0752741 }
  , r2: { a: 0.0270343, b: 0.0706872, c: 0.9911085 }
  }

-- | XYZ to Wide-Gamut RGB (D65)
xyzToWideGamutRGB :: Matrix3x3
xyzToWideGamutRGB = mkMatrix
  { r0: { a: 2.041369, b: -0.5649464, c: -0.3446944 }
  , r1: { a: -0.969266, b: 1.8760108, c: 0.041556 }
  , r2: { a: 0.0134474, b: -0.1183897, c: 1.0154096 }
  }

-- | ProPhoto RGB to XYZ (D50)
proPhotoToXYZ :: Matrix3x3
proPhotoToXYZ = mkMatrix
  { r0: { a: 0.7976749, b: 0.1351917, c: 0.0313534 }
  , r1: { a: 0.2880402, b: 0.7118741, c: 0.0000857 }
  , r2: { a: 0.0, b: 0.0, c: 0.8252100 }
  }

-- | XYZ to ProPhoto RGB (D50)
xyzToProPhoto :: Matrix3x3
xyzToProPhoto = mkMatrix
  { r0: { a: 1.3459433, b: -0.2556075, c: -0.0511118 }
  , r1: { a: -0.5445989, b: 1.5081673, c: 0.0205351 }
  , r2: { a: 0.0, b: 0.0, c: 1.2118128 }
  }

-- | ACEScg to XYZ
acesCGToXYZ :: Matrix3x3
acesCGToXYZ = mkMatrix
  { r0: { a: 0.6624542, b: 0.1340042, c: 0.1561877 }
  , r1: { a: 0.2722287, b: 0.6740818, c: 0.0536895 }
  , r2: { a: -0.0055746, b: 0.0040607, c: 1.0103391 }
  }

-- | XYZ to ACEScg
xyzToACEScg :: Matrix3x3
xyzToACEScg = mkMatrix
  { r0: { a: 1.6410234, b: -0.3248033, c: -0.2364247 }
  , r1: { a: -0.6636629, b: 1.6153316, c: 0.0167563 }
  , r2: { a: 0.0117219, b: -0.0082844, c: 0.9883948 }
  }

--------------------------------------------------------------------------------
-- Color Space Accessors
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Conversion Functions
--------------------------------------------------------------------------------

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
  | otherwise = case { from, to } of
      { from: LinearSRGB, to: SRGB_CS } -> applyGammaRGB rgb SRGB
      { from: SRGB_CS, to: LinearSRGB } -> linearizeRGB rgb SRGB
      _ -> let xyz = rgbToXYZ rgb from
           in xyzToRGB xyz to

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Get luminance (Y component) from RGB
getLuminance :: RGB -> ColorSpaceId -> Number
getLuminance rgb colorSpace = (rgbToXYZ rgb colorSpace).y

-- | Check if color is within gamut (all components 0-1)
isInGamut :: RGB -> Boolean
isInGamut rgb =
  rgb.r >= 0.0 && rgb.r <= 1.0 &&
  rgb.g >= 0.0 && rgb.g <= 1.0 &&
  rgb.b >= 0.0 && rgb.b <= 1.0

-- | Clip color to gamut by clamping
clipToGamut :: RGB -> RGB
clipToGamut = clampRGB

-- | Create RGB from hex color code (RRGGBB or RGB)
fromHex :: String -> Maybe RGB
fromHex s =
  let hex = if (charAt 0 s) == Just '#' then drop 1 s else s
  in case length hex of
       6 -> parseHex6 hex
       3 -> parseHex3 hex
       _ -> Nothing
  where
    parseHex6 h = do
      rv <- fromStringAs hexadecimal (take 2 h)
      gv <- fromStringAs hexadecimal (take 2 (drop 2 h))
      bv <- fromStringAs hexadecimal (drop 4 h)
      Just { r: toNumber rv / 255.0
           , g: toNumber gv / 255.0
           , b: toNumber bv / 255.0
           }

    parseHex3 h = do
      rv <- fromStringAs hexadecimal (take 1 h)
      gv <- fromStringAs hexadecimal (take 1 (drop 1 h))
      bv <- fromStringAs hexadecimal (drop 2 h)
      Just { r: toNumber (rv * 17) / 255.0
           , g: toNumber (gv * 17) / 255.0
           , b: toNumber (bv * 17) / 255.0
           }
