/-
  Lattice.Services.ColorSpace.Conversions - Color Space Conversions

  Pure color space conversion algorithms:
  - RGB ↔ XYZ via matrix transformation
  - Color space primaries and white points
  - Conversion between any two color spaces

  Source: ui/src/services/colorManagement/ColorProfileService.ts
-/

import Lattice.Services.ColorSpace.TransferFunctions

namespace Lattice.Services.ColorSpace.Conversions

open Lattice.Services.ColorSpace.TransferFunctions

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- XYZ tristimulus values -/
structure XYZ where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited, BEq

/-- 3x3 color matrix -/
structure Matrix3x3 where
  m00 : Float; m01 : Float; m02 : Float
  m10 : Float; m11 : Float; m12 : Float
  m20 : Float; m21 : Float; m22 : Float
  deriving Repr, Inhabited

/-- Color space identifier -/
inductive ColorSpaceId where
  | sRGB
  | linearSRGB
  | wideGamutRGB
  | displayP3
  | proPhotoRGB
  | acesCG
  | rec709
  | rec2020
  deriving Repr, DecidableEq, Inhabited

/-- Color space definition -/
structure ColorSpaceDef where
  id : ColorSpaceId
  name : String
  gamma : GammaType
  toXYZ : Matrix3x3
  fromXYZ : Matrix3x3
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Matrix Operations
--------------------------------------------------------------------------------

/-- Create matrix from row values -/
def mkMatrix (r0 : Float × Float × Float) (r1 : Float × Float × Float)
    (r2 : Float × Float × Float) : Matrix3x3 :=
  { m00 := r0.1, m01 := r0.2.1, m02 := r0.2.2
  , m10 := r1.1, m11 := r1.2.1, m12 := r1.2.2
  , m20 := r2.1, m21 := r2.2.1, m22 := r2.2.2 }

/-- Multiply matrix by RGB vector, producing XYZ -/
def matrixMultiplyRGB (m : Matrix3x3) (rgb : RGB) : XYZ :=
  { x := m.m00 * rgb.r + m.m01 * rgb.g + m.m02 * rgb.b
  , y := m.m10 * rgb.r + m.m11 * rgb.g + m.m12 * rgb.b
  , z := m.m20 * rgb.r + m.m21 * rgb.g + m.m22 * rgb.b }

/-- Multiply matrix by XYZ vector, producing RGB -/
def matrixMultiplyXYZ (m : Matrix3x3) (xyz : XYZ) : RGB :=
  { r := m.m00 * xyz.x + m.m01 * xyz.y + m.m02 * xyz.z
  , g := m.m10 * xyz.x + m.m11 * xyz.y + m.m12 * xyz.z
  , b := m.m20 * xyz.x + m.m21 * xyz.y + m.m22 * xyz.z }

--------------------------------------------------------------------------------
-- Color Space Matrices (D65 white point unless noted)
--------------------------------------------------------------------------------

/-- sRGB to XYZ (D65) -/
def srgbToXYZ : Matrix3x3 := mkMatrix
  (0.4124564, 0.3575761, 0.1804375)
  (0.2126729, 0.7151522, 0.072175)
  (0.0193339, 0.119192, 0.9503041)

/-- XYZ to sRGB (D65) -/
def xyzToSRGB : Matrix3x3 := mkMatrix
  (3.2404542, -1.5371385, -0.4985314)
  (-0.969266, 1.8760108, 0.041556)
  (0.0556434, -0.2040259, 1.0572252)

/-- Display P3 to XYZ (D65) -/
def p3ToXYZ : Matrix3x3 := mkMatrix
  (0.4865709, 0.2656677, 0.1982173)
  (0.2289746, 0.6917385, 0.0792869)
  (0.0, 0.0451134, 1.0439444)

/-- XYZ to Display P3 (D65) -/
def xyzToP3 : Matrix3x3 := mkMatrix
  (2.4934969, -0.9313836, -0.4027108)
  (-0.829489, 1.7626641, 0.0236247)
  (0.0358458, -0.0761724, 0.9568845)

/-- Wide-Gamut RGB to XYZ (D65) -/
def wideGamutRGBToXYZ : Matrix3x3 := mkMatrix
  (0.5767309, 0.185554, 0.1881852)
  (0.2973769, 0.6273491, 0.0752741)
  (0.0270343, 0.0706872, 0.9911085)

/-- XYZ to Wide-Gamut RGB (D65) -/
def xyzToWideGamutRGB : Matrix3x3 := mkMatrix
  (2.041369, -0.5649464, -0.3446944)
  (-0.969266, 1.8760108, 0.041556)
  (0.0134474, -0.1183897, 1.0154096)

/-- ProPhoto RGB to XYZ (D50) -/
def proPhotoToXYZ : Matrix3x3 := mkMatrix
  (0.7976749, 0.1351917, 0.0313534)
  (0.2880402, 0.7118741, 0.0000857)
  (0.0, 0.0, 0.8252100)

/-- XYZ to ProPhoto RGB (D50) -/
def xyzToProPhoto : Matrix3x3 := mkMatrix
  (1.3459433, -0.2556075, -0.0511118)
  (-0.5445989, 1.5081673, 0.0205351)
  (0.0, 0.0, 1.2118128)

/-- ACEScg to XYZ (ACES white point) -/
def acesCGToXYZ : Matrix3x3 := mkMatrix
  (0.6624542, 0.1340042, 0.1561877)
  (0.2722287, 0.6740818, 0.0536895)
  (-0.0055746, 0.0040607, 1.0103391)

/-- XYZ to ACEScg (ACES white point) -/
def xyzToACEScg : Matrix3x3 := mkMatrix
  (1.6410234, -0.3248033, -0.2364247)
  (-0.6636629, 1.6153316, 0.0167563)
  (0.0117219, -0.0082844, 0.9883948)

--------------------------------------------------------------------------------
-- Color Space Definitions
--------------------------------------------------------------------------------

/-- Get gamma type for color space -/
def getGamma (cs : ColorSpaceId) : GammaType :=
  match cs with
  | .sRGB => .sRGB
  | .linearSRGB => .linear
  | .wideGamutRGB => .power 2.2
  | .displayP3 => .sRGB  -- Uses sRGB transfer function
  | .proPhotoRGB => .power 1.8
  | .acesCG => .linear
  | .rec709 => .power 2.4
  | .rec2020 => .power 2.4

/-- Get RGB to XYZ matrix for color space -/
def getToXYZMatrix (cs : ColorSpaceId) : Matrix3x3 :=
  match cs with
  | .sRGB | .linearSRGB | .rec709 => srgbToXYZ
  | .wideGamutRGB => wideGamutRGBToXYZ
  | .displayP3 => p3ToXYZ
  | .proPhotoRGB => proPhotoToXYZ
  | .acesCG => acesCGToXYZ
  | .rec2020 => srgbToXYZ  -- Rec.2020 uses similar primaries

/-- Get XYZ to RGB matrix for color space -/
def getFromXYZMatrix (cs : ColorSpaceId) : Matrix3x3 :=
  match cs with
  | .sRGB | .linearSRGB | .rec709 => xyzToSRGB
  | .wideGamutRGB => xyzToWideGamutRGB
  | .displayP3 => xyzToP3
  | .proPhotoRGB => xyzToProPhoto
  | .acesCG => xyzToACEScg
  | .rec2020 => xyzToSRGB

--------------------------------------------------------------------------------
-- Conversion Functions
--------------------------------------------------------------------------------

/-- Convert RGB to XYZ -/
def rgbToXYZ (rgb : RGB) (colorSpace : ColorSpaceId) : XYZ :=
  let gamma := getGamma colorSpace
  let linear := linearizeRGB rgb gamma
  let matrix := getToXYZMatrix colorSpace
  matrixMultiplyRGB matrix linear

/-- Convert XYZ to RGB -/
def xyzToRGB (xyz : XYZ) (colorSpace : ColorSpaceId) : RGB :=
  let matrix := getFromXYZMatrix colorSpace
  let linear := matrixMultiplyXYZ matrix xyz
  let gamma := getGamma colorSpace
  applyGammaRGB linear gamma

/-- Convert RGB from one color space to another -/
def convertColorSpace (rgb : RGB) (from to : ColorSpaceId) : RGB :=
  if from == to then rgb
  else
    -- Special case: linear sRGB conversions
    match (from, to) with
    | (.linearSRGB, .sRGB) => applyGammaRGB rgb .sRGB
    | (.sRGB, .linearSRGB) => linearizeRGB rgb .sRGB
    | _ =>
      -- General conversion via XYZ
      let xyz := rgbToXYZ rgb from
      xyzToRGB xyz to

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

/-- Get luminance (Y component) from RGB -/
def getLuminance (rgb : RGB) (colorSpace : ColorSpaceId := .sRGB) : Float :=
  let xyz := rgbToXYZ rgb colorSpace
  xyz.y

/-- Check if color is within gamut (all components 0-1) -/
def isInGamut (rgb : RGB) : Bool :=
  rgb.r >= 0.0 && rgb.r <= 1.0 &&
  rgb.g >= 0.0 && rgb.g <= 1.0 &&
  rgb.b >= 0.0 && rgb.b <= 1.0

/-- Clip color to gamut by clamping -/
def clipToGamut (rgb : RGB) : RGB :=
  clampRGB rgb

/-- Create RGB from hex color code (RRGGBB or RGB) -/
def fromHex (hex : String) : Option RGB :=
  let s := if hex.startsWith "#" then hex.drop 1 else hex
  if s.length == 6 then
    match (s.take 2, s.drop 2 |>.take 2, s.drop 4) with
    | (r, g, b) =>
      match (r.toNat? (radix := 16), g.toNat? (radix := 16), b.toNat? (radix := 16)) with
      | (some rv, some gv, some bv) =>
        some { r := rv.toFloat / 255.0
             , g := gv.toFloat / 255.0
             , b := bv.toFloat / 255.0 }
      | _ => none
  else if s.length == 3 then
    match (s.take 1, s.drop 1 |>.take 1, s.drop 2) with
    | (r, g, b) =>
      match (r.toNat? (radix := 16), g.toNat? (radix := 16), b.toNat? (radix := 16)) with
      | (some rv, some gv, some bv) =>
        some { r := (rv * 17).toFloat / 255.0
             , g := (gv * 17).toFloat / 255.0
             , b := (bv * 17).toFloat / 255.0 }
      | _ => none
  else
    none

end Lattice.Services.ColorSpace.Conversions
