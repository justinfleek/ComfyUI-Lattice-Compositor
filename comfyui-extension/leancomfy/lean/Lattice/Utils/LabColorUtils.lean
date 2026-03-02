/-
  Lattice.Utils.LabColorUtils - LAB Color Space Utilities

  Provides CIE LAB, XYZ, and YUV color space conversions
  for professional color correction and analysis.

  Uses D65 illuminant (standard for sRGB)
  LAB L* range: 0-100, a* and b* range: -128 to +127

  Source: ui/src/utils/labColorUtils.ts
-/

namespace Lattice.Utils.LabColorUtils

/-! ## Constants -/

/-- D65 white point X reference value -/
def D65_X : Float := 95.047

/-- D65 white point Y reference value -/
def D65_Y : Float := 100.0

/-- D65 white point Z reference value -/
def D65_Z : Float := 108.883

/-- BT.709 luminance coefficient for red -/
def BT709_R : Float := 0.2126

/-- BT.709 luminance coefficient for green -/
def BT709_G : Float := 0.7152

/-- BT.709 luminance coefficient for blue -/
def BT709_B : Float := 0.0722

/-! ## Color Types -/

/-- LAB color type -/
structure LAB where
  L : Float -- 0-100 (lightness)
  a : Float -- -128 to +127 (green to red)
  b : Float -- -128 to +127 (blue to yellow)
  deriving Repr, BEq

/-- XYZ color type -/
structure XYZ where
  X : Float
  Y : Float
  Z : Float
  deriving Repr, BEq

/-- YUV color type (for vectorscope) -/
structure YUV where
  Y : Float -- Luminance (0-1)
  U : Float -- Blue-Yellow chrominance (-0.5 to +0.5)
  V : Float -- Red-Cyan chrominance (-0.5 to +0.5)
  deriving Repr, BEq

/-- HSL color type -/
structure HSL where
  h : Float -- 0-360 (hue)
  s : Float -- 0-1 (saturation)
  l : Float -- 0-1 (lightness)
  deriving Repr, BEq

/-- RGB color type (0-255) -/
structure RGB where
  r : UInt8
  g : UInt8
  b : UInt8
  deriving Repr, BEq

/-! ## sRGB <-> Linear RGB Conversion -/

/-- Convert sRGB component (0-255) to linear RGB (0-1) -/
def sRGBToLinear (value : Float) : Float :=
  let v := value / 255.0
  if v <= 0.04045 then v / 12.92
  else Float.pow ((v + 0.055) / 1.055) 2.4

/-- Convert linear RGB (0-1) to sRGB component (0-255) -/
def linearToSRGB (value : Float) : UInt8 :=
  let v := if value <= 0.0031308
           then value * 12.92
           else 1.055 * Float.pow value (1.0 / 2.4) - 0.055
  let clamped := Float.max 0.0 (Float.min 255.0 (v * 255.0))
  clamped.toUInt8

/-! ## RGB <-> XYZ Conversion -/

/-- sRGB to XYZ conversion matrix (D65) row 0 -/
def SRGB_TO_XYZ_R : Float × Float × Float := (0.4124564, 0.3575761, 0.1804375)
def SRGB_TO_XYZ_G : Float × Float × Float := (0.2126729, 0.7151522, 0.072175)
def SRGB_TO_XYZ_B : Float × Float × Float := (0.0193339, 0.119192, 0.9503041)

/-- XYZ to sRGB conversion matrix (D65) -/
def XYZ_TO_SRGB_R : Float × Float × Float := (3.2404542, -1.5371385, -0.4985314)
def XYZ_TO_SRGB_G : Float × Float × Float := (-0.969266, 1.8760108, 0.041556)
def XYZ_TO_SRGB_B : Float × Float × Float := (0.0556434, -0.2040259, 1.0572252)

/-- Convert RGB (0-255) to XYZ color space -/
def rgbToXyz (r g b : Float) : XYZ :=
  let rLinear := sRGBToLinear r
  let gLinear := sRGBToLinear g
  let bLinear := sRGBToLinear b
  let (r0, r1, r2) := SRGB_TO_XYZ_R
  let (g0, g1, g2) := SRGB_TO_XYZ_G
  let (b0, b1, b2) := SRGB_TO_XYZ_B
  { X := (rLinear * r0 + gLinear * r1 + bLinear * r2) * 100.0
  , Y := (rLinear * g0 + gLinear * g1 + bLinear * g2) * 100.0
  , Z := (rLinear * b0 + gLinear * b1 + bLinear * b2) * 100.0 }

/-- Convert XYZ to RGB (0-255) -/
def xyzToRgb (X Y Z : Float) : RGB :=
  let x := X / 100.0
  let y := Y / 100.0
  let z := Z / 100.0
  let (r0, r1, r2) := XYZ_TO_SRGB_R
  let (g0, g1, g2) := XYZ_TO_SRGB_G
  let (b0, b1, b2) := XYZ_TO_SRGB_B
  let rLinear := x * r0 + y * r1 + z * r2
  let gLinear := x * g0 + y * g1 + z * g2
  let bLinear := x * b0 + y * b1 + z * b2
  { r := linearToSRGB rLinear
  , g := linearToSRGB gLinear
  , b := linearToSRGB bLinear }

/-! ## XYZ <-> LAB Conversion -/

/-- Lab f(t) function for XYZ to LAB conversion -/
def labF (t : Float) : Float :=
  let delta := 6.0 / 29.0
  let delta3 := delta * delta * delta
  if t > delta3 then Float.pow t (1.0 / 3.0)
  else t / (3.0 * delta * delta) + 4.0 / 29.0

/-- Inverse Lab f(t) function for LAB to XYZ conversion -/
def labFInverse (t : Float) : Float :=
  let delta := 6.0 / 29.0
  if t > delta then t * t * t
  else 3.0 * delta * delta * (t - 4.0 / 29.0)

/-- Convert XYZ to CIE LAB -/
def xyzToLab (X Y Z : Float) : LAB :=
  let xn := X / D65_X
  let yn := Y / D65_Y
  let zn := Z / D65_Z
  let fx := labF xn
  let fy := labF yn
  let fz := labF zn
  { L := 116.0 * fy - 16.0
  , a := 500.0 * (fx - fy)
  , b := 200.0 * (fy - fz) }

/-- Convert CIE LAB to XYZ -/
def labToXyz (L a b : Float) : XYZ :=
  let fy := (L + 16.0) / 116.0
  let fx := a / 500.0 + fy
  let fz := fy - b / 200.0
  { X := D65_X * labFInverse fx
  , Y := D65_Y * labFInverse fy
  , Z := D65_Z * labFInverse fz }

/-! ## RGB <-> LAB Direct Conversion -/

/-- Convert RGB (0-255) directly to CIE LAB -/
def rgbToLab (r g b : Float) : LAB :=
  let xyz := rgbToXyz r g b
  xyzToLab xyz.X xyz.Y xyz.Z

/-- Convert CIE LAB directly to RGB (0-255) -/
def labToRgb (L a b : Float) : RGB :=
  let xyz := labToXyz L a b
  xyzToRgb xyz.X xyz.Y xyz.Z

/-! ## Color Difference (Delta E) -/

/-- Calculate Delta E (CIE76) - basic Euclidean distance in LAB space -/
def deltaE76 (lab1 lab2 : LAB) : Float :=
  let dL := lab1.L - lab2.L
  let da := lab1.a - lab2.a
  let db := lab1.b - lab2.b
  Float.sqrt (dL * dL + da * da + db * db)

/-- Calculate Delta E (CIE94) - weighted formula for graphics applications -/
def deltaE94 (lab1 lab2 : LAB) : Float :=
  let kL := 1.0
  let kC := 1.0
  let kH := 1.0
  let K1 := 0.045
  let K2 := 0.015
  let dL := lab1.L - lab2.L
  let C1 := Float.sqrt (lab1.a * lab1.a + lab1.b * lab1.b)
  let C2 := Float.sqrt (lab2.a * lab2.a + lab2.b * lab2.b)
  let dC := C1 - C2
  let da := lab1.a - lab2.a
  let db := lab1.b - lab2.b
  let dH2 := da * da + db * db - dC * dC
  let dH := if dH2 > 0.0 then Float.sqrt dH2 else 0.0
  let SL := 1.0
  let SC := 1.0 + K1 * C1
  let SH := 1.0 + K2 * C1
  let term1 := dL / (kL * SL)
  let term2 := dC / (kC * SC)
  let term3 := dH / (kH * SH)
  Float.sqrt (term1 * term1 + term2 * term2 + term3 * term3)

/-! ## RGB <-> YUV Conversion -/

/-- Convert RGB (0-255) to YUV (BT.709) -/
def rgbToYuv (r g b : Float) : YUV :=
  let rn := r / 255.0
  let gn := g / 255.0
  let bn := b / 255.0
  let Y := BT709_R * rn + BT709_G * gn + BT709_B * bn
  let U := (0.5 * (bn - Y)) / (1.0 - BT709_B)
  let V := (0.5 * (rn - Y)) / (1.0 - BT709_R)
  { Y, U, V }

/-- Convert YUV to RGB (0-255) -/
def yuvToRgb (Y U V : Float) : RGB :=
  let r := Y + 2.0 * V * (1.0 - BT709_R)
  let g := Y - (2.0 * U * BT709_B * (1.0 - BT709_B)) / BT709_G -
               (2.0 * V * BT709_R * (1.0 - BT709_R)) / BT709_G
  let b := Y + 2.0 * U * (1.0 - BT709_B)
  let clamp v := Float.max 0.0 (Float.min 255.0 (v * 255.0))
  { r := (clamp r).toUInt8
  , g := (clamp g).toUInt8
  , b := (clamp b).toUInt8 }

/-! ## RGB <-> HSL Conversion -/

/-- Convert RGB (0-255) to HSL -/
def rgbToHsl (r g b : Float) : HSL :=
  let rn := r / 255.0
  let gn := g / 255.0
  let bn := b / 255.0
  let max := Float.max rn (Float.max gn bn)
  let min := Float.min rn (Float.min gn bn)
  let l := (max + min) / 2.0
  if max == min then { h := 0.0, s := 0.0, l }
  else
    let d := max - min
    let s := if l > 0.5 then d / (2.0 - max - min) else d / (max + min)
    let h := if max == rn then ((gn - bn) / d + (if gn < bn then 6.0 else 0.0)) / 6.0
             else if max == gn then ((bn - rn) / d + 2.0) / 6.0
             else ((rn - gn) / d + 4.0) / 6.0
    { h := h * 360.0, s, l }

/-- Helper for HSL to RGB conversion -/
def hue2rgb (p q t : Float) : Float :=
  let t' := if t < 0.0 then t + 1.0 else if t > 1.0 then t - 1.0 else t
  if t' < 1.0 / 6.0 then p + (q - p) * 6.0 * t'
  else if t' < 0.5 then q
  else if t' < 2.0 / 3.0 then p + (q - p) * (2.0 / 3.0 - t') * 6.0
  else p

/-- Convert HSL to RGB (0-255) -/
def hslToRgb (h s l : Float) : RGB :=
  let h' := (((h % 360.0) + 360.0) % 360.0) / 360.0
  if s == 0.0 then
    let v := (l * 255.0).toUInt8
    { r := v, g := v, b := v }
  else
    let q := if l < 0.5 then l * (1.0 + s) else l + s - l * s
    let p := 2.0 * l - q
    { r := (hue2rgb p q (h' + 1.0 / 3.0) * 255.0).toUInt8
    , g := (hue2rgb p q h' * 255.0).toUInt8
    , b := (hue2rgb p q (h' - 1.0 / 3.0) * 255.0).toUInt8 }

/-! ## Utility Functions -/

/-- Calculate luminance (BT.709) from RGB (0-255) -/
def rgbToLuminance (r g b : Float) : Float :=
  BT709_R * r + BT709_G * g + BT709_B * b

/-- Check if a color is within a tolerance of neutral gray -/
def isNeutral (r g b : Float) (tolerance : Float := 5.0) : Bool :=
  let lab := rgbToLab r g b
  Float.abs lab.a < tolerance && Float.abs lab.b < tolerance

/-- Get the complementary color -/
def complementary (r g b : Float) : RGB :=
  let hsl := rgbToHsl r g b
  hslToRgb ((hsl.h + 180.0) % 360.0) hsl.s hsl.l

/-- Clamp a value between min and max -/
def clamp (value min max : Float) : Float :=
  Float.max min (Float.min max value)

/-- Linear interpolation between two values -/
def lerp (a b t : Float) : Float :=
  a + (b - a) * t

/-- Smoothstep function for smooth transitions -/
def smoothstep (edge0 edge1 x : Float) : Float :=
  let t := clamp ((x - edge0) / (edge1 - edge0)) 0.0 1.0
  t * t * (3.0 - 2.0 * t)

end Lattice.Utils.LabColorUtils
