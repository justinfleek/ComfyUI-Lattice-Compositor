/-
  Lattice.Services.BlendModes.ColorSpace - Color space conversions

  Pure math functions for RGB/HSL color space conversion.
  Used by blend mode operations.

  Source: ui/src/services/blendModes.ts (lines 77-148)
-/

namespace Lattice.Services.BlendModes.ColorSpace

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- RGB color with values in 0-255 range -/
structure RGB where
  r : Float
  g : Float
  b : Float
  deriving Repr, Inhabited

/-- HSL color with h in 0-1, s in 0-1, l in 0-1 -/
structure HSL where
  h : Float
  s : Float
  l : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

/-- Clamp value to 0-255 range -/
def clamp255 (value : Float) : Float :=
  Float.max 0.0 (Float.min 255.0 value)

/-- Round and clamp to 0-255 -/
def clampRound (value : Float) : Float :=
  clamp255 (Float.round value)

--------------------------------------------------------------------------------
-- Luminance
--------------------------------------------------------------------------------

/-- Get luminance of RGB color (0-255 scale)
    Uses ITU-R BT.601 coefficients -/
def getLuminance (r g b : Float) : Float :=
  0.299 * r + 0.587 * g + 0.114 * b

/-- Get normalized luminance (0-1 scale) -/
def getLuminanceNormalized (r g b : Float) : Float :=
  getLuminance r g b / 255.0

--------------------------------------------------------------------------------
-- RGB to HSL
--------------------------------------------------------------------------------

/-- Convert RGB (0-255) to HSL (0-1) -/
def rgbToHsl (r g b : Float) : HSL :=
  let rn := r / 255.0
  let gn := g / 255.0
  let bn := b / 255.0

  let maxVal := Float.max rn (Float.max gn bn)
  let minVal := Float.min rn (Float.min gn bn)
  let l := (maxVal + minVal) / 2.0

  if maxVal == minVal then
    -- Achromatic (gray)
    { h := 0.0, s := 0.0, l := l }
  else
    let d := maxVal - minVal
    let s := if l > 0.5
             then d / (2.0 - maxVal - minVal)
             else d / (maxVal + minVal)

    let h := if maxVal == rn then
               ((gn - bn) / d + (if gn < bn then 6.0 else 0.0)) / 6.0
             else if maxVal == gn then
               ((bn - rn) / d + 2.0) / 6.0
             else
               ((rn - gn) / d + 4.0) / 6.0

    { h := h, s := s, l := l }

--------------------------------------------------------------------------------
-- HSL to RGB
--------------------------------------------------------------------------------

/-- Helper for HSL to RGB conversion -/
private def hue2rgb (p q t : Float) : Float :=
  let t' := if t < 0.0 then t + 1.0
            else if t > 1.0 then t - 1.0
            else t
  if t' < 1.0 / 6.0 then
    p + (q - p) * 6.0 * t'
  else if t' < 1.0 / 2.0 then
    q
  else if t' < 2.0 / 3.0 then
    p + (q - p) * (2.0 / 3.0 - t') * 6.0
  else
    p

/-- Convert HSL (0-1) to RGB (0-255) -/
def hslToRgb (hsl : HSL) : RGB :=
  if hsl.s == 0.0 then
    -- Achromatic (gray)
    let v := Float.round (hsl.l * 255.0)
    { r := v, g := v, b := v }
  else
    let q := if hsl.l < 0.5
             then hsl.l * (1.0 + hsl.s)
             else hsl.l + hsl.s - hsl.l * hsl.s
    let p := 2.0 * hsl.l - q

    let r := hue2rgb p q (hsl.h + 1.0 / 3.0)
    let g := hue2rgb p q hsl.h
    let b := hue2rgb p q (hsl.h - 1.0 / 3.0)

    { r := Float.round (r * 255.0)
    , g := Float.round (g * 255.0)
    , b := Float.round (b * 255.0) }

--------------------------------------------------------------------------------
-- Convenience Functions
--------------------------------------------------------------------------------

/-- Create RGB from components -/
def rgb (r g b : Float) : RGB := { r, g, b }

/-- Create HSL from components -/
def hsl (h s l : Float) : HSL := { h, s, l }

/-- Get hue component from RGB (0-1) -/
def getHue (r g b : Float) : Float :=
  (rgbToHsl r g b).h

/-- Get saturation component from RGB (0-1) -/
def getSaturation (r g b : Float) : Float :=
  (rgbToHsl r g b).s

/-- Get lightness component from RGB (0-1) -/
def getLightness (r g b : Float) : Float :=
  (rgbToHsl r g b).l

end Lattice.Services.BlendModes.ColorSpace
