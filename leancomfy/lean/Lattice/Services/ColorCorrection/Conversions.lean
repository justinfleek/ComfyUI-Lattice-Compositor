/-
  Lattice.Services.ColorCorrection.Conversions - Color Space Conversion Functions

  Pure mathematical functions for color space transformations:
  - RGB to HSL
  - HSL to RGB
  - Luminance calculation

  All functions are total (no partial def) and deterministic.

  Source: ui/src/services/effects/colorRenderer.ts (lines 131-188, 436)
-/

namespace Lattice.Services.ColorCorrection.Conversions

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- RGB color with values in 0-255 range -/
structure RGB where
  r : Float
  g : Float
  b : Float
  deriving Repr, Inhabited

/-- HSL color with H in 0-1, S in 0-1, L in 0-1 -/
structure HSL where
  h : Float  -- Hue, 0-1 (where 1 = 360°)
  s : Float  -- Saturation, 0-1
  l : Float  -- Lightness, 0-1
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Luminance Calculation
--------------------------------------------------------------------------------

/-- Calculate perceived luminance using Rec. 601 coefficients.

    Formula: L = 0.299*R + 0.587*G + 0.114*B

    @param r Red value (0-255)
    @param g Green value (0-255)
    @param b Blue value (0-255)
    @return Luminance in 0-255 range -/
def luminance (r g b : Float) : Float :=
  r * 0.299 + g * 0.587 + b * 0.114

/-- Calculate normalized luminance (0-1 range).

    @param r Red value (0-255)
    @param g Green value (0-255)
    @param b Blue value (0-255)
    @return Luminance in 0-1 range -/
def luminanceNormalized (r g b : Float) : Float :=
  (r * 0.299 + g * 0.587 + b * 0.114) / 255.0

--------------------------------------------------------------------------------
-- RGB to HSL Conversion
--------------------------------------------------------------------------------

/-- Convert RGB (0-255) to HSL (0-1).

    Algorithm:
    1. Normalize RGB to 0-1
    2. Find max and min components
    3. L = (max + min) / 2
    4. If max ≠ min:
       - S = d / (2 - max - min) if L > 0.5, else d / (max + min)
       - H based on which component is max

    @param r Red value (0-255)
    @param g Green value (0-255)
    @param b Blue value (0-255)
    @return HSL values (h, s, l) each in 0-1 range -/
def rgbToHsl (r g b : Float) : HSL :=
  let rNorm := r / 255.0
  let gNorm := g / 255.0
  let bNorm := b / 255.0

  let maxC := Float.max rNorm (Float.max gNorm bNorm)
  let minC := Float.min rNorm (Float.min gNorm bNorm)
  let l := (maxC + minC) / 2.0

  if maxC == minC then
    -- Achromatic (gray)
    { h := 0.0, s := 0.0, l := l }
  else
    let d := maxC - minC
    let s := if l > 0.5 then d / (2.0 - maxC - minC) else d / (maxC + minC)

    -- Calculate hue based on which channel is max
    let h :=
      if maxC == rNorm then
        let rawH := (gNorm - bNorm) / d
        let adjustedH := if gNorm < bNorm then rawH + 6.0 else rawH
        adjustedH / 6.0
      else if maxC == gNorm then
        ((bNorm - rNorm) / d + 2.0) / 6.0
      else
        ((rNorm - gNorm) / d + 4.0) / 6.0

    { h := h, s := s, l := l }

--------------------------------------------------------------------------------
-- HSL to RGB Conversion
--------------------------------------------------------------------------------

/-- Helper function for HSL to RGB conversion.

    Converts a hue value to RGB component based on p, q parameters.

    @param p Lower bound
    @param q Upper bound
    @param t Hue offset (will be wrapped to 0-1)
    @return RGB component value (0-1) -/
def hue2rgb (p q t : Float) : Float :=
  -- Wrap t to 0-1 range
  let t' := if t < 0.0 then t + 1.0 else if t > 1.0 then t - 1.0 else t

  if t' < 1.0 / 6.0 then
    p + (q - p) * 6.0 * t'
  else if t' < 0.5 then
    q
  else if t' < 2.0 / 3.0 then
    p + (q - p) * (2.0 / 3.0 - t') * 6.0
  else
    p

/-- Convert HSL (0-1) to RGB (0-255).

    Algorithm:
    1. If S = 0: R = G = B = L (achromatic)
    2. Otherwise:
       - q = L * (1 + S) if L < 0.5, else L + S - L * S
       - p = 2 * L - q
       - R = hue2rgb(p, q, H + 1/3)
       - G = hue2rgb(p, q, H)
       - B = hue2rgb(p, q, H - 1/3)

    @param h Hue (0-1)
    @param s Saturation (0-1)
    @param l Lightness (0-1)
    @return RGB values in 0-255 range -/
def hslToRgb (hsl : HSL) : RGB :=
  if hsl.s == 0.0 then
    -- Achromatic
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

/-- Convert RGB tuple to HSL tuple.

    @param r Red (0-255)
    @param g Green (0-255)
    @param b Blue (0-255)
    @return (h, s, l) each in 0-1 range -/
def rgbToHslTuple (r g b : Float) : Float × Float × Float :=
  let hsl := rgbToHsl r g b
  (hsl.h, hsl.s, hsl.l)

/-- Convert HSL tuple to RGB tuple.

    @param h Hue (0-1)
    @param s Saturation (0-1)
    @param l Lightness (0-1)
    @return (r, g, b) each in 0-255 range -/
def hslToRgbTuple (h s l : Float) : Float × Float × Float :=
  let rgb := hslToRgb { h := h, s := s, l := l }
  (rgb.r, rgb.g, rgb.b)

end Lattice.Services.ColorCorrection.Conversions
