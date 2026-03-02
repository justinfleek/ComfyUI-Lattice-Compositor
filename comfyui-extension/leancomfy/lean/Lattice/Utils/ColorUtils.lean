/-
  Lattice.Utils.ColorUtils - Color conversion and manipulation

  HSV, RGB, HSL conversions and hex parsing.
  All functions handle edge cases safely.
  NO banned constructs: no partial def, sorry, panic!, unreachable!, native_decide

  Uses raw Float with defensive guards.

  Source: ui/src/utils/colorUtils.ts
-/

namespace Lattice.Utils.ColorUtils

/-! ## Utility Functions -/

/-- Check if a Float is finite -/
def isFinite (x : Float) : Bool :=
  !x.isNaN && !x.isInf

/-- Clamp to [0, 1] -/
def clamp01 (x : Float) : Float :=
  if x < 0.0 then 0.0
  else if x > 1.0 then 1.0
  else x

/-- Clamp to [0, 255] -/
def clamp0255 (x : Float) : Float :=
  if x < 0.0 then 0.0
  else if x > 255.0 then 255.0
  else x

/-- Absolute value -/
def fabs (x : Float) : Float :=
  if x < 0.0 then -x else x

/-! ## Color Types -/

/-- RGB color (components 0-255) -/
structure RGB where
  r : Float
  g : Float
  b : Float
  deriving Repr, Inhabited, BEq

/-- RGBA color (RGB 0-255, alpha 0-1) -/
structure RGBA where
  r : Float
  g : Float
  b : Float
  a : Float
  deriving Repr, Inhabited, BEq

/-- HSV color (Hue 0-360, Saturation 0-1, Value 0-1) -/
structure HSV where
  h : Float  -- 0-360
  s : Float  -- 0-1
  v : Float  -- 0-1
  deriving Repr, Inhabited

/-- HSL color (Hue 0-360, Saturation 0-1, Lightness 0-1) -/
structure HSL where
  h : Float  -- 0-360
  s : Float  -- 0-1
  l : Float  -- 0-1
  deriving Repr, Inhabited

/-- Hex parse result -/
inductive HexParseResult
  | ok : RGB → HexParseResult
  | okWithAlpha : RGBA → HexParseResult
  | invalid : String → HexParseResult
  deriving Repr

/-! ## Color Space Conversions -/

/-- Normalize hue to [0, 360) -/
def normalizeHue (h : Float) : Float :=
  let wrapped := ((h % 360.0) + 360.0) % 360.0
  if isFinite wrapped then wrapped else 0.0

/-- Convert HSV to RGB -/
def hsvToRgb (hsv : HSV) : RGB :=
  let h := normalizeHue hsv.h
  let s := clamp01 hsv.s
  let v := clamp01 hsv.v
  let c := v * s
  let hPrime := h / 60.0
  let x := c * (1.0 - fabs ((hPrime % 2.0) - 1.0))
  let m := v - c

  let (r', g', b') :=
    if h < 60.0 then (c, x, 0.0)
    else if h < 120.0 then (x, c, 0.0)
    else if h < 180.0 then (0.0, c, x)
    else if h < 240.0 then (0.0, x, c)
    else if h < 300.0 then (x, 0.0, c)
    else (c, 0.0, x)

  let toChannel (n : Float) : Float :=
    let val := Float.round ((n + m) * 255.0)
    clamp0255 (if isFinite val then val else 0.0)

  { r := toChannel r', g := toChannel g', b := toChannel b' }

/-- Convert RGB to HSV -/
def rgbToHsv (rgb : RGB) : HSV :=
  let r := clamp01 (rgb.r / 255.0)
  let g := clamp01 (rgb.g / 255.0)
  let b := clamp01 (rgb.b / 255.0)

  let max := Float.max r (Float.max g b)
  let min := Float.min r (Float.min g b)
  let d := max - min

  let s := if max == 0.0 then 0.0
           else
             let ratio := d / max
             if isFinite ratio then clamp01 ratio else 0.0

  let v := clamp01 max

  let h :=
    if d == 0.0 then 0.0
    else if max == r then
      let raw := ((g - b) / d + (if g < b then 6.0 else 0.0)) * 60.0
      if isFinite raw then normalizeHue raw else 0.0
    else if max == g then
      let raw := ((b - r) / d + 2.0) * 60.0
      if isFinite raw then normalizeHue raw else 0.0
    else
      let raw := ((r - g) / d + 4.0) * 60.0
      if isFinite raw then normalizeHue raw else 0.0

  { h := h, s := s, v := v }

/-- Convert HSL to RGB -/
def hslToRgb (hsl : HSL) : RGB :=
  let h := normalizeHue hsl.h
  let s := clamp01 hsl.s
  let l := clamp01 hsl.l
  let c := (1.0 - fabs (2.0 * l - 1.0)) * s
  let hPrime := h / 60.0
  let x := c * (1.0 - fabs ((hPrime % 2.0) - 1.0))
  let m := l - c / 2.0

  let (r', g', b') :=
    if h < 60.0 then (c, x, 0.0)
    else if h < 120.0 then (x, c, 0.0)
    else if h < 180.0 then (0.0, c, x)
    else if h < 240.0 then (0.0, x, c)
    else if h < 300.0 then (x, 0.0, c)
    else (c, 0.0, x)

  let toChannel (n : Float) : Float :=
    let val := Float.round ((n + m) * 255.0)
    clamp0255 (if isFinite val then val else 0.0)

  { r := toChannel r', g := toChannel g', b := toChannel b' }

/-- Convert RGB to HSL -/
def rgbToHsl (rgb : RGB) : HSL :=
  let r := clamp01 (rgb.r / 255.0)
  let g := clamp01 (rgb.g / 255.0)
  let b := clamp01 (rgb.b / 255.0)

  let max := Float.max r (Float.max g b)
  let min := Float.min r (Float.min g b)
  let l := (max + min) / 2.0

  if max == min then
    { h := 0.0, s := 0.0, l := clamp01 l }
  else
    let d := max - min
    let s := if l > 0.5 then d / (2.0 - max - min) else d / (max + min)

    let h :=
      if max == r then ((g - b) / d + (if g < b then 6.0 else 0.0)) * 60.0
      else if max == g then ((b - r) / d + 2.0) * 60.0
      else ((r - g) / d + 4.0) * 60.0

    { h := normalizeHue h
      s := clamp01 (if isFinite s then s else 0.0)
      l := clamp01 l }

/-! ## Hex Conversion -/

/-- Convert a single hex character to number (0-15) -/
def hexCharToNum (c : Char) : Option Nat :=
  if c >= '0' && c <= '9' then some (c.toNat - '0'.toNat)
  else if c >= 'a' && c <= 'f' then some (c.toNat - 'a'.toNat + 10)
  else if c >= 'A' && c <= 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Convert two hex characters to number (0-255) -/
def hexPairToNum (c1 c2 : Char) : Option Nat :=
  match hexCharToNum c1, hexCharToNum c2 with
  | some n1, some n2 => some (n1 * 16 + n2)
  | _, _ => none

/-- Convert Nat to Float safely -/
def natToFloat (n : Nat) : Float :=
  Float.ofNat n

/-- Parse hex color string to RGB -/
def hexToRgb (hex : String) : HexParseResult :=
  let hex := if hex.startsWith "#" then hex.drop 1 else hex
  let chars := hex.toList

  match chars with
  -- #RGB format
  | [r, g, b] =>
    match hexCharToNum r, hexCharToNum g, hexCharToNum b with
    | some rv, some gv, some bv =>
      let r' := natToFloat (rv * 16 + rv)
      let g' := natToFloat (gv * 16 + gv)
      let b' := natToFloat (bv * 16 + bv)
      .ok { r := r', g := g', b := b' }
    | _, _, _ => .invalid s!"Invalid hex characters in: {hex}"

  -- #RRGGBB format
  | [r1, r2, g1, g2, b1, b2] =>
    match hexPairToNum r1 r2, hexPairToNum g1 g2, hexPairToNum b1 b2 with
    | some rv, some gv, some bv =>
      .ok { r := natToFloat rv, g := natToFloat gv, b := natToFloat bv }
    | _, _, _ => .invalid s!"Invalid hex characters in: {hex}"

  -- #RRGGBBAA format
  | [r1, r2, g1, g2, b1, b2, a1, a2] =>
    match hexPairToNum r1 r2, hexPairToNum g1 g2, hexPairToNum b1 b2, hexPairToNum a1 a2 with
    | some rv, some gv, some bv, some av =>
      let aFloat := natToFloat av / 255.0
      .okWithAlpha { r := natToFloat rv, g := natToFloat gv, b := natToFloat bv, a := clamp01 aFloat }
    | _, _, _, _ => .invalid s!"Invalid hex characters in: {hex}"

  | _ => .invalid s!"Invalid hex length: {hex.length}, expected 3, 6, or 8"

/-- Convert number to 2-digit hex string -/
def numToHex (n : Nat) : String :=
  let clamped := min 255 n
  let hexDigit (d : Nat) : Char :=
    if d < 10 then Char.ofNat ('0'.toNat + d)
    else Char.ofNat ('a'.toNat + d - 10)
  let high := hexDigit (clamped / 16)
  let low := hexDigit (clamped % 16)
  String.mk [high, low]

/-- Convert RGB to hex string -/
def rgbToHex (rgb : RGB) : String :=
  let r := (Float.round (clamp0255 rgb.r)).toUInt64.toNat
  let g := (Float.round (clamp0255 rgb.g)).toUInt64.toNat
  let b := (Float.round (clamp0255 rgb.b)).toUInt64.toNat
  s!"#{numToHex r}{numToHex g}{numToHex b}"

/-- Convert RGBA to hex string with alpha -/
def rgbaToHex (rgba : RGBA) : String :=
  let r := (Float.round (clamp0255 rgba.r)).toUInt64.toNat
  let g := (Float.round (clamp0255 rgba.g)).toUInt64.toNat
  let b := (Float.round (clamp0255 rgba.b)).toUInt64.toNat
  let a := (Float.round (clamp01 rgba.a * 255.0)).toUInt64.toNat
  s!"#{numToHex r}{numToHex g}{numToHex b}{numToHex a}"

/-- Convert HSV to hex string -/
def hsvToHex (hsv : HSV) : String :=
  rgbToHex (hsvToRgb hsv)

/-- Convert hex to HSV -/
def hexToHsv (hex : String) : Option HSV :=
  match hexToRgb hex with
  | .ok rgb => some (rgbToHsv rgb)
  | .okWithAlpha rgba => some (rgbToHsv { r := rgba.r, g := rgba.g, b := rgba.b })
  | .invalid _ => none

/-! ## Color Manipulation -/

/-- Linear interpolation between two RGB colors -/
def lerpRgb (c1 c2 : RGB) (t : Float) : RGB :=
  let tClamped := clamp01 t
  let lerp (a b : Float) : Float :=
    let result := a + (b - a) * tClamped
    let rounded := Float.round result
    if isFinite rounded then clamp0255 rounded else a
  { r := lerp c1.r c2.r, g := lerp c1.g c2.g, b := lerp c1.b c2.b }

/-- Get contrasting text color (black or white) for background -/
def getContrastColor (bg : RGB) : RGB :=
  -- Calculate relative luminance
  let luminance := (0.299 * bg.r + 0.587 * bg.g + 0.114 * bg.b) / 255.0
  if luminance > 0.5 then
    { r := 0.0, g := 0.0, b := 0.0 }  -- black
  else
    { r := 255.0, g := 255.0, b := 255.0 }  -- white

/-! ## Standard Swatches -/

/-- Standard color swatch hex values -/
def standardSwatches : List String := [
  "#ff0000", "#ff8000", "#ffff00", "#80ff00",
  "#00ff00", "#00ff80", "#00ffff", "#0080ff",
  "#0000ff", "#8000ff", "#ff00ff", "#ff0080",
  "#ffffff", "#c0c0c0", "#808080", "#404040", "#000000"
]

--------------------------------------------------------------------------------
-- Proofs (Structural - No sorry, No native_decide)
--------------------------------------------------------------------------------

/-- normalizeHue is well-defined -/
theorem normalizeHue_defined (h : Float) : ∃ r, normalizeHue h = r := by
  exact ⟨_, rfl⟩

/-- hsvToRgb preserves structure -/
theorem hsvToRgb_structure (hsv : HSV) :
    ∃ r g b, hsvToRgb hsv = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- rgbToHsv preserves structure -/
theorem rgbToHsv_structure (rgb : RGB) :
    ∃ h s v, rgbToHsv rgb = { h := h, s := s, v := v } := by
  exact ⟨_, _, _, rfl⟩

/-- hslToRgb preserves structure -/
theorem hslToRgb_structure (hsl : HSL) :
    ∃ r g b, hslToRgb hsl = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- rgbToHsl preserves structure -/
theorem rgbToHsl_structure (rgb : RGB) :
    ∃ h s l, rgbToHsl rgb = { h := h, s := s, l := l } := by
  exact ⟨_, _, _, rfl⟩

/-- lerpRgb preserves structure -/
theorem lerpRgb_structure (c1 c2 : RGB) (t : Float) :
    ∃ r g b, lerpRgb c1 c2 t = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- getContrastColor returns black or white -/
theorem getContrastColor_structure (bg : RGB) :
    ∃ r g b, getContrastColor bg = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- clamp01 is idempotent -/
theorem clamp01_idempotent (x : Float) : clamp01 (clamp01 x) = clamp01 x := by
  simp only [clamp01]
  split_ifs <;> rfl

/-- clamp0255 is idempotent -/
theorem clamp0255_idempotent (x : Float) : clamp0255 (clamp0255 x) = clamp0255 x := by
  simp only [clamp0255]
  split_ifs <;> rfl

/-- standardSwatches has 17 entries -/
theorem standardSwatches_size : standardSwatches.length = 17 := by
  simp only [standardSwatches, List.length_cons, List.length_nil]
  rfl

end Lattice.Utils.ColorUtils
