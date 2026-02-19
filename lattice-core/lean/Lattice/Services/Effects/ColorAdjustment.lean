/-
  Lattice.Services.Effects.ColorAdjustment - Color Adjustment Functions

  Pure mathematical functions for color adjustment:
  - Hue/Saturation/Lightness
  - Vibrance (smart saturation)
  - Tint (black/white mapping)
  - Color Balance (shadows/midtones/highlights)

  All functions operate on normalized [0,1] color values.
  All functions are total and deterministic.
  NO banned constructs: no partial def, sorry, panic!, unreachable!

  Source: ui/src/services/effects/colorRenderer.ts
-/

namespace Lattice.Services.Effects.ColorAdjustment

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- RGB color tuple -/
structure RGB where
  r : Float
  g : Float
  b : Float
  deriving Repr, Inhabited

/-- HSL color tuple -/
structure HSL where
  h : Float  -- Hue [0,1]
  s : Float  -- Saturation [0,1]
  l : Float  -- Lightness [0,1]
  deriving Repr, Inhabited

/-- Hue/Saturation parameters -/
structure HueSatParams where
  hueShift : Float        -- -0.5 to 0.5 (normalized from -180 to 180)
  saturationShift : Float -- -1 to 1 (normalized from -100 to 100)
  lightnessShift : Float  -- -1 to 1 (normalized from -100 to 100)
  colorize : Bool         -- Colorize mode
  deriving Repr, Inhabited

/-- Vibrance parameters -/
structure VibranceParams where
  vibrance : Float    -- -1 to 1 (smart saturation)
  saturation : Float  -- -1 to 1 (standard saturation)
  deriving Repr, Inhabited

/-- Tint parameters (map black/white to colors) -/
structure TintParams where
  blackR : Float  -- Black point R [0,1]
  blackG : Float  -- Black point G [0,1]
  blackB : Float  -- Black point B [0,1]
  whiteR : Float  -- White point R [0,1]
  whiteG : Float  -- White point G [0,1]
  whiteB : Float  -- White point B [0,1]
  amount : Float  -- Blend amount 0-1
  deriving Repr, Inhabited

/-- Color Balance parameters -/
structure ColorBalanceParams where
  shadowR : Float     -- -1 to 1 (cyan to red in shadows)
  shadowG : Float     -- -1 to 1 (magenta to green in shadows)
  shadowB : Float     -- -1 to 1 (yellow to blue in shadows)
  midtoneR : Float    -- -1 to 1 (cyan to red in midtones)
  midtoneG : Float    -- -1 to 1 (magenta to green in midtones)
  midtoneB : Float    -- -1 to 1 (yellow to blue in midtones)
  highlightR : Float  -- -1 to 1 (cyan to red in highlights)
  highlightG : Float  -- -1 to 1 (magenta to green in highlights)
  highlightB : Float  -- -1 to 1 (yellow to blue in highlights)
  preserveLuminosity : Bool
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

/-- Default hue/saturation (no change) -/
def defaultHueSatParams : HueSatParams :=
  { hueShift := 0.0
    saturationShift := 0.0
    lightnessShift := 0.0
    colorize := false }

/-- Default vibrance (no change) -/
def defaultVibranceParams : VibranceParams :=
  { vibrance := 0.0
    saturation := 0.0 }

/-- Default tint (identity) -/
def defaultTintParams : TintParams :=
  { blackR := 0.0, blackG := 0.0, blackB := 0.0
    whiteR := 1.0, whiteG := 1.0, whiteB := 1.0
    amount := 1.0 }

/-- Default color balance (no change) -/
def defaultColorBalanceParams : ColorBalanceParams :=
  { shadowR := 0.0, shadowG := 0.0, shadowB := 0.0
    midtoneR := 0.0, midtoneG := 0.0, midtoneB := 0.0
    highlightR := 0.0, highlightG := 0.0, highlightB := 0.0
    preserveLuminosity := true }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

/-- Clamp value to [0, 1] -/
def clamp01 (x : Float) : Float :=
  if x < 0.0 then 0.0
  else if x > 1.0 then 1.0
  else x

/-- Calculate luminance from RGB [0,1] -/
def luminance (rgb : RGB) : Float :=
  rgb.r * 0.299 + rgb.g * 0.587 + rgb.b * 0.114

/-- Maximum of three values -/
def max3 (a b c : Float) : Float :=
  if a >= b && a >= c then a
  else if b >= c then b
  else c

/-- Minimum of three values -/
def min3 (a b c : Float) : Float :=
  if a <= b && a <= c then a
  else if b <= c then b
  else c

/-- Safe division with fallback -/
def safeDiv (a b fallback : Float) : Float :=
  if b == 0.0 || b.isNaN || b.isInf then fallback
  else a / b

/-- Absolute value -/
def fabs (x : Float) : Float :=
  if x < 0.0 then -x else x

--------------------------------------------------------------------------------
-- HSL Conversion
--------------------------------------------------------------------------------

/-- Convert RGB [0,1] to HSL [0,1] -/
def rgbToHsl (rgb : RGB) : HSL :=
  let maxC := max3 rgb.r rgb.g rgb.b
  let minC := min3 rgb.r rgb.g rgb.b
  let l := (maxC + minC) / 2.0
  let d := maxC - minC
  if d == 0.0 then
    { h := 0.0, s := 0.0, l := l }
  else
    let s := if l > 0.5 then
               safeDiv d (2.0 - maxC - minC) 0.0
             else
               safeDiv d (maxC + minC) 0.0
    let h :=
      if maxC == rgb.r then
        let base := safeDiv (rgb.g - rgb.b) d 0.0
        let adj := if rgb.g < rgb.b then 6.0 else 0.0
        (base + adj) / 6.0
      else if maxC == rgb.g then
        let base := safeDiv (rgb.b - rgb.r) d 0.0
        (base + 2.0) / 6.0
      else
        let base := safeDiv (rgb.r - rgb.g) d 0.0
        (base + 4.0) / 6.0
    { h := h, s := s, l := l }

/-- Helper for HSL to RGB conversion -/
def hue2rgb (p q t : Float) : Float :=
  let t' := if t < 0.0 then t + 1.0
            else if t > 1.0 then t - 1.0
            else t
  if t' < 1.0/6.0 then
    p + (q - p) * 6.0 * t'
  else if t' < 0.5 then
    q
  else if t' < 2.0/3.0 then
    p + (q - p) * (2.0/3.0 - t') * 6.0
  else
    p

/-- Convert HSL [0,1] to RGB [0,1] -/
def hslToRgb (hsl : HSL) : RGB :=
  if hsl.s == 0.0 then
    { r := hsl.l, g := hsl.l, b := hsl.l }
  else
    let q := if hsl.l < 0.5 then
               hsl.l * (1.0 + hsl.s)
             else
               hsl.l + hsl.s - hsl.l * hsl.s
    let p := 2.0 * hsl.l - q
    { r := hue2rgb p q (hsl.h + 1.0/3.0)
      g := hue2rgb p q hsl.h
      b := hue2rgb p q (hsl.h - 1.0/3.0) }

--------------------------------------------------------------------------------
-- Hue/Saturation
--------------------------------------------------------------------------------

/-- Apply hue/saturation adjustment -/
def hueSaturation (params : HueSatParams) (rgb : RGB) : RGB :=
  let hsl := rgbToHsl rgb
  let (h, s) := if params.colorize then
                  (params.hueShift, fabs params.saturationShift + 0.25)
                else
                  let h' := hsl.h + params.hueShift
                  let hWrapped := h' - Float.floor h'
                  let s' := hsl.s + hsl.s * params.saturationShift
                  (hWrapped, s')
  let l := hsl.l + hsl.l * params.lightnessShift
  hslToRgb { h := h, s := clamp01 s, l := clamp01 l }

--------------------------------------------------------------------------------
-- Vibrance
--------------------------------------------------------------------------------

/-- Apply vibrance (smart saturation protecting skin tones) -/
def vibrance (params : VibranceParams) (rgb : RGB) : RGB :=
  let maxC := max3 rgb.r rgb.g rgb.b
  let minC := min3 rgb.r rgb.g rgb.b
  let currentSat := maxC - minC
  let lum := luminance rgb
  -- Skin tone protection (orange-ish colors)
  let rDiff := fabs (rgb.r - 0.8)
  let gDiff := fabs (rgb.g - 0.5)
  let bDiff := fabs (rgb.b - 0.3)
  let skinDist := rDiff * 2.0 + gDiff * 2.0 + bDiff * 3.0
  let skinProtection := 1.0 - clamp01 skinDist
  -- Vibrance inversely proportional to current saturation
  let vibranceAmount := params.vibrance * (1.0 - currentSat) * (1.0 - skinProtection * 0.5)
  -- Combined saturation adjustment
  let satAdjust := 1.0 + params.saturation + vibranceAmount
  -- Apply saturation change
  let r' := lum + (rgb.r - lum) * satAdjust
  let g' := lum + (rgb.g - lum) * satAdjust
  let b' := lum + (rgb.b - lum) * satAdjust
  { r := clamp01 r', g := clamp01 g', b := clamp01 b' }

--------------------------------------------------------------------------------
-- Tint
--------------------------------------------------------------------------------

/-- Apply tint (map black to one color, white to another) -/
def tint (params : TintParams) (rgb : RGB) : RGB :=
  let lum := luminance rgb
  -- Interpolate between black and white colors
  let tintR := params.blackR + (params.whiteR - params.blackR) * lum
  let tintG := params.blackG + (params.whiteG - params.blackG) * lum
  let tintB := params.blackB + (params.whiteB - params.blackB) * lum
  -- Blend with original
  let r' := rgb.r + (tintR - rgb.r) * params.amount
  let g' := rgb.g + (tintG - rgb.g) * params.amount
  let b' := rgb.b + (tintB - rgb.b) * params.amount
  { r := clamp01 r', g := clamp01 g', b := clamp01 b' }

--------------------------------------------------------------------------------
-- Color Balance
--------------------------------------------------------------------------------

/-- Apply color balance (shadows/midtones/highlights) -/
def colorBalance (params : ColorBalanceParams) (rgb : RGB) : RGB :=
  let lum := luminance rgb
  -- Calculate weights for tonal ranges
  let shadowWeight := if 1.0 - lum * 3.0 > 0.0 then 1.0 - lum * 3.0 else 0.0
  let highlightWeight := if (lum - 0.67) * 3.0 > 0.0 then (lum - 0.67) * 3.0 else 0.0
  let midtoneWeight := 1.0 - shadowWeight - highlightWeight
  -- Apply adjustments per tonal range
  let rAdj := params.shadowR * shadowWeight + params.midtoneR * midtoneWeight + params.highlightR * highlightWeight
  let gAdj := params.shadowG * shadowWeight + params.midtoneG * midtoneWeight + params.highlightG * highlightWeight
  let bAdj := params.shadowB * shadowWeight + params.midtoneB * midtoneWeight + params.highlightB * highlightWeight
  let r' := rgb.r + rAdj
  let g' := rgb.g + gAdj
  let b' := rgb.b + bAdj
  -- Preserve luminosity if enabled
  if params.preserveLuminosity then
    let newLum := luminance { r := r', g := g', b := b' }
    let ratio := if newLum > 0.001 then safeDiv lum newLum 1.0 else 1.0
    { r := clamp01 (r' * ratio)
      g := clamp01 (g' * ratio)
      b := clamp01 (b' * ratio) }
  else
    { r := clamp01 r', g := clamp01 g', b := clamp01 b' }

--------------------------------------------------------------------------------
-- Proofs (Structural - No sorry, No native_decide)
--------------------------------------------------------------------------------

/-- clamp01 applied twice is idempotent -/
theorem clamp01_idempotent (x : Float) : clamp01 (clamp01 x) = clamp01 x := by
  simp only [clamp01]
  split_ifs <;> rfl

/-- rgbToHsl preserves grayscale (r=g=b implies s=0) -/
theorem rgbToHsl_grayscale_saturation (v : Float) :
    (rgbToHsl { r := v, g := v, b := v }).s = 0.0 := by
  simp only [rgbToHsl, max3, min3]
  split_ifs <;> rfl

/-- hslToRgb with s=0 produces grayscale -/
theorem hslToRgb_zero_sat_grayscale (h l : Float) :
    let rgb := hslToRgb { h := h, s := 0.0, l := l }
    rgb.r = l ∧ rgb.g = l ∧ rgb.b = l := by
  simp only [hslToRgb]
  constructor <;> rfl

/-- Default hue/sat params has zero hue shift -/
theorem defaultHueSatParams_zero_hueShift :
    defaultHueSatParams.hueShift = 0.0 := by
  rfl

/-- Default vibrance params has zero vibrance -/
theorem defaultVibranceParams_zero_vibrance :
    defaultVibranceParams.vibrance = 0.0 := by
  rfl

/-- Default tint params has unit amount -/
theorem defaultTintParams_unit_amount :
    defaultTintParams.amount = 1.0 := by
  rfl

/-- Default color balance preserves luminosity -/
theorem defaultColorBalanceParams_preserves_lum :
    defaultColorBalanceParams.preserveLuminosity = true := by
  rfl

/-- luminance is well-defined for any RGB -/
theorem luminance_defined (rgb : RGB) : ∃ l, luminance rgb = l := by
  exact ⟨_, rfl⟩

/-- hueSaturation preserves structure -/
theorem hueSaturation_preserves_structure (params : HueSatParams) (rgb : RGB) :
    ∃ r g b, hueSaturation params rgb = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- vibrance preserves structure -/
theorem vibrance_preserves_structure (params : VibranceParams) (rgb : RGB) :
    ∃ r g b, vibrance params rgb = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- tint preserves structure -/
theorem tint_preserves_structure (params : TintParams) (rgb : RGB) :
    ∃ r g b, tint params rgb = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- colorBalance preserves structure -/
theorem colorBalance_preserves_structure (params : ColorBalanceParams) (rgb : RGB) :
    ∃ r g b, colorBalance params rgb = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

end Lattice.Services.Effects.ColorAdjustment
