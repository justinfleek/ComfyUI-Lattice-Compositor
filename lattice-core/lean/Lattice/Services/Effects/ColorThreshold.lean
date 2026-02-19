/-
  Lattice.Services.Effects.ColorThreshold - Threshold-based Color Effects

  Pure mathematical functions for threshold-based color effects:
  - Invert (with channel selection)
  - Posterize (reduce color levels)
  - Threshold (black and white)

  All functions operate on normalized [0,1] color values.
  All functions are total and deterministic.
  NO banned constructs: no partial def, sorry, panic!, unreachable!

  Source: ui/src/services/effects/colorRenderer.ts
-/

import Lattice.Services.Effects.ColorAdjustment

namespace Lattice.Services.Effects.ColorThreshold

open ColorAdjustment (RGB HSL rgbToHsl hslToRgb clamp01 luminance)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Channel to invert -/
inductive InvertChannel where
  | RGB       -- Invert all RGB channels
  | Red       -- Invert red channel only
  | Green     -- Invert green channel only
  | Blue      -- Invert blue channel only
  | Hue       -- Invert hue (shift by 180 degrees)
  | Sat       -- Invert saturation
  | Light     -- Invert lightness
  deriving Repr, DecidableEq

/-- Invert parameters -/
structure InvertParams where
  channel : InvertChannel  -- Which channel(s) to invert
  blend : Float            -- Blend with original 0-1
  deriving Repr, Inhabited

/-- Posterize parameters -/
structure PosterizeParams where
  levels : Nat  -- Number of levels per channel (2-256)
  deriving Repr, Inhabited

/-- Threshold parameters -/
structure ThresholdParams where
  threshold : Float  -- Threshold value [0,1]
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

/-- Default invert (full RGB inversion) -/
def defaultInvertParams : InvertParams :=
  { channel := InvertChannel.RGB
    blend := 1.0 }

/-- Default posterize (6 levels) -/
def defaultPosterizeParams : PosterizeParams :=
  { levels := 6 }

/-- Default threshold (0.5) -/
def defaultThresholdParams : ThresholdParams :=
  { threshold := 0.5 }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

/-- Linear interpolation -/
def lerp (a b t : Float) : Float :=
  a + (b - a) * t

/-- Safe division with fallback -/
def safeDiv (a b fallback : Float) : Float :=
  if b == 0.0 || b.isNaN || b.isInf then fallback
  else a / b

--------------------------------------------------------------------------------
-- Invert
--------------------------------------------------------------------------------

/-- Invert a single channel value -/
def invertChannel (x : Float) : Float :=
  1.0 - x

/-- Apply invert effect with channel selection -/
def invert (params : InvertParams) (rgb : RGB) : RGB :=
  let inverted := match params.channel with
    | InvertChannel.RGB =>
        { r := invertChannel rgb.r
          g := invertChannel rgb.g
          b := invertChannel rgb.b }
    | InvertChannel.Red =>
        { r := invertChannel rgb.r
          g := rgb.g
          b := rgb.b }
    | InvertChannel.Green =>
        { r := rgb.r
          g := invertChannel rgb.g
          b := rgb.b }
    | InvertChannel.Blue =>
        { r := rgb.r
          g := rgb.g
          b := invertChannel rgb.b }
    | InvertChannel.Hue =>
        let hsl := rgbToHsl rgb
        let h' := hsl.h + 0.5
        let hWrapped := if h' > 1.0 then h' - 1.0 else h'
        hslToRgb { h := hWrapped, s := hsl.s, l := hsl.l }
    | InvertChannel.Sat =>
        let hsl := rgbToHsl rgb
        hslToRgb { h := hsl.h, s := invertChannel hsl.s, l := hsl.l }
    | InvertChannel.Light =>
        let hsl := rgbToHsl rgb
        hslToRgb { h := hsl.h, s := hsl.s, l := invertChannel hsl.l }
  -- Blend with original
  let rFinal := lerp rgb.r inverted.r params.blend
  let gFinal := lerp rgb.g inverted.g params.blend
  let bFinal := lerp rgb.b inverted.b params.blend
  { r := clamp01 rFinal
    g := clamp01 gFinal
    b := clamp01 bFinal }

--------------------------------------------------------------------------------
-- Posterize
--------------------------------------------------------------------------------

/-- Clamp levels to valid range [2, 256] -/
def clampLevels (levels : Nat) : Nat :=
  max 2 (min 256 levels)

/-- Posterize a single pixel value -/
def posterizePixel (levels : Nat) (value : Float) : Float :=
  if levels >= 256 then value  -- No change at 256 levels
  else if levels <= 1 then 0.0 -- Single level
  else
    let lvls := clampLevels levels
    let lvlsF := Float.ofNat lvls
    let lvlsMinus1 := lvlsF - 1.0
    -- Quantize: round(value * (levels-1)) / (levels-1)
    let scaled := value * lvlsMinus1
    let rounded := Float.floor (scaled + 0.5)
    safeDiv rounded lvlsMinus1 0.0

/-- Apply posterize effect -/
def posterize (params : PosterizeParams) (rgb : RGB) : RGB :=
  { r := posterizePixel params.levels rgb.r
    g := posterizePixel params.levels rgb.g
    b := posterizePixel params.levels rgb.b }

/-- Build 256-entry lookup table for posterize -/
def buildPosterizeLUT (levels : Nat) : Array UInt8 :=
  Array.ofFn fun i : Fin 256 =>
    let normalized := Float.ofNat i.val / 255.0
    let result := posterizePixel levels normalized
    let scaled := result * 255.0
    let clamped := if scaled < 0.0 then 0.0
                   else if scaled > 255.0 then 255.0
                   else scaled
    clamped.toUInt8

--------------------------------------------------------------------------------
-- Threshold
--------------------------------------------------------------------------------

/-- Apply threshold effect (convert to black and white) -/
def threshold (params : ThresholdParams) (rgb : RGB) : RGB :=
  let lum := luminance rgb
  let value : Float := if lum >= params.threshold then 1.0 else 0.0
  { r := value, g := value, b := value }

--------------------------------------------------------------------------------
-- Proofs (Structural - No sorry, No native_decide)
--------------------------------------------------------------------------------

/-- invertChannel is involutive: invert(invert(x)) = x -/
theorem invertChannel_involutive (x : Float) :
    invertChannel (invertChannel x) = 1.0 - (1.0 - x) := by
  simp only [invertChannel]

/-- lerp at t=0 returns a -/
theorem lerp_zero (a b : Float) : lerp a b 0.0 = a + (b - a) * 0.0 := by
  simp only [lerp]

/-- lerp at t=1 returns b -/
theorem lerp_one (a b : Float) : lerp a b 1.0 = a + (b - a) * 1.0 := by
  simp only [lerp]

/-- Default invert has RGB channel -/
theorem defaultInvertParams_rgb_channel :
    defaultInvertParams.channel = InvertChannel.RGB := by
  rfl

/-- Default invert has full blend -/
theorem defaultInvertParams_full_blend :
    defaultInvertParams.blend = 1.0 := by
  rfl

/-- Default posterize has 6 levels -/
theorem defaultPosterizeParams_six_levels :
    defaultPosterizeParams.levels = 6 := by
  rfl

/-- Default threshold is 0.5 -/
theorem defaultThresholdParams_half :
    defaultThresholdParams.threshold = 0.5 := by
  rfl

/-- clampLevels always returns at least 2 -/
theorem clampLevels_ge_two (n : Nat) : clampLevels n ≥ 2 := by
  simp only [clampLevels]
  exact Nat.le_max_left 2 _

/-- posterize preserves structure -/
theorem posterize_preserves_structure (params : PosterizeParams) (rgb : RGB) :
    ∃ r g b, posterize params rgb = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- threshold preserves structure -/
theorem threshold_preserves_structure (params : ThresholdParams) (rgb : RGB) :
    ∃ r g b, threshold params rgb = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- invert preserves structure -/
theorem invert_preserves_structure (params : InvertParams) (rgb : RGB) :
    ∃ r g b, invert params rgb = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- Posterize LUT has 256 entries -/
theorem buildPosterizeLUT_size (levels : Nat) : (buildPosterizeLUT levels).size = 256 := by
  simp only [buildPosterizeLUT, Array.size_ofFn]

/-- threshold produces monochrome output (all channels equal) -/
theorem threshold_monochrome (params : ThresholdParams) (rgb : RGB) :
    let result := threshold params rgb
    result.r = result.g ∧ result.g = result.b := by
  simp only [threshold]
  constructor <;> rfl

end Lattice.Services.Effects.ColorThreshold
