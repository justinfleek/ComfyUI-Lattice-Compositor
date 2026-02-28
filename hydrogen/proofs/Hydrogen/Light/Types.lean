/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       HYDROGEN // LIGHT // TYPES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Core light types with proven invariants.
  
  This module defines the foundational light types following Three.js patterns,
  with physically-based invariants proven at compile time.
  
  KEY INVARIANTS:
    - Intensity: non-negative (lights don't subtract light)
    - Color components: in [0, 1] for normalized RGB
    - Decay: non-negative (light doesn't amplify with distance)
    - Distance: non-negative (cutoff distance)
    - Cone angle: in (0, π/2] for spotlights
    - Penumbra: in [0, 1] for soft edges
  
  PHOTOMETRIC UNITS (when physically correct):
    - DirectionalLight: lux (lm/m²)
    - PointLight: candela (cd)
    - SpotLight: candela (cd)
    - RectAreaLight: nits (cd/m²)
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Vec3  : Light position, direction
  - Color : Light color (via RGB components)
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Math.Vec3
import Mathlib.Data.Real.Basic

namespace Hydrogen.Light

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: LIGHT TYPE ENUMERATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Types of lights supported -/
inductive LightType where
  | ambient       -- Uniform light from all directions
  | directional   -- Parallel rays (sun, distant light)
  | point         -- Omnidirectional point source (bulb)
  | spot          -- Cone of light (flashlight, stage light)
  | hemisphere    -- Two-color ambient (sky + ground)
  | rectArea      -- Area light (soft box, window)
  deriving Repr, BEq, DecidableEq

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: COLOR (RGB Components)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Normalized RGB color with components in [0, 1] -/
structure ColorRGB where
  r : ℝ
  g : ℝ
  b : ℝ
  r_ge_0 : r ≥ 0
  r_le_1 : r ≤ 1
  g_ge_0 : g ≥ 0
  g_le_1 : g ≤ 1
  b_ge_0 : b ≥ 0
  b_le_1 : b ≤ 1

namespace ColorRGB

def white : ColorRGB where
  r := 1
  g := 1
  b := 1
  r_ge_0 := by norm_num
  r_le_1 := by norm_num
  g_ge_0 := by norm_num
  g_le_1 := by norm_num
  b_ge_0 := by norm_num
  b_le_1 := by norm_num

def black : ColorRGB where
  r := 0
  g := 0
  b := 0
  r_ge_0 := by norm_num
  r_le_1 := by norm_num
  g_ge_0 := by norm_num
  g_le_1 := by norm_num
  b_ge_0 := by norm_num
  b_le_1 := by norm_num

/-- Warm white (incandescent-like, ~2700K) -/
def warmWhite : ColorRGB where
  r := 1
  g := 0.85
  b := 0.7
  r_ge_0 := by norm_num
  r_le_1 := by norm_num
  g_ge_0 := by norm_num
  g_le_1 := by norm_num
  b_ge_0 := by norm_num
  b_le_1 := by norm_num

/-- Cool white (daylight-like, ~6500K) -/
def coolWhite : ColorRGB where
  r := 0.85
  g := 0.9
  b := 1
  r_ge_0 := by norm_num
  r_le_1 := by norm_num
  g_ge_0 := by norm_num
  g_le_1 := by norm_num
  b_ge_0 := by norm_num
  b_le_1 := by norm_num

/-- Golden hour sunlight -/
def goldenHour : ColorRGB where
  r := 1
  g := 0.75
  b := 0.4
  r_ge_0 := by norm_num
  r_le_1 := by norm_num
  g_ge_0 := by norm_num
  g_le_1 := by norm_num
  b_ge_0 := by norm_num
  b_le_1 := by norm_num

/-- Blue sky ambient -/
def skyBlue : ColorRGB where
  r := 0.5
  g := 0.7
  b := 1
  r_ge_0 := by norm_num
  r_le_1 := by norm_num
  g_ge_0 := by norm_num
  g_le_1 := by norm_num
  b_ge_0 := by norm_num
  b_le_1 := by norm_num

/-- Luminance (perceived brightness) using Rec.709 coefficients -/
noncomputable def luminance (c : ColorRGB) : ℝ :=
  0.2126 * c.r + 0.7152 * c.g + 0.0722 * c.b

/-- Luminance is non-negative -/
theorem luminance_ge_0 (c : ColorRGB) : luminance c ≥ 0 := by
  unfold luminance
  have hr := c.r_ge_0
  have hg := c.g_ge_0
  have hb := c.b_ge_0
  nlinarith

/-- Luminance is at most 1 -/
theorem luminance_le_1 (c : ColorRGB) : luminance c ≤ 1 := by
  unfold luminance
  have hr := c.r_le_1
  have hg := c.g_le_1
  have hb := c.b_le_1
  -- 0.2126 + 0.7152 + 0.0722 = 1
  nlinarith

end ColorRGB

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: INTENSITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Light intensity, non-negative.
    Units depend on light type and physically correct mode:
    - Legacy: arbitrary units
    - Physically correct: lux, candela, or nits -/
structure Intensity where
  value : ℝ
  non_negative : value ≥ 0

namespace Intensity

def zero : Intensity where value := 0; non_negative := by norm_num
def one : Intensity where value := 1; non_negative := by norm_num

/-- Typical indoor ambient: ~50-100 lux -/
def indoorAmbient : Intensity where value := 75; non_negative := by norm_num

/-- Overcast day: ~1000 lux -/
def overcast : Intensity where value := 1000; non_negative := by norm_num

/-- Direct sunlight: ~100,000 lux -/
def directSunlight : Intensity where value := 100000; non_negative := by norm_num

/-- 60W bulb equivalent: ~800 lumens → ~65 candela -/
def bulb60W : Intensity where value := 65; non_negative := by norm_num

/-- 100W bulb equivalent: ~1600 lumens → ~130 candela -/
def bulb100W : Intensity where value := 130; non_negative := by norm_num

/-- Scale intensity by a non-negative factor -/
noncomputable def scale (i : Intensity) (factor : ℝ) (hf : factor ≥ 0) : Intensity where
  value := i.value * factor
  non_negative := mul_nonneg i.non_negative hf

/-- Scaling by 1 preserves intensity -/
theorem scale_one (i : Intensity) : (i.scale 1 (by norm_num)).value = i.value := by
  simp [scale]

/-- Scaling by 0 gives zero intensity -/
theorem scale_zero (i : Intensity) : (i.scale 0 (by norm_num)).value = 0 := by
  simp [scale]

end Intensity

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: DECAY / ATTENUATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Light decay exponent, non-negative.
    - 0: No decay (constant intensity)
    - 1: Linear decay
    - 2: Physically correct inverse square law -/
structure Decay where
  value : ℝ
  non_negative : value ≥ 0

namespace Decay

def none : Decay where value := 0; non_negative := by norm_num
def linear : Decay where value := 1; non_negative := by norm_num
def physical : Decay where value := 2; non_negative := by norm_num

end Decay

/-- Cutoff distance for lights (0 = infinite) -/
structure CutoffDistance where
  value : ℝ
  non_negative : value ≥ 0

namespace CutoffDistance

def infinite : CutoffDistance where value := 0; non_negative := by norm_num
def short : CutoffDistance where value := 5; non_negative := by norm_num
def medium : CutoffDistance where value := 20; non_negative := by norm_num
def long : CutoffDistance where value := 100; non_negative := by norm_num

/-- Check if distance is infinite (value = 0) -/
noncomputable def isInfinite (d : CutoffDistance) : Bool := d.value == 0

end CutoffDistance

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: CONE PARAMETERS (for SpotLight)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Spot light cone angle in radians, in (0, π/2].
    This is the half-angle of the cone. -/
structure ConeAngle where
  value : ℝ
  positive : value > 0
  le_pi_half : value ≤ Real.pi / 2

namespace ConeAngle

/-- Narrow spot (5°) -/
noncomputable def narrow : ConeAngle where
  value := 5 * Real.pi / 180
  positive := by positivity
  le_pi_half := by
    have hpi : Real.pi > 0 := Real.pi_pos
    nlinarith

/-- Medium spot (30°) -/
noncomputable def medium : ConeAngle where
  value := 30 * Real.pi / 180
  positive := by positivity
  le_pi_half := by
    have hpi : Real.pi > 0 := Real.pi_pos
    nlinarith

/-- Wide spot (45°) -/
noncomputable def wide : ConeAngle where
  value := 45 * Real.pi / 180
  positive := by positivity
  le_pi_half := by
    have hpi : Real.pi > 0 := Real.pi_pos
    nlinarith

/-- Maximum cone (90° half-angle = hemisphere) -/
noncomputable def maximum : ConeAngle where
  value := Real.pi / 2
  positive := by positivity
  le_pi_half := le_refl _

/-- Cosine of cone angle (used for cutoff calculation) -/
noncomputable def cosine (a : ConeAngle) : ℝ := Real.cos a.value

/-- Cosine of cone angle is non-negative (since angle ≤ π/2) -/
theorem cosine_nonneg (a : ConeAngle) : a.cosine ≥ 0 := by
  unfold cosine
  have hpos := a.positive
  have hle := a.le_pi_half
  have hge : a.value ≥ 0 := le_of_lt hpos
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, hle⟩

/-- Cosine of cone angle is at most 1 -/
theorem cosine_le_1 (a : ConeAngle) : a.cosine ≤ 1 := Real.cos_le_one a.value

end ConeAngle

/-- Penumbra factor for soft spotlight edges, in [0, 1].
    - 0: Hard edge
    - 1: Completely soft (linear falloff from center to edge) -/
structure Penumbra where
  value : ℝ
  ge_0 : value ≥ 0
  le_1 : value ≤ 1

namespace Penumbra

def hard : Penumbra where
  value := 0
  ge_0 := by norm_num
  le_1 := by norm_num

def soft : Penumbra where
  value := 0.5
  ge_0 := by norm_num
  le_1 := by norm_num

def verySoft : Penumbra where
  value := 1
  ge_0 := by norm_num
  le_1 := by norm_num

end Penumbra

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: SHADOW CONFIGURATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Shadow map resolution (power of 2 for GPU efficiency) -/
inductive ShadowMapResolution where
  | r256   -- 256×256
  | r512   -- 512×512
  | r1024  -- 1024×1024
  | r2048  -- 2048×2048
  | r4096  -- 4096×4096
  deriving Repr, BEq, DecidableEq

namespace ShadowMapResolution

def toNat : ShadowMapResolution → Nat
  | r256 => 256
  | r512 => 512
  | r1024 => 1024
  | r2048 => 2048
  | r4096 => 4096

theorem toNat_positive (r : ShadowMapResolution) : r.toNat > 0 := by
  cases r <;> simp [toNat]

theorem toNat_power_of_two (r : ShadowMapResolution) : ∃ n : Nat, r.toNat = 2^n := by
  cases r
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩

end ShadowMapResolution

/-- Shadow bias to prevent shadow acne -/
structure ShadowBias where
  depth : ℝ       -- Depth buffer bias
  normal : ℝ      -- Normal offset bias

namespace ShadowBias

def default : ShadowBias where depth := 0.0001; normal := 0.01
def minimal : ShadowBias where depth := 0.00001; normal := 0.001
def aggressive : ShadowBias where depth := 0.001; normal := 0.05

end ShadowBias

/-- Shadow configuration -/
structure ShadowConfig where
  enabled : Bool
  resolution : ShadowMapResolution
  bias : ShadowBias
  radius : ℝ                  -- PCF blur radius
  blurSamples : Nat           -- PCF sample count
  radius_ge_0 : radius ≥ 0
  blurSamples_positive : blurSamples > 0

namespace ShadowConfig

def disabled : ShadowConfig where
  enabled := false
  resolution := .r1024
  bias := ShadowBias.default
  radius := 1
  blurSamples := 8
  radius_ge_0 := by norm_num
  blurSamples_positive := by norm_num

def lowQuality : ShadowConfig where
  enabled := true
  resolution := .r512
  bias := ShadowBias.default
  radius := 2
  blurSamples := 4
  radius_ge_0 := by norm_num
  blurSamples_positive := by norm_num

def highQuality : ShadowConfig where
  enabled := true
  resolution := .r2048
  bias := ShadowBias.minimal
  radius := 1
  blurSamples := 16
  radius_ge_0 := by norm_num
  blurSamples_positive := by norm_num

def ultraQuality : ShadowConfig where
  enabled := true
  resolution := .r4096
  bias := ShadowBias.minimal
  radius := 0.5
  blurSamples := 32
  radius_ge_0 := by norm_num
  blurSamples_positive := by norm_num

end ShadowConfig

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: BASE LIGHT STRUCTURE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Base light properties common to all light types -/
structure LightBase where
  color : ColorRGB
  intensity : Intensity
  castShadow : Bool
  shadowConfig : ShadowConfig

namespace LightBase

def defaultWhite : LightBase where
  color := ColorRGB.white
  intensity := Intensity.one
  castShadow := false
  shadowConfig := ShadowConfig.disabled

def defaultWithShadow : LightBase where
  color := ColorRGB.white
  intensity := Intensity.one
  castShadow := true
  shadowConfig := ShadowConfig.highQuality

/-- Effective intensity (intensity * luminance for colored lights) -/
noncomputable def effectiveIntensity (light : LightBase) : ℝ :=
  light.intensity.value * ColorRGB.luminance light.color

/-- Effective intensity is non-negative -/
theorem effectiveIntensity_ge_0 (light : LightBase) : light.effectiveIntensity ≥ 0 := by
  unfold effectiveIntensity
  have hi := light.intensity.non_negative
  have hl := ColorRGB.luminance_ge_0 light.color
  exact mul_nonneg hi hl

end LightBase

end Hydrogen.Light
