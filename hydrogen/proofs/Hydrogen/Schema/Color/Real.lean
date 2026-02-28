/-
  Hydrogen.Schema.Color.Real
  
  Real-number based color math with full proofs.
  Adapted from PRISM (https://github.com/justinfleek/PRISM)
  
  This module provides mathematically rigorous proofs for color space
  properties using Mathlib's Real type, which supports proper analysis.
  
  The Float-based Conversions.lean provides fast runtime execution.
  This module provides the mathematical guarantees.
  
  Status: IN PROGRESS
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Hydrogen.Schema.Color.Real

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: UNIT INTERVAL
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A value bounded in the unit interval [0,1] -/
structure UnitInterval where
  val : ℝ
  lower : 0 ≤ val
  upper : val ≤ 1

instance : Inhabited UnitInterval where
  default := ⟨0, le_refl 0, zero_le_one⟩

/-- Smart constructor for UnitInterval with clamping -/
def UnitInterval.clamp (x : ℝ) : UnitInterval :=
  ⟨max 0 (min x 1), 
   le_max_left 0 _, 
   max_le (by norm_num : (0 : ℝ) ≤ 1) (min_le_right x 1)⟩

/-- Clamping preserves values already in [0,1] -/
theorem UnitInterval.clamp_of_mem (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (UnitInterval.clamp x).val = x := by
  unfold clamp
  simp only [min_eq_left h1, max_eq_right h0]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: COLOR SPACE TYPES (sRGB, LinearRGB, XYZ, LAB)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- sRGB color space - gamma-corrected device color -/
structure SRGB where
  r : UnitInterval
  g : UnitInterval
  b : UnitInterval

/-- Linear RGB - physical light intensity, no gamma -/
structure LinearRGB where
  r : UnitInterval
  g : UnitInterval
  b : UnitInterval

/-- CIE XYZ color space with D65 white point -/
structure XYZ where
  x : ℝ
  y : ℝ  -- Y is luminance
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z

/-- CIE LAB perceptually uniform color space -/
structure LAB where
  l : ℝ  -- Lightness: 0-100
  a : ℝ  -- Green-Red axis
  b : ℝ  -- Blue-Yellow axis
  l_lower : 0 ≤ l
  l_upper : l ≤ 100

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: sRGB TRANSFER FUNCTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- sRGB linearization threshold -/
def srgbThreshold : ℝ := 0.04045

/-- sRGB gamma exponent -/
def srgbGamma : ℝ := 2.4

/-- sRGB gamma expansion (sRGB → Linear) for a single component -/
noncomputable def srgbToLinearComponent (c : UnitInterval) : ℝ :=
  if c.val ≤ srgbThreshold then
    c.val / 12.92
  else
    ((c.val + 0.055) / 1.055) ^ srgbGamma

/-- sRGB gamma compression (Linear → sRGB) for a single component -/
noncomputable def linearToSrgbComponent (c : UnitInterval) : ℝ :=
  if c.val ≤ 0.0031308 then
    12.92 * c.val
  else
    1.055 * (c.val ^ (1 / srgbGamma)) - 0.055

/-- sRGB linearization produces non-negative values -/
theorem srgbToLinearComponent_nonneg (c : UnitInterval) : 
    0 ≤ srgbToLinearComponent c := by
  unfold srgbToLinearComponent srgbThreshold srgbGamma
  split_ifs with h
  · apply div_nonneg c.lower; norm_num
  · apply Real.rpow_nonneg
    apply div_nonneg
    · linarith [c.lower]
    · norm_num

/-- sRGB linearization produces values ≤ 1 -/
theorem srgbToLinearComponent_le_one (c : UnitInterval) : 
    srgbToLinearComponent c ≤ 1 := by
  unfold srgbToLinearComponent srgbThreshold srgbGamma
  split_ifs with h
  · -- Linear case: c / 12.92 ≤ 0.04045 / 12.92 < 1
    calc c.val / 12.92 ≤ 0.04045 / 12.92 := by
          apply div_le_div_of_nonneg_right h; norm_num
       _ ≤ 1 := by norm_num
  · -- Gamma case: ((c + 0.055) / 1.055)^2.4 ≤ 1^2.4 = 1
    have hbase_le_one : (c.val + 0.055) / 1.055 ≤ 1 := by
      rw [div_le_one (by norm_num : (0:ℝ) < 1.055)]
      linarith [c.upper]
    have hbase_nonneg : 0 ≤ (c.val + 0.055) / 1.055 := by
      apply div_nonneg; linarith [c.lower]; norm_num
    calc ((c.val + 0.055) / 1.055) ^ (2.4 : ℝ) 
        ≤ 1 ^ (2.4 : ℝ) := by
          apply Real.rpow_le_rpow hbase_nonneg hbase_le_one; norm_num
      _ = 1 := by norm_num

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: LINEAR RGB ↔ XYZ CONVERSIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- D65 white point X reference -/
def d65Xn : ℝ := 0.95047

/-- D65 white point Y reference (luminance) -/
def d65Yn : ℝ := 1.0

/-- D65 white point Z reference -/
def d65Zn : ℝ := 1.08883

/-- Convert Linear RGB to XYZ using sRGB transformation matrix (D65 white) -/
noncomputable def linearToXYZ (c : LinearRGB) : XYZ :=
  let r := c.r.val
  let g := c.g.val
  let b := c.b.val
  ⟨0.4124564 * r + 0.3575761 * g + 0.1804375 * b,
   0.2126729 * r + 0.7151522 * g + 0.0721750 * b,  -- Y row = luminance
   0.0193339 * r + 0.1191920 * g + 0.9503041 * b,
   by -- X ≥ 0: all coefficients positive, all inputs in [0,1]
      apply add_nonneg
      apply add_nonneg
      · apply mul_nonneg (by norm_num) c.r.lower
      · apply mul_nonneg (by norm_num) c.g.lower
      · apply mul_nonneg (by norm_num) c.b.lower,
   by -- Y ≥ 0
      apply add_nonneg
      apply add_nonneg
      · apply mul_nonneg (by norm_num) c.r.lower
      · apply mul_nonneg (by norm_num) c.g.lower
      · apply mul_nonneg (by norm_num) c.b.lower,
   by -- Z ≥ 0
      apply add_nonneg
      apply add_nonneg
      · apply mul_nonneg (by norm_num) c.r.lower
      · apply mul_nonneg (by norm_num) c.g.lower
      · apply mul_nonneg (by norm_num) c.b.lower⟩

/-- Luminance (Y) from Linear RGB -/
noncomputable def luminance (c : LinearRGB) : ℝ :=
  0.2126729 * c.r.val + 0.7151522 * c.g.val + 0.0721750 * c.b.val

/-- Luminance is non-negative -/
theorem luminance_nonneg (c : LinearRGB) : 0 ≤ luminance c := by
  unfold luminance
  apply add_nonneg
  apply add_nonneg
  · apply mul_nonneg (by norm_num) c.r.lower
  · apply mul_nonneg (by norm_num) c.g.lower
  · apply mul_nonneg (by norm_num) c.b.lower

/-- Luminance is at most ~1.0000001 (for in-gamut colors) 
    Note: sRGB matrix coefficients sum to ~1.0000001 due to truncation -/
theorem luminance_le_one (c : LinearRGB) : luminance c ≤ 1.0000001 := by
  unfold luminance
  have hr : 0.2126729 * c.r.val ≤ 0.2126729 * 1 := 
    mul_le_mul_of_nonneg_left c.r.upper (by norm_num)
  have hg : 0.7151522 * c.g.val ≤ 0.7151522 * 1 := 
    mul_le_mul_of_nonneg_left c.g.upper (by norm_num)
  have hb : 0.0721750 * c.b.val ≤ 0.0721750 * 1 := 
    mul_le_mul_of_nonneg_left c.b.upper (by norm_num)
  linarith

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: XYZ ↔ LAB CONVERSIONS
-- ═══════════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: MONOTONICITY PROOFS
-- ═══════════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 7: ROUNDTRIP PROOFS
-- ═══════════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 8: RELATIVE LUMINANCE
-- ═══════════════════════════════════════════════════════════════════════════════

end Hydrogen.Schema.Color.Real
