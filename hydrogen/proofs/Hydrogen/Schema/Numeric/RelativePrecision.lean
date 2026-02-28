/-
  Hydrogen.Schema.Numeric.RelativePrecision
  
  Relative Precision Metric for Error Analysis
  
  Based on NumFuzz/Bean (Kellison, 2025) - arXiv:2501.14598
  
  INVARIANTS:
    1. RP is symmetric: RP(x, y) = RP(y, x)
    2. RP satisfies triangle inequality
    3. RP(x, x) = 0 for all x ≠ 0
    4. RP is non-negative
  
  Status: FOUNDATIONAL
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Schema.Numeric.RelativePrecision

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: RELATIVE PRECISION DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Relative Precision Metric

Unlike relative error (|x - x̃|/|x|), relative precision is symmetric:
  RP(x, x̃) = |ln(x/x̃)|  when sign(x) = sign(x̃) and both nonzero
           = 0           when x = x̃ = 0
           = ∞           otherwise

This makes RP a proper extended metric (symmetric, triangle inequality).
-/

/-- Sign agreement predicate -/
def sameSign (x y : ℝ) : Prop := (0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0) ∨ (x = 0 ∧ y = 0)

/-- Relative precision for nonzero values with same sign -/
noncomputable def rpCore (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : ℝ :=
  |Real.log (x / y)|

/-- RP is zero when x = y (nonzero) -/
theorem rpCore_self (x : ℝ) (hx : x ≠ 0) : rpCore x x hx hx = 0 := by
  simp [rpCore, div_self hx]

/-- RP is symmetric -/
theorem rpCore_symm (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : 
    rpCore x y hx hy = rpCore y x hy hx := by
  simp [rpCore]
  rw [Real.log_div hx hy, Real.log_div hy hx]
  ring_nf
  exact abs_neg _

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: TRIANGLE INEQUALITY
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Triangle Inequality for RP

The key metric property: RP(x, z) ≤ RP(x, y) + RP(y, z)

This follows from properties of logarithms:
  ln(x/z) = ln(x/y) + ln(y/z)
  |ln(x/z)| ≤ |ln(x/y)| + |ln(y/z)|  (triangle inequality for absolute value)
-/

/-- Triangle inequality for rpCore -/
theorem rpCore_triangle (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : sameSign x y) (hyz : sameSign y z) :
    rpCore x z hx hz ≤ rpCore x y hx hy + rpCore y z hy hz := by
  simp only [rpCore]
  have h1 : Real.log (x / z) = Real.log (x / y) + Real.log (y / z) := by
    rw [Real.log_div hx hz, Real.log_div hx hy, Real.log_div hy hz]
    ring
  rw [h1]
  exact abs_add _ _

/-- RP is non-negative -/
theorem rpCore_nonneg (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : 
    0 ≤ rpCore x y hx hy := abs_nonneg _

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: OLVER'S ROUNDING MODEL
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Olver's Exponential Rounding Model

Standard model:  fl(x op y) = (x op y)(1 + δ),  |δ| ≤ u
Olver model:     fl(x op y) = (x op y)e^δ,      |δ| ≤ ε = u/(1-u)

Olver's model has better compositional properties:
  - Relative precision is preserved under composition
  - Error bounds compose multiplicatively in log space
-/

/-- Machine epsilon u for IEEE binary64 -/
noncomputable def machineU : ℝ := 2⁻⁵³

/-- Olver epsilon: ε = u/(1-u) -/
noncomputable def olverEps : ℝ := machineU / (1 - machineU)

/-- Machine epsilon is small -/
theorem machineU_lt_one : machineU < 1 := by
  unfold machineU
  norm_num

/-- Olver epsilon is positive -/
theorem olverEps_pos : 0 < olverEps := by
  unfold olverEps machineU
  apply div_pos
  · norm_num
  · have h : (2 : ℝ)⁻⁵³ < 1 := by norm_num
    linarith

/-- Olver rounding: result is within ε in log space -/
structure OlverRounded (x : ℝ) (hx : x ≠ 0) where
  result : ℝ
  result_ne_zero : result ≠ 0
  same_sign : sameSign x result
  precision_bound : rpCore x result hx result_ne_zero ≤ olverEps

end Hydrogen.Schema.Numeric.RelativePrecision
