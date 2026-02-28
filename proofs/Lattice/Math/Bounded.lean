/-
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // lattice // math // bounded
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  BOUNDED TYPES — THE FOUNDATION OF AGENT SAFETY

  "Bounded types everywhere — agents must reach definitive answers."

  At billion-agent scale:
  - Unbounded values cause crashes across swarms
  - NaN/Infinity propagate through pipelines catastrophically
  - Invalid states cannot be "handled later" — they must be unrepresentable

  This module provides:
  1. BoundedFloat — Float values with proven min/max bounds
  2. UnitInterval — Values in [0, 1] with clamping
  3. Clamping operations with idempotence proofs
  4. Linear interpolation with bounds preservation

-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

noncomputable section

namespace Lattice.Math.Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // unit interval
-- ═══════════════════════════════════════════════════════════════════════════════

/--
UnitInterval: A real number guaranteed to be in [0, 1].

This is THE fundamental bounded type. Animation progress, opacity, blend
factors — all live here. The type system guarantees bounds at compile time.
-/
structure UnitInterval where
  val : ℝ
  ge_zero : val ≥ 0
  le_one : val ≤ 1

namespace UnitInterval

/-- Zero (start of interval) -/
def zero : UnitInterval := ⟨0, le_refl 0, zero_le_one⟩

/-- One (end of interval) -/
def one : UnitInterval := ⟨1, zero_le_one, le_refl 1⟩

/-- Half (midpoint) -/
def half : UnitInterval := ⟨1/2, by norm_num, by norm_num⟩

/-- Clamp any real to [0, 1] -/
def clamp (x : ℝ) : UnitInterval :=
  ⟨max 0 (min x 1),
   le_max_left 0 (min x 1),
   by
     apply max_le
     · exact zero_le_one
     · exact min_le_right x 1⟩

/-- Clamping is idempotent: clamp(clamp(x)) = clamp(x) -/
theorem clamp_idempotent (x : ℝ) : clamp (clamp x).val = clamp x := by
  have h1 : (clamp x).val ≥ 0 := (clamp x).ge_zero
  have h2 : (clamp x).val ≤ 1 := (clamp x).le_one
  unfold clamp at *
  simp only [min_eq_left h2, max_eq_right h1]

/-- Already-valid values pass through unchanged -/
theorem clamp_noop (x : ℝ) (h_ge : x ≥ 0) (h_le : x ≤ 1) :
    (clamp x).val = x := by
  simp only [clamp, max_eq_right h_ge, min_eq_left h_le]

/-- Complement: 1 - t (for reverse animations) -/
def complement (t : UnitInterval) : UnitInterval :=
  ⟨1 - t.val,
   by linarith [t.le_one],
   by linarith [t.ge_zero]⟩

/-- Complement is involutive: complement(complement(t)) = t -/
theorem complement_involutive (t : UnitInterval) :
    complement (complement t) = t := by
  simp only [complement]
  congr 1
  ring

/-- Linear interpolation between two unit intervals -/
def lerp (a b : UnitInterval) (t : UnitInterval) : UnitInterval :=
  clamp (a.val * (1 - t.val) + b.val * t.val)

/-- Lerp at t=0 returns first value -/
theorem lerp_at_zero (a b : UnitInterval) :
    lerp a b zero = a := by
  simp only [lerp, zero]
  have h : a.val * (1 - 0) + b.val * 0 = a.val := by ring
  simp only [h, clamp]
  congr 1
  simp only [max_eq_right a.ge_zero, min_eq_left a.le_one]

/-- Lerp at t=1 returns second value -/
theorem lerp_at_one (a b : UnitInterval) :
    lerp a b one = b := by
  simp only [lerp, one]
  have h : a.val * (1 - 1) + b.val * 1 = b.val := by ring
  simp only [h, clamp]
  congr 1
  simp only [max_eq_right b.ge_zero, min_eq_left b.le_one]

end UnitInterval

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // bounded float
-- ═══════════════════════════════════════════════════════════════════════════════

/--
BoundedFloat: A real number with explicit min/max bounds.

Used for: pixel coordinates, angles, scales — any value with known domain.
The bounds are carried at the type level, ensuring operations preserve them.
-/
structure BoundedFloat (lo hi : ℝ) (h : lo ≤ hi) where
  val : ℝ
  ge_lo : val ≥ lo
  le_hi : val ≤ hi

namespace BoundedFloat

variable {lo hi : ℝ} {h : lo ≤ hi}

/-- Clamp any real to [lo, hi] -/
def clamp (x : ℝ) : BoundedFloat lo hi h :=
  ⟨max lo (min x hi),
   le_max_left lo (min x hi),
   by
     apply max_le
     · exact h
     · exact min_le_right x hi⟩

/-- Clamping is idempotent -/
theorem clamp_idempotent (x : ℝ) :
    clamp (h := h) (clamp (h := h) x).val = clamp (h := h) x := by
  have hge : (clamp (h := h) x).val ≥ lo := (clamp (h := h) x).ge_lo
  have hle : (clamp (h := h) x).val ≤ hi := (clamp (h := h) x).le_hi
  unfold clamp at *
  simp only [min_eq_left hle, max_eq_right hge]

/-- Linear interpolation -/
def lerp (a b : BoundedFloat lo hi h) (t : UnitInterval) : BoundedFloat lo hi h :=
  clamp (a.val * (1 - t.val) + b.val * t.val)

/-- Lerp stays within bounds (by construction via clamp) -/
theorem lerp_bounded (a b : BoundedFloat lo hi h) (t : UnitInterval) :
    (lerp a b t).val ≥ lo ∧ (lerp a b t).val ≤ hi :=
  ⟨(lerp a b t).ge_lo, (lerp a b t).le_hi⟩

end BoundedFloat

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // pixel type
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Pixel: A non-negative real representing pixel coordinates.

Pixels cannot be negative. This is enforced at the type level.
-/
structure Pixel where
  val : ℝ
  nonneg : val ≥ 0

namespace Pixel

/-- Zero pixel -/
def zero : Pixel := ⟨0, le_refl 0⟩

/-- Clamp to non-negative -/
def clamp (x : ℝ) : Pixel := ⟨max 0 x, le_max_left 0 x⟩

/-- Addition of pixels -/
def add (a b : Pixel) : Pixel :=
  ⟨a.val + b.val, add_nonneg a.nonneg b.nonneg⟩

/-- Addition is commutative -/
theorem add_comm (a b : Pixel) : add a b = add b a := by
  simp only [add]
  congr 1
  ring

/-- Addition is associative -/
theorem add_assoc (a b c : Pixel) : add (add a b) c = add a (add b c) := by
  simp only [add]
  congr 1
  ring

/-- Zero is identity for addition -/
theorem add_zero (p : Pixel) : add p zero = p := by
  simp only [add, zero]
  congr 1
  ring

/-- Scale by non-negative factor -/
def scale (factor : ℝ) (h : factor ≥ 0) (p : Pixel) : Pixel :=
  ⟨p.val * factor, mul_nonneg p.nonneg h⟩

end Pixel

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // aspect ratio
-- ═══════════════════════════════════════════════════════════════════════════════

/--
AspectRatio: A positive real representing width/height ratio.

Aspect ratios are always positive (you cannot have negative dimensions).
-/
structure AspectRatio where
  val : ℝ
  pos : val > 0

namespace AspectRatio

/-- Square aspect ratio (1:1) -/
def square : AspectRatio := ⟨1, by norm_num⟩

/-- Widescreen (16:9) -/
def widescreen : AspectRatio := ⟨16 / 9, by norm_num⟩

/-- Ultrawide (21:9) -/
def ultrawide : AspectRatio := ⟨21 / 9, by norm_num⟩

/-- Invert aspect ratio (portrait ↔ landscape) -/
def invert (ar : AspectRatio) : AspectRatio :=
  ⟨1 / ar.val, one_div_pos.mpr ar.pos⟩

/-- Inversion is involutive -/
theorem invert_involutive (ar : AspectRatio) : invert (invert ar) = ar := by
  simp only [invert]
  congr 1
  field_simp

/-- Predicates -/
def isSquare (ar : AspectRatio) : Prop := ar.val = 1
def isPortrait (ar : AspectRatio) : Prop := ar.val < 1
def isLandscape (ar : AspectRatio) : Prop := ar.val > 1

/-- Square is neither portrait nor landscape -/
theorem square_neither : ¬isPortrait square ∧ ¬isLandscape square := by
  simp only [isPortrait, isLandscape, square]
  constructor <;> norm_num

end AspectRatio

end Lattice.Math.Bounded

end
