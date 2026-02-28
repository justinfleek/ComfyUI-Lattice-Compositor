/-
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // lattice // math // vec3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  VEC3 — 3D VECTORS FOR AGENT SPATIAL REPRESENTATION

  "Consider a billion agents operating at 1000 tokens/second:
   Each agent needs: position, velocity, shape, color, history, state
   Each agent needs to *know* what it is and where it is"

  This module provides:
  1. Vec3 — 3D vector with proven arithmetic properties
  2. Dot product, cross product, magnitude
  3. Normalization with safety guarantees
  4. Agent position representation

-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

noncomputable section

namespace Lattice.Math

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // vec3 type
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Vec3: A 3D vector representing position, velocity, or direction.

For agent embodiment: position is WHERE the agent is. The type carries no
constraints on bounds — that's the job of WorldState invariants.
-/
@[ext]
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Vec3

/-- Zero vector -/
def zero : Vec3 := ⟨0, 0, 0⟩

/-- Unit vectors -/
def unitX : Vec3 := ⟨1, 0, 0⟩
def unitY : Vec3 := ⟨0, 1, 0⟩
def unitZ : Vec3 := ⟨0, 0, 1⟩

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // arithmetic
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Vector addition -/
def add (a b : Vec3) : Vec3 :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/-- Vector subtraction -/
def sub (a b : Vec3) : Vec3 :=
  ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

/-- Scalar multiplication -/
def scale (s : ℝ) (v : Vec3) : Vec3 :=
  ⟨s * v.x, s * v.y, s * v.z⟩

/-- Negation -/
def neg (v : Vec3) : Vec3 :=
  ⟨-v.x, -v.y, -v.z⟩

/-- Addition is commutative -/
theorem add_comm (a b : Vec3) : add a b = add b a := by
  simp only [add]
  ext <;> ring

/-- Addition is associative -/
theorem add_assoc (a b c : Vec3) : add (add a b) c = add a (add b c) := by
  simp only [add]
  ext <;> ring

/-- Zero is identity for addition -/
theorem add_zero (v : Vec3) : add v zero = v := by
  simp only [add, zero]
  ext <;> ring

/-- Zero is left identity for addition -/
theorem zero_add (v : Vec3) : add zero v = v := by
  simp only [add, zero]
  ext <;> ring

/-- Negation gives additive inverse -/
theorem add_neg (v : Vec3) : add v (neg v) = zero := by
  simp only [add, neg, zero]
  ext <;> ring

/-- Scalar multiplication distributes over vector addition -/
theorem scale_add (s : ℝ) (a b : Vec3) : scale s (add a b) = add (scale s a) (scale s b) := by
  simp only [scale, add]
  ext <;> ring

/-- Scalar multiplication distributes over scalar addition -/
theorem add_scale (s t : ℝ) (v : Vec3) : scale (s + t) v = add (scale s v) (scale t v) := by
  simp only [scale, add]
  ext <;> ring

/-- Scalar multiplication is associative -/
theorem scale_scale (s t : ℝ) (v : Vec3) : scale s (scale t v) = scale (s * t) v := by
  simp only [scale]
  ext <;> ring

/-- Scaling by 1 is identity -/
theorem scale_one (v : Vec3) : scale 1 v = v := by
  simp only [scale]
  ext <;> ring

/-- Scaling by 0 gives zero vector -/
theorem scale_zero (v : Vec3) : scale 0 v = zero := by
  simp only [scale, zero]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // dot and cross
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Dot product -/
def dot (a b : Vec3) : ℝ :=
  a.x * b.x + a.y * b.y + a.z * b.z

/-- Cross product -/
def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y,
   a.z * b.x - a.x * b.z,
   a.x * b.y - a.y * b.x⟩

/-- Dot product is commutative -/
theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  simp only [dot]
  ring

/-- Dot product distributes over addition -/
theorem dot_add (a b c : Vec3) : dot a (add b c) = dot a b + dot a c := by
  simp only [dot, add]
  ring

/-- Cross product is anticommutative -/
theorem cross_anticomm (a b : Vec3) : cross a b = neg (cross b a) := by
  simp only [cross, neg]
  ext <;> ring

/-- Cross product with self is zero -/
theorem cross_self (v : Vec3) : cross v v = zero := by
  simp only [cross, zero]
  ext <;> ring

/-- Cross product is perpendicular to both inputs -/
theorem cross_perp_left (a b : Vec3) : dot a (cross a b) = 0 := by
  simp only [dot, cross]
  ring

theorem cross_perp_right (a b : Vec3) : dot b (cross a b) = 0 := by
  simp only [dot, cross]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // magnitude
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Squared magnitude (avoids sqrt) -/
def magSq (v : Vec3) : ℝ :=
  v.x * v.x + v.y * v.y + v.z * v.z

/-- Magnitude -/
def mag (v : Vec3) : ℝ :=
  Real.sqrt (magSq v)

/-- Squared magnitude is non-negative -/
theorem magSq_nonneg (v : Vec3) : magSq v ≥ 0 := by
  simp only [magSq]
  apply add_nonneg
  apply add_nonneg
  · exact mul_self_nonneg v.x
  · exact mul_self_nonneg v.y
  · exact mul_self_nonneg v.z

/-- Magnitude is non-negative -/
theorem mag_nonneg (v : Vec3) : mag v ≥ 0 := by
  simp only [mag]
  exact Real.sqrt_nonneg (magSq v)

/-- Zero vector has zero magnitude -/
theorem mag_zero : mag zero = 0 := by
  simp only [mag, magSq, zero]
  norm_num

/-- Dot product equals squared magnitude for same vector -/
theorem dot_self_eq_magSq (v : Vec3) : dot v v = magSq v := by
  simp only [dot, magSq]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // normalization
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Normalize a vector to unit length.

SAFETY: Returns None for zero vector (cannot normalize zero).
This is enforced at the type level — agents cannot accidentally
create invalid normalized vectors.
-/
def normalize (v : Vec3) : Option Vec3 :=
  if magSq v = 0 then
    none
  else
    some (scale (1 / mag v) v)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // lerp
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Linear interpolation between two vectors -/
def lerp (a b : Vec3) (t : ℝ) : Vec3 :=
  add (scale (1 - t) a) (scale t b)

/-- Lerp at t=0 returns first vector -/
theorem lerp_at_zero (a b : Vec3) : lerp a b 0 = a := by
  simp only [lerp]
  rw [sub_zero, scale_one, scale_zero, add_zero]

/-- Lerp at t=1 returns second vector -/
theorem lerp_at_one (a b : Vec3) : lerp a b 1 = b := by
  simp only [lerp]
  rw [sub_self, scale_zero, scale_one, zero_add]

end Vec3

end Lattice.Math

end
