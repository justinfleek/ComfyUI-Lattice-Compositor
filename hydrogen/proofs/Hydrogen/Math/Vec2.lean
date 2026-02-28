/-
  Hydrogen.Math.Vec2
  
  2D Vector type for particle physics and UI layout.
  
  PROVEN INVARIANTS:
    1. perp_orthogonal: perp(v) · v = 0 (perpendicular is orthogonal)
       → Vortex forces do no work (tangent to radius)
    2. perpCW_orthogonal: perpCW(v) · v = 0 (clockwise perpendicular)
    3. lengthSq_perp: |perp(v)|² = |v|² (rotation preserves length)
    4. perp_perp: perp(perp(v)) = -v (180° rotation)
    5. lengthSq_nonneg, length_nonneg: length ≥ 0
    6. lengthSq_eq_zero: |v|² = 0 ↔ v = zero
    7. dot_comm, dot_self_nonneg: dot product laws
    8. add forms abelian group: add_comm, add_assoc, add_zero, add_neg
    9. lerp_zero, lerp_one, lerp_self: interpolation endpoints
  
  NOT YET PROVEN (future work):
    - normalize_length: |normalize(v)| = 1 (requires nonzero proof)
    - Cauchy-Schwarz: |a·b| ≤ |a||b|
  
  PARTICLE PHYSICS APPLICATIONS:
    - Position, velocity, acceleration vectors
    - Force vectors (vortex forces use perp)
    - Collision normals and tangents
    - 2D constraint solving
  
  Status: FOUNDATIONAL - All theorems fully proven, no sorry, no custom axioms.
-/

import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- VEC2 DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- 2D vector with real components -/
structure Vec2 where
  x : ℝ
  y : ℝ

namespace Vec2

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {a b : Vec2} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Zero vector -/
def zero : Vec2 := ⟨0, 0⟩

/-- Unit vectors -/
def unitX : Vec2 := ⟨1, 0⟩
def unitY : Vec2 := ⟨0, 1⟩

/-- Uniform vector (both components equal) -/
def uniform (s : ℝ) : Vec2 := ⟨s, s⟩

/-- One vector (all 1s) -/
def one : Vec2 := uniform 1

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Vector addition -/
def add (a b : Vec2) : Vec2 := ⟨a.x + b.x, a.y + b.y⟩

/-- Vector subtraction -/
def sub (a b : Vec2) : Vec2 := ⟨a.x - b.x, a.y - b.y⟩

/-- Scalar multiplication -/
def scale (s : ℝ) (v : Vec2) : Vec2 := ⟨s * v.x, s * v.y⟩

/-- Negation -/
def neg (v : Vec2) : Vec2 := ⟨-v.x, -v.y⟩

/-- Component-wise multiplication (Hadamard product) -/
def hadamard (a b : Vec2) : Vec2 := ⟨a.x * b.x, a.y * b.y⟩

instance : Add Vec2 := ⟨add⟩
instance : Sub Vec2 := ⟨sub⟩
instance : Neg Vec2 := ⟨neg⟩
instance : HMul ℝ Vec2 Vec2 := ⟨scale⟩
instance : Zero Vec2 := ⟨zero⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- DOT PRODUCT AND PERPENDICULAR
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Dot product: a · b = ax*bx + ay*by -/
def dot (a b : Vec2) : ℝ := a.x * b.x + a.y * b.y

/-- Perpendicular vector (90° counter-clockwise rotation)
    
    THIS IS CRITICAL FOR PARTICLE PHYSICS:
    - Vortex forces use perpendicular direction
    - Collision tangents
    - 2D cross product analog
-/
def perp (v : Vec2) : Vec2 := ⟨-v.y, v.x⟩

/-- Perpendicular (clockwise rotation) -/
def perpCW (v : Vec2) : Vec2 := ⟨v.y, -v.x⟩

/-- 2D "cross product" (returns scalar: the z-component of 3D cross)
    
    Used for: winding order, signed area, angular velocity
-/
def cross (a b : Vec2) : ℝ := a.x * b.y - a.y * b.x

-- ═══════════════════════════════════════════════════════════════════════════════
-- LENGTH AND NORMALIZATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Squared length (avoids sqrt, useful for comparisons) -/
def lengthSq (v : Vec2) : ℝ := v.x * v.x + v.y * v.y

/-- Length (Euclidean norm) -/
noncomputable def length (v : Vec2) : ℝ := Real.sqrt (lengthSq v)

/-- Normalize to unit length -/
noncomputable def normalize (v : Vec2) (_h : v ≠ zero) : Vec2 :=
  let len := length v
  scale (1 / len) v

/-- Distance between two points -/
noncomputable def dist (a b : Vec2) : ℝ := length (sub a b)

/-- Squared distance (avoids sqrt) -/
def distSq (a b : Vec2) : ℝ := lengthSq (sub a b)

-- ═══════════════════════════════════════════════════════════════════════════════
-- ALGEBRAIC LAWS
-- ═══════════════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────────────
-- Addition Laws
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_comm (a b : Vec2) : add a b = add b a := by
  simp only [add]
  ext <;> ring

theorem add_assoc (a b c : Vec2) : add (add a b) c = add a (add b c) := by
  simp only [add]
  ext <;> ring

theorem add_zero (v : Vec2) : add v zero = v := by
  simp only [add, zero]
  ext <;> ring

theorem zero_add (v : Vec2) : add zero v = v := by
  simp only [add, zero]
  ext <;> ring

theorem add_neg (v : Vec2) : add v (neg v) = zero := by
  simp only [add, neg, zero]
  ext <;> ring

-- ─────────────────────────────────────────────────────────────────────────────
-- Scalar Multiplication Laws
-- ─────────────────────────────────────────────────────────────────────────────

theorem scale_one (v : Vec2) : scale 1 v = v := by
  simp only [scale]
  ext <;> ring

theorem scale_zero_vec (s : ℝ) : scale s zero = zero := by
  simp only [scale, zero]
  ext <;> ring

theorem scale_zero_scalar (v : Vec2) : scale 0 v = zero := by
  simp only [scale, zero]
  ext <;> ring

theorem scale_assoc (s t : ℝ) (v : Vec2) : scale s (scale t v) = scale (s * t) v := by
  simp only [scale]
  ext <;> ring

theorem scale_distrib_vec (s : ℝ) (a b : Vec2) : scale s (add a b) = add (scale s a) (scale s b) := by
  simp only [scale, add]
  ext <;> ring

theorem scale_distrib_scalar (s t : ℝ) (v : Vec2) : scale (s + t) v = add (scale s v) (scale t v) := by
  simp only [scale, add]
  ext <;> ring

-- ─────────────────────────────────────────────────────────────────────────────
-- Dot Product Laws
-- ─────────────────────────────────────────────────────────────────────────────

theorem dot_comm (a b : Vec2) : dot a b = dot b a := by
  simp only [dot]
  ring

theorem dot_self_nonneg (v : Vec2) : 0 ≤ dot v v := by
  simp only [dot]
  have h1 : 0 ≤ v.x * v.x := mul_self_nonneg v.x
  have h2 : 0 ≤ v.y * v.y := mul_self_nonneg v.y
  linarith

theorem dot_self_eq_lengthSq (v : Vec2) : dot v v = lengthSq v := by
  simp only [dot, lengthSq]

theorem dot_scale_left (s : ℝ) (a b : Vec2) : dot (scale s a) b = s * dot a b := by
  simp only [dot, scale]
  ring

theorem dot_scale_right (s : ℝ) (a b : Vec2) : dot a (scale s b) = s * dot a b := by
  simp only [dot, scale]
  ring

theorem dot_add_left (a b c : Vec2) : dot (add a b) c = dot a c + dot b c := by
  simp only [dot, add]
  ring

theorem dot_add_right (a b c : Vec2) : dot a (add b c) = dot a b + dot a c := by
  simp only [dot, add]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PERPENDICULAR PROOFS (THE KEY PARTICLE PHYSICS THEOREMS)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- THE CRITICAL THEOREM: perpendicular vector is orthogonal to original
    
    This proves vortex force calculation is correct:
    perp(v) · v = 0, so tangential force does no work in radial direction
-/
theorem perp_orthogonal (v : Vec2) : dot (perp v) v = 0 := by
  simp only [dot, perp]
  ring

/-- Clockwise perpendicular is also orthogonal -/
theorem perpCW_orthogonal (v : Vec2) : dot (perpCW v) v = 0 := by
  simp only [dot, perpCW]
  ring

/-- perp and perpCW are negatives of each other -/
theorem perp_neg_perpCW (v : Vec2) : perp v = neg (perpCW v) := by
  simp only [perp, perpCW, neg]
  ext <;> ring

/-- Perpendicular preserves length -/
theorem lengthSq_perp (v : Vec2) : lengthSq (perp v) = lengthSq v := by
  simp only [lengthSq, perp]
  ring

/-- Double perpendicular is negation -/
theorem perp_perp (v : Vec2) : perp (perp v) = neg v := by
  simp only [perp, neg]

/-- Four perpendiculars returns to original -/
theorem perp_perp_perp_perp (v : Vec2) : perp (perp (perp (perp v))) = v := by
  simp only [perp]
  ext <;> ring

-- ─────────────────────────────────────────────────────────────────────────────
-- Length Laws
-- ─────────────────────────────────────────────────────────────────────────────

theorem lengthSq_nonneg (v : Vec2) : 0 ≤ lengthSq v := by
  simp only [lengthSq]
  have h1 : 0 ≤ v.x * v.x := mul_self_nonneg v.x
  have h2 : 0 ≤ v.y * v.y := mul_self_nonneg v.y
  linarith

theorem length_nonneg (v : Vec2) : 0 ≤ length v := by
  simp only [length]
  exact Real.sqrt_nonneg _

theorem lengthSq_zero : lengthSq zero = 0 := by
  simp only [lengthSq, zero]
  ring

theorem length_zero : length zero = 0 := by
  simp only [length, lengthSq_zero, Real.sqrt_zero]

theorem lengthSq_eq_zero {v : Vec2} : lengthSq v = 0 ↔ v = zero := by
  constructor
  · intro h
    simp only [lengthSq] at h
    have h1 : v.x * v.x ≥ 0 := mul_self_nonneg v.x
    have h2 : v.y * v.y ≥ 0 := mul_self_nonneg v.y
    have hx : v.x * v.x = 0 := by linarith
    have hy : v.y * v.y = 0 := by linarith
    have ex : v.x = 0 := mul_self_eq_zero.mp hx
    have ey : v.y = 0 := mul_self_eq_zero.mp hy
    ext <;> simp only [zero] <;> assumption
  · intro h
    rw [h]
    exact lengthSq_zero

-- ═══════════════════════════════════════════════════════════════════════════════
-- LERP (Linear Interpolation)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Linear interpolation between two vectors -/
def lerp (a b : Vec2) (t : ℝ) : Vec2 :=
  add (scale (1 - t) a) (scale t b)

theorem lerp_zero (a b : Vec2) : lerp a b 0 = a := by
  simp only [lerp, scale, add]
  ext <;> ring

theorem lerp_one (a b : Vec2) : lerp a b 1 = b := by
  simp only [lerp, scale, add]
  ext <;> ring

theorem lerp_self (v : Vec2) (t : ℝ) : lerp v v t = v := by
  simp only [lerp, scale, add]
  ext <;> ring

end Vec2

end Hydrogen.Math
