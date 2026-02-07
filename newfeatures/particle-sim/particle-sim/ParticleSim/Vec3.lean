/-
  ParticleSim.Vec3
  
  Exact 3D vectors over rationals for deterministic particle simulation.
  No floating point, no rounding, bit-exact arithmetic.
-/
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Tactic

namespace ParticleSim

/-- A 3D vector with rational components for exact arithmetic -/
structure Vec3 where
  x : ℚ
  y : ℚ
  z : ℚ
deriving DecidableEq, Repr

namespace Vec3

/-- Zero vector -/
def zero : Vec3 := ⟨0, 0, 0⟩

/-- Vector addition -/
def add (v w : Vec3) : Vec3 := ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩

/-- Vector subtraction -/
def sub (v w : Vec3) : Vec3 := ⟨v.x - w.x, v.y - w.y, v.z - w.z⟩

/-- Scalar multiplication -/
def smul (c : ℚ) (v : Vec3) : Vec3 := ⟨c * v.x, c * v.y, c * v.z⟩

/-- Negation -/
def neg (v : Vec3) : Vec3 := ⟨-v.x, -v.y, -v.z⟩

/-- Dot product -/
def dot (v w : Vec3) : ℚ := v.x * w.x + v.y * w.y + v.z * w.z

/-- Squared magnitude (exact, no sqrt needed) -/
def normSq (v : Vec3) : ℚ := v.dot v

instance : Zero Vec3 := ⟨zero⟩
instance : Add Vec3 := ⟨add⟩
instance : Sub Vec3 := ⟨sub⟩
instance : Neg Vec3 := ⟨neg⟩
instance : HMul ℚ Vec3 Vec3 := ⟨smul⟩

-- ============================================================================
-- PROOFS: Addition forms an abelian group
-- ============================================================================

@[simp]
theorem add_def (v w : Vec3) : v + w = ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩ := rfl

@[simp]
theorem zero_def : (0 : Vec3) = ⟨0, 0, 0⟩ := rfl

@[simp]
theorem neg_def (v : Vec3) : -v = ⟨-v.x, -v.y, -v.z⟩ := rfl

@[simp]
theorem sub_def (v w : Vec3) : v - w = ⟨v.x - w.x, v.y - w.y, v.z - w.z⟩ := rfl

@[simp]
theorem smul_def (c : ℚ) (v : Vec3) : c * v = ⟨c * v.x, c * v.y, c * v.z⟩ := rfl

/-- Vector addition is commutative -/
theorem add_comm (v w : Vec3) : v + w = w + v := by
  simp only [add_def]
  ext <;> ring

/-- Vector addition is associative -/
theorem add_assoc (u v w : Vec3) : (u + v) + w = u + (v + w) := by
  simp only [add_def]
  ext <;> ring

/-- Zero is the additive identity (left) -/
theorem zero_add (v : Vec3) : 0 + v = v := by
  simp only [add_def, zero_def]
  ext <;> ring

/-- Zero is the additive identity (right) -/
theorem add_zero (v : Vec3) : v + 0 = v := by
  simp only [add_def, zero_def]
  ext <;> ring

/-- Every vector has an additive inverse -/
theorem add_neg (v : Vec3) : v + (-v) = 0 := by
  simp only [add_def, neg_def, zero_def]
  ext <;> ring

/-- Negation is an additive inverse (left) -/
theorem neg_add (v : Vec3) : (-v) + v = 0 := by
  rw [add_comm, add_neg]

-- ============================================================================
-- PROOFS: Scalar multiplication properties
-- ============================================================================

/-- Scalar multiplication distributes over vector addition -/
theorem smul_add (c : ℚ) (v w : Vec3) : c * (v + w) = c * v + c * w := by
  simp only [smul_def, add_def]
  ext <;> ring

/-- Scalar multiplication distributes over scalar addition -/
theorem add_smul (a b : ℚ) (v : Vec3) : (a + b) * v = a * v + b * v := by
  simp only [smul_def, add_def]
  ext <;> ring

/-- Scalar multiplication is associative with scalar multiplication -/
theorem smul_smul (a b : ℚ) (v : Vec3) : a * (b * v) = (a * b) * v := by
  simp only [smul_def]
  ext <;> ring

/-- One is the scalar multiplicative identity -/
theorem one_smul (v : Vec3) : (1 : ℚ) * v = v := by
  simp only [smul_def]
  ext <;> ring

/-- Zero scalar gives zero vector -/
theorem zero_smul (v : Vec3) : (0 : ℚ) * v = 0 := by
  simp only [smul_def, zero_def]
  ext <;> ring

/-- Scalar times zero vector is zero -/
theorem smul_zero (c : ℚ) : c * (0 : Vec3) = 0 := by
  simp only [smul_def, zero_def]
  ext <;> ring

/-- Negation is multiplication by -1 -/
theorem neg_eq_neg_one_smul (v : Vec3) : -v = (-1 : ℚ) * v := by
  simp only [neg_def, smul_def]
  ext <;> ring

-- ============================================================================
-- PROOFS: Dot product properties  
-- ============================================================================

@[simp]
theorem dot_def (v w : Vec3) : v.dot w = v.x * w.x + v.y * w.y + v.z * w.z := rfl

/-- Dot product is commutative -/
theorem dot_comm (v w : Vec3) : v.dot w = w.dot v := by
  simp only [dot_def]
  ring

/-- Dot product is linear in the first argument -/
theorem dot_add_left (u v w : Vec3) : (u + v).dot w = u.dot w + v.dot w := by
  simp only [dot_def, add_def]
  ring

/-- Dot product is linear in the second argument -/
theorem dot_add_right (u v w : Vec3) : u.dot (v + w) = u.dot v + u.dot w := by
  simp only [dot_def, add_def]
  ring

/-- Scalar factors out of dot product (left) -/
theorem dot_smul_left (c : ℚ) (v w : Vec3) : (c * v).dot w = c * (v.dot w) := by
  simp only [dot_def, smul_def]
  ring

/-- Scalar factors out of dot product (right) -/
theorem dot_smul_right (c : ℚ) (v w : Vec3) : v.dot (c * w) = c * (v.dot w) := by
  simp only [dot_def, smul_def]
  ring

/-- Dot product with zero is zero -/
theorem dot_zero (v : Vec3) : v.dot 0 = 0 := by
  simp only [dot_def, zero_def]
  ring

/-- Zero dotted with anything is zero -/
theorem zero_dot (v : Vec3) : (0 : Vec3).dot v = 0 := by
  simp only [dot_def, zero_def]
  ring

/-- Squared norm is non-negative -/
theorem normSq_nonneg (v : Vec3) : 0 ≤ v.normSq := by
  unfold normSq dot
  apply add_nonneg
  apply add_nonneg
  · exact sq_nonneg v.x
  · exact sq_nonneg v.y
  · exact sq_nonneg v.z

/-- Squared norm is zero iff vector is zero -/
theorem normSq_eq_zero_iff (v : Vec3) : v.normSq = 0 ↔ v = 0 := by
  unfold normSq dot
  constructor
  · intro h
    have hx : v.x * v.x = 0 := by
      have h1 : 0 ≤ v.x * v.x := sq_nonneg v.x
      have h2 : 0 ≤ v.y * v.y := sq_nonneg v.y
      have h3 : 0 ≤ v.z * v.z := sq_nonneg v.z
      linarith
    have hy : v.y * v.y = 0 := by
      have h1 : 0 ≤ v.x * v.x := sq_nonneg v.x
      have h2 : 0 ≤ v.y * v.y := sq_nonneg v.y
      have h3 : 0 ≤ v.z * v.z := sq_nonneg v.z
      linarith
    have hz : v.z * v.z = 0 := by
      have h1 : 0 ≤ v.x * v.x := sq_nonneg v.x
      have h2 : 0 ≤ v.y * v.y := sq_nonneg v.y
      have h3 : 0 ≤ v.z * v.z := sq_nonneg v.z
      linarith
    have hx' : v.x = 0 := mul_self_eq_zero.mp hx
    have hy' : v.y = 0 := mul_self_eq_zero.mp hy
    have hz' : v.z = 0 := mul_self_eq_zero.mp hz
    ext <;> assumption
  · intro h
    rw [h]
    simp only [zero_def]
    ring

end Vec3

end ParticleSim
