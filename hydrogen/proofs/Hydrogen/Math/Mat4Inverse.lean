/-
  Hydrogen.Math.Mat4Inverse
  
  Matrix inversion for 4x4 matrices using the adjugate method.
  
  ZERO-LATENCY INVARIANTS:
    1. Inverse exists iff determinant is nonzero (proven)
    2. A × A⁻¹ = I for invertible matrices (proven)
    3. (A × B)⁻¹ = B⁻¹ × A⁻¹ (proven)
  
  The adjugate matrix is the transpose of the cofactor matrix.
  For invertible A: A⁻¹ = adj(A) / det(A)
  
  Status: FOUNDATIONAL - Required for camera and view matrix computation.
-/

import Hydrogen.Math.Mat4

namespace Hydrogen.Math

namespace Mat4

-- ═══════════════════════════════════════════════════════════════════════════════
-- COFACTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Cofactors

The cofactor C_ij is (-1)^(i+j) times the determinant of the 3×3 submatrix
obtained by deleting row i and column j.

We compute all 16 cofactors for the adjugate matrix.
-/

/-- Cofactor C_00: delete row 0, col 0 -/
def c00 (m : Mat4) : ℝ :=
  det3 m.m11 m.m21 m.m31 m.m12 m.m22 m.m32 m.m13 m.m23 m.m33

/-- Cofactor C_01: delete row 0, col 1 (negated) -/
def c01 (m : Mat4) : ℝ :=
  -(det3 m.m10 m.m20 m.m30 m.m12 m.m22 m.m32 m.m13 m.m23 m.m33)

/-- Cofactor C_02: delete row 0, col 2 -/
def c02 (m : Mat4) : ℝ :=
  det3 m.m10 m.m20 m.m30 m.m11 m.m21 m.m31 m.m13 m.m23 m.m33

/-- Cofactor C_03: delete row 0, col 3 (negated) -/
def c03 (m : Mat4) : ℝ :=
  -(det3 m.m10 m.m20 m.m30 m.m11 m.m21 m.m31 m.m12 m.m22 m.m32)

/-- Cofactor C_10: delete row 1, col 0 (negated) -/
def c10 (m : Mat4) : ℝ :=
  -(det3 m.m01 m.m21 m.m31 m.m02 m.m22 m.m32 m.m03 m.m23 m.m33)

/-- Cofactor C_11: delete row 1, col 1 -/
def c11 (m : Mat4) : ℝ :=
  det3 m.m00 m.m20 m.m30 m.m02 m.m22 m.m32 m.m03 m.m23 m.m33

/-- Cofactor C_12: delete row 1, col 2 (negated) -/
def c12 (m : Mat4) : ℝ :=
  -(det3 m.m00 m.m20 m.m30 m.m01 m.m21 m.m31 m.m03 m.m23 m.m33)

/-- Cofactor C_13: delete row 1, col 3 -/
def c13 (m : Mat4) : ℝ :=
  det3 m.m00 m.m20 m.m30 m.m01 m.m21 m.m31 m.m02 m.m22 m.m32

/-- Cofactor C_20: delete row 2, col 0 -/
def c20 (m : Mat4) : ℝ :=
  det3 m.m01 m.m11 m.m31 m.m02 m.m12 m.m32 m.m03 m.m13 m.m33

/-- Cofactor C_21: delete row 2, col 1 (negated) -/
def c21 (m : Mat4) : ℝ :=
  -(det3 m.m00 m.m10 m.m30 m.m02 m.m12 m.m32 m.m03 m.m13 m.m33)

/-- Cofactor C_22: delete row 2, col 2 -/
def c22 (m : Mat4) : ℝ :=
  det3 m.m00 m.m10 m.m30 m.m01 m.m11 m.m31 m.m03 m.m13 m.m33

/-- Cofactor C_23: delete row 2, col 3 (negated) -/
def c23 (m : Mat4) : ℝ :=
  -(det3 m.m00 m.m10 m.m30 m.m01 m.m11 m.m31 m.m02 m.m12 m.m32)

/-- Cofactor C_30: delete row 3, col 0 (negated) -/
def c30 (m : Mat4) : ℝ :=
  -(det3 m.m01 m.m11 m.m21 m.m02 m.m12 m.m22 m.m03 m.m13 m.m23)

/-- Cofactor C_31: delete row 3, col 1 -/
def c31 (m : Mat4) : ℝ :=
  det3 m.m00 m.m10 m.m20 m.m02 m.m12 m.m22 m.m03 m.m13 m.m23

/-- Cofactor C_32: delete row 3, col 2 (negated) -/
def c32 (m : Mat4) : ℝ :=
  -(det3 m.m00 m.m10 m.m20 m.m01 m.m11 m.m21 m.m03 m.m13 m.m23)

/-- Cofactor C_33: delete row 3, col 3 -/
def c33 (m : Mat4) : ℝ :=
  det3 m.m00 m.m10 m.m20 m.m01 m.m11 m.m21 m.m02 m.m12 m.m22

-- ═══════════════════════════════════════════════════════════════════════════════
-- ADJUGATE MATRIX
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Adjugate Matrix

The adjugate (classical adjoint) is the transpose of the cofactor matrix.
adj(A)_ij = C_ji

Key property: A × adj(A) = det(A) × I
-/

/-- Adjugate matrix: transpose of cofactor matrix -/
def adjugate (m : Mat4) : Mat4 :=
  -- Transpose of cofactor matrix: adj_ij = C_ji
  ⟨c00 m, c10 m, c20 m, c30 m,
   c01 m, c11 m, c21 m, c31 m,
   c02 m, c12 m, c22 m, c32 m,
   c03 m, c13 m, c23 m, c33 m⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- INVERSE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Matrix Inverse

For an invertible matrix A (det A ≠ 0):
  A⁻¹ = adj(A) / det(A)

We define inverse as a function that requires a proof of invertibility.
-/

/-- Inverse of a matrix, given proof of invertibility.
    The proof h is required for correctness theorems, not computation. -/
noncomputable def inverse (m : Mat4) (_h : IsInvertible m) : Mat4 :=
  let d := det m
  let adj := adjugate m
  scale (1 / d) adj

-- ─────────────────────────────────────────────────────────────────────────────
-- Adjugate Laws
-- ─────────────────────────────────────────────────────────────────────────────

/-- Adjugate of identity is identity -/
theorem adjugate_identity : adjugate identity = identity := by
  simp only [adjugate, identity, c00, c01, c02, c03, c10, c11, c12, c13,
             c20, c21, c22, c23, c30, c31, c32, c33, det3]
  ext <;> ring

-- The key adjugate properties (A × adj(A) = det(A) × I) require massive
-- polynomial expansion. We increase heartbeats for these critical proofs.

set_option maxHeartbeats 400000 in
/-- Key property: A × adj(A) = det(A) × I -/
theorem mul_adjugate (m : Mat4) : mul m (adjugate m) = scale (det m) identity := by
  simp only [mul, adjugate, scale, identity, det,
             c00, c01, c02, c03, c10, c11, c12, c13,
             c20, c21, c22, c23, c30, c31, c32, c33, det3]
  ext <;> ring

set_option maxHeartbeats 400000 in
/-- Key property: adj(A) × A = det(A) × I -/
theorem adjugate_mul (m : Mat4) : mul (adjugate m) m = scale (det m) identity := by
  simp only [mul, adjugate, scale, identity, det,
             c00, c01, c02, c03, c10, c11, c12, c13,
             c20, c21, c22, c23, c30, c31, c32, c33, det3]
  ext <;> ring

-- ─────────────────────────────────────────────────────────────────────────────
-- Inverse Laws
-- ─────────────────────────────────────────────────────────────────────────────

/-- Right inverse: A × A⁻¹ = I -/
theorem mul_inverse (m : Mat4) (h : IsInvertible m) : mul m (inverse m h) = identity := by
  unfold inverse
  rw [scale_mul_right, mul_adjugate]
  simp only [scale, identity]
  have hd : det m ≠ 0 := h
  ext <;> field_simp

/-- Left inverse: A⁻¹ × A = I -/
theorem inverse_mul (m : Mat4) (h : IsInvertible m) : mul (inverse m h) m = identity := by
  unfold inverse
  rw [scale_mul_left, adjugate_mul]
  simp only [scale, identity]
  have hd : det m ≠ 0 := h
  ext <;> field_simp

/-- Inverse of identity is identity -/
theorem inverse_identity : inverse identity identity_invertible = identity := by
  unfold inverse
  rw [det_identity, adjugate_identity]
  simp only [scale, identity]
  ext <;> norm_num

/-- Inverse of product: (A × B)⁻¹ = B⁻¹ × A⁻¹ -/
theorem inverse_mul_rev (a b : Mat4) (ha : IsInvertible a) (hb : IsInvertible b) :
    let hab : IsInvertible (mul a b) := mul_invertible ha hb
    inverse (mul a b) hab = mul (inverse b hb) (inverse a ha) := by
  -- Proof by showing both sides are the unique inverse of (a × b)
  -- We prove (B⁻¹ × A⁻¹) × (A × B) = I, which uniquely determines the inverse
  have key : mul (mul (inverse b hb) (inverse a ha)) (mul a b) = identity := by
    rw [mul_assoc, ← mul_assoc (inverse a ha) a b]
    rw [inverse_mul]
    rw [mul_identity_left, inverse_mul]
  -- By uniqueness of inverse, (A × B)⁻¹ = B⁻¹ × A⁻¹
  -- This requires showing that if X × Y = I and Y × X = I, then X is the unique inverse
  have key2 : mul (mul a b) (mul (inverse b hb) (inverse a ha)) = identity := by
    rw [mul_assoc, ← mul_assoc b (inverse b hb) (inverse a ha)]
    rw [mul_inverse]
    rw [mul_identity_left, mul_inverse]
  -- The final step uses that inverse is unique
  have uniqueness : ∀ (m : Mat4) (h : IsInvertible m) (x : Mat4),
      mul m x = identity → mul x m = identity → x = inverse m h := by
    intro m h x hright hleft
    calc x = mul identity x := by rw [mul_identity_left]
      _ = mul (mul (inverse m h) m) x := by rw [inverse_mul]
      _ = mul (inverse m h) (mul m x) := by rw [mul_assoc]
      _ = mul (inverse m h) identity := by rw [hright]
      _ = inverse m h := by rw [mul_identity_right]
  exact (uniqueness (mul a b) (mul_invertible ha hb) (mul (inverse b hb) (inverse a ha)) key2 key).symm

end Mat4

end Hydrogen.Math
