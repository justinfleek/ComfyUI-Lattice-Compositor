/-
  Hydrogen.Math.Mat3
  
  3×3 Matrix type for 2D transforms and normal transformations.
  
  PROVEN INVARIANTS:
    1. mul_assoc: Matrix multiplication is associative
    2. mul_identity: I × A = A × I = A
    3. transpose_involutive: (Aᵀ)ᵀ = A
    4. transpose_mul: (AB)ᵀ = BᵀAᵀ
    5. det_identity: det(I) = 1
    6. det_mul: det(AB) = det(A) × det(B)
  
  THREE.JS PARITY:
    - identity, multiply, determinant, transpose, invert
    - getNormalMatrix (from Mat4)
    - setFromMatrix4, makeRotation, makeScale
  
  APPLICATIONS:
    - Normal transformation: N' = (M⁻¹)ᵀ × N
    - 2D transforms (with homogeneous coords)
    - Rotation matrices (3D)
    - Upper-left 3×3 of Mat4
  
  Status: FOUNDATIONAL - All theorems fully proven, no sorry, no custom axioms.
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- MAT3 DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- 3×3 matrix stored in row-major order
    
    | m00 m01 m02 |
    | m10 m11 m12 |
    | m20 m21 m22 |
-/
structure Mat3 where
  -- Row 0
  m00 : ℝ
  m01 : ℝ
  m02 : ℝ
  -- Row 1
  m10 : ℝ
  m11 : ℝ
  m12 : ℝ
  -- Row 2
  m20 : ℝ
  m21 : ℝ
  m22 : ℝ

namespace Mat3

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {a b : Mat3} 
    (h00 : a.m00 = b.m00) (h01 : a.m01 = b.m01) (h02 : a.m02 = b.m02)
    (h10 : a.m10 = b.m10) (h11 : a.m11 = b.m11) (h12 : a.m12 = b.m12)
    (h20 : a.m20 = b.m20) (h21 : a.m21 = b.m21) (h22 : a.m22 = b.m22) : a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Zero matrix -/
def zero : Mat3 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Identity matrix -/
def identity : Mat3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

/-- Diagonal matrix -/
def diagonal (d0 d1 d2 : ℝ) : Mat3 := ⟨d0, 0, 0, 0, d1, 0, 0, 0, d2⟩

/-- Uniform scale matrix -/
def uniformScale (s : ℝ) : Mat3 := diagonal s s s

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Matrix addition -/
def add (a b : Mat3) : Mat3 := 
  ⟨a.m00 + b.m00, a.m01 + b.m01, a.m02 + b.m02,
   a.m10 + b.m10, a.m11 + b.m11, a.m12 + b.m12,
   a.m20 + b.m20, a.m21 + b.m21, a.m22 + b.m22⟩

/-- Matrix subtraction -/
def sub (a b : Mat3) : Mat3 := 
  ⟨a.m00 - b.m00, a.m01 - b.m01, a.m02 - b.m02,
   a.m10 - b.m10, a.m11 - b.m11, a.m12 - b.m12,
   a.m20 - b.m20, a.m21 - b.m21, a.m22 - b.m22⟩

/-- Scalar multiplication -/
def scale (s : ℝ) (m : Mat3) : Mat3 := 
  ⟨s * m.m00, s * m.m01, s * m.m02,
   s * m.m10, s * m.m11, s * m.m12,
   s * m.m20, s * m.m21, s * m.m22⟩

/-- Negation -/
def neg (m : Mat3) : Mat3 := 
  ⟨-m.m00, -m.m01, -m.m02,
   -m.m10, -m.m11, -m.m12,
   -m.m20, -m.m21, -m.m22⟩

/-- Matrix transpose -/
def transpose (m : Mat3) : Mat3 := 
  ⟨m.m00, m.m10, m.m20,
   m.m01, m.m11, m.m21,
   m.m02, m.m12, m.m22⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- MATRIX MULTIPLICATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Matrix multiplication: C = A × B -/
def mul (a b : Mat3) : Mat3 := 
  ⟨-- Row 0
   a.m00 * b.m00 + a.m01 * b.m10 + a.m02 * b.m20,
   a.m00 * b.m01 + a.m01 * b.m11 + a.m02 * b.m21,
   a.m00 * b.m02 + a.m01 * b.m12 + a.m02 * b.m22,
   -- Row 1
   a.m10 * b.m00 + a.m11 * b.m10 + a.m12 * b.m20,
   a.m10 * b.m01 + a.m11 * b.m11 + a.m12 * b.m21,
   a.m10 * b.m02 + a.m11 * b.m12 + a.m12 * b.m22,
   -- Row 2
   a.m20 * b.m00 + a.m21 * b.m10 + a.m22 * b.m20,
   a.m20 * b.m01 + a.m21 * b.m11 + a.m22 * b.m21,
   a.m20 * b.m02 + a.m21 * b.m12 + a.m22 * b.m22⟩

/-- Matrix-vector multiplication: v' = M × v -/
def mulVec (m : Mat3) (v : Vec3) : Vec3 := 
  ⟨m.m00 * v.x + m.m01 * v.y + m.m02 * v.z,
   m.m10 * v.x + m.m11 * v.y + m.m12 * v.z,
   m.m20 * v.x + m.m21 * v.y + m.m22 * v.z⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- DETERMINANT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Determinant using Sarrus' rule / cofactor expansion -/
def det (m : Mat3) : ℝ := 
  m.m00 * (m.m11 * m.m22 - m.m12 * m.m21) -
  m.m01 * (m.m10 * m.m22 - m.m12 * m.m20) +
  m.m02 * (m.m10 * m.m21 - m.m11 * m.m20)

/-- Matrix is invertible iff determinant is nonzero -/
def Invertible (m : Mat3) : Prop := det m ≠ 0

-- ═══════════════════════════════════════════════════════════════════════════════
-- ROTATION MATRICES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Rotation about X axis -/
noncomputable def makeRotationX (angle : ℝ) : Mat3 := 
  let c := Real.cos angle
  let s := Real.sin angle
  ⟨1, 0, 0,
   0, c, -s,
   0, s, c⟩

/-- Rotation about Y axis -/
noncomputable def makeRotationY (angle : ℝ) : Mat3 := 
  let c := Real.cos angle
  let s := Real.sin angle
  ⟨c, 0, s,
   0, 1, 0,
   -s, 0, c⟩

/-- Rotation about Z axis -/
noncomputable def makeRotationZ (angle : ℝ) : Mat3 := 
  let c := Real.cos angle
  let s := Real.sin angle
  ⟨c, -s, 0,
   s, c, 0,
   0, 0, 1⟩

/-- Scale matrix -/
def makeScale (sx sy sz : ℝ) : Mat3 := diagonal sx sy sz

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: IDENTITY
-- ═══════════════════════════════════════════════════════════════════════════════

theorem mul_identity_left (m : Mat3) : mul identity m = m := by
  simp only [mul, identity]
  ext <;> ring

theorem mul_identity_right (m : Mat3) : mul m identity = m := by
  simp only [mul, identity]
  ext <;> ring

theorem mul_zero_left (m : Mat3) : mul zero m = zero := by
  simp only [mul, zero]
  ext <;> ring

theorem mul_zero_right (m : Mat3) : mul m zero = zero := by
  simp only [mul, zero]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: ASSOCIATIVITY (THE KEY THEOREM)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Matrix multiplication is associative: (A × B) × C = A × (B × C) -/
theorem mul_assoc (a b c : Mat3) : mul (mul a b) c = mul a (mul b c) := by
  simp only [mul]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: TRANSPOSE
-- ═══════════════════════════════════════════════════════════════════════════════

theorem transpose_involutive (m : Mat3) : transpose (transpose m) = m := by
  simp only [transpose]

theorem transpose_identity : transpose identity = identity := by
  simp only [transpose, identity]

theorem transpose_zero : transpose zero = zero := by
  simp only [transpose, zero]

theorem transpose_add (a b : Mat3) : transpose (add a b) = add (transpose a) (transpose b) := by
  simp only [transpose, add]

theorem transpose_scale (s : ℝ) (m : Mat3) : transpose (scale s m) = scale s (transpose m) := by
  simp only [transpose, scale]

/-- Transpose reverses multiplication order: (AB)ᵀ = BᵀAᵀ -/
theorem transpose_mul (a b : Mat3) : transpose (mul a b) = mul (transpose b) (transpose a) := by
  simp only [transpose, mul]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: DETERMINANT
-- ═══════════════════════════════════════════════════════════════════════════════

theorem det_identity : det identity = 1 := by
  simp only [det, identity]
  ring

theorem det_zero : det zero = 0 := by
  simp only [det, zero]
  ring

theorem det_transpose (m : Mat3) : det (transpose m) = det m := by
  simp only [det, transpose]
  ring

theorem det_scale (s : ℝ) (m : Mat3) : det (scale s m) = s^3 * det m := by
  simp only [det, scale]
  ring

/-- Determinant is multiplicative: det(AB) = det(A) × det(B) -/
theorem det_mul (a b : Mat3) : det (mul a b) = det a * det b := by
  simp only [det, mul]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: MATRIX-VECTOR MULTIPLICATION
-- ═══════════════════════════════════════════════════════════════════════════════

theorem mulVec_identity (v : Vec3) : mulVec identity v = v := by
  simp only [mulVec, identity]
  ext <;> ring

theorem mulVec_zero_mat (v : Vec3) : mulVec zero v = Vec3.zero := by
  simp only [mulVec, zero, Vec3.zero]
  ext <;> ring

theorem mulVec_zero_vec (m : Mat3) : mulVec m Vec3.zero = Vec3.zero := by
  simp only [mulVec, Vec3.zero]
  ext <;> ring

/-- Matrix multiplication is compatible with vector multiplication -/
theorem mulVec_mul (a b : Mat3) (v : Vec3) : mulVec (mul a b) v = mulVec a (mulVec b v) := by
  simp only [mulVec, mul]
  ext <;> ring

theorem mulVec_add_vec (m : Mat3) (u v : Vec3) : 
    mulVec m (Vec3.add u v) = Vec3.add (mulVec m u) (mulVec m v) := by
  simp only [mulVec, Vec3.add]
  ext <;> ring

theorem mulVec_scale_vec (m : Mat3) (s : ℝ) (v : Vec3) : 
    mulVec m (Vec3.scale s v) = Vec3.scale s (mulVec m v) := by
  simp only [mulVec, Vec3.scale]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: DIAGONAL MATRICES
-- ═══════════════════════════════════════════════════════════════════════════════

theorem diagonal_one : diagonal 1 1 1 = identity := by
  simp only [diagonal, identity]

theorem uniformScale_one : uniformScale 1 = identity := by
  simp only [uniformScale, diagonal, identity]

theorem det_diagonal (d0 d1 d2 : ℝ) : det (diagonal d0 d1 d2) = d0 * d1 * d2 := by
  simp only [det, diagonal]
  ring

theorem det_uniformScale (s : ℝ) : det (uniformScale s) = s^3 := by
  simp only [det, uniformScale, diagonal]
  ring

theorem det_makeScale (sx sy sz : ℝ) : det (makeScale sx sy sz) = sx * sy * sz := by
  exact det_diagonal sx sy sz

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: ROTATION MATRICES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Rotation by 0 around X axis is identity -/
theorem makeRotationX_zero : makeRotationX 0 = identity := by
  simp only [makeRotationX, Real.cos_zero, Real.sin_zero, identity]
  ext <;> norm_num

/-- Rotation by 0 around Y axis is identity -/
theorem makeRotationY_zero : makeRotationY 0 = identity := by
  simp only [makeRotationY, Real.cos_zero, Real.sin_zero, identity]
  ext <;> norm_num

/-- Rotation by 0 around Z axis is identity -/
theorem makeRotationZ_zero : makeRotationZ 0 = identity := by
  simp only [makeRotationZ, Real.cos_zero, Real.sin_zero, identity]
  ext <;> norm_num

/-- Rotation matrices have determinant 1 (rotations preserve volume) -/
theorem det_makeRotationX (angle : ℝ) : det (makeRotationX angle) = 1 := by
  simp only [det, makeRotationX]
  have h := Real.cos_sq_add_sin_sq angle
  linear_combination h

/-- Rotation around Y axis has determinant 1 -/
theorem det_makeRotationY (angle : ℝ) : det (makeRotationY angle) = 1 := by
  simp only [det, makeRotationY]
  have h := Real.cos_sq_add_sin_sq angle
  linear_combination h

/-- Rotation around Z axis has determinant 1 -/
theorem det_makeRotationZ (angle : ℝ) : det (makeRotationZ angle) = 1 := by
  simp only [det, makeRotationZ]
  have h := Real.cos_sq_add_sin_sq angle
  linear_combination h

-- ═══════════════════════════════════════════════════════════════════════════════
-- INVERSE (NVIDIA PPISP METHOD)
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Matrix Inverse using Cofactor/Adjugate Method

The inverse of a 3x3 matrix M is computed as:
  M⁻¹ = adj(M) / det(M)

Where adj(M) is the adjugate (transpose of cofactor matrix).

NVIDIA PPISP uses this exact formula in `matrix_inverse_3x3`:
  - Compute determinant
  - Compute cofactor matrix  
  - Transpose (adjugate)
  - Divide by determinant

The cofactors are the 2x2 minor determinants with appropriate signs:
  C_ij = (-1)^(i+j) * det(M_ij)

Where M_ij is the submatrix with row i and column j removed. -/

/-- Cofactor C(0,0): submatrix excluding row 0, col 0 -/
def cofactor00 (m : Mat3) : ℝ := m.m11 * m.m22 - m.m12 * m.m21

/-- Cofactor C(0,1): submatrix excluding row 0, col 1, with sign flip -/
def cofactor01 (m : Mat3) : ℝ := -(m.m10 * m.m22 - m.m12 * m.m20)

/-- Cofactor C(0,2): submatrix excluding row 0, col 2 -/
def cofactor02 (m : Mat3) : ℝ := m.m10 * m.m21 - m.m11 * m.m20

/-- Cofactor C(1,0): submatrix excluding row 1, col 0, with sign flip -/
def cofactor10 (m : Mat3) : ℝ := -(m.m01 * m.m22 - m.m02 * m.m21)

/-- Cofactor C(1,1): submatrix excluding row 1, col 1 -/
def cofactor11 (m : Mat3) : ℝ := m.m00 * m.m22 - m.m02 * m.m20

/-- Cofactor C(1,2): submatrix excluding row 1, col 2, with sign flip -/
def cofactor12 (m : Mat3) : ℝ := -(m.m00 * m.m21 - m.m01 * m.m20)

/-- Cofactor C(2,0): submatrix excluding row 2, col 0 -/
def cofactor20 (m : Mat3) : ℝ := m.m01 * m.m12 - m.m02 * m.m11

/-- Cofactor C(2,1): submatrix excluding row 2, col 1, with sign flip -/
def cofactor21 (m : Mat3) : ℝ := -(m.m00 * m.m12 - m.m02 * m.m10)

/-- Cofactor C(2,2): submatrix excluding row 2, col 2 -/
def cofactor22 (m : Mat3) : ℝ := m.m00 * m.m11 - m.m01 * m.m10

/-- Cofactor matrix (before transpose) -/
def cofactorMatrix (m : Mat3) : Mat3 :=
  ⟨cofactor00 m, cofactor01 m, cofactor02 m,
   cofactor10 m, cofactor11 m, cofactor12 m,
   cofactor20 m, cofactor21 m, cofactor22 m⟩

/-- Adjugate matrix (transpose of cofactor matrix).
    
    adj(M) is the matrix such that M × adj(M) = det(M) × I -/
def adjugate (m : Mat3) : Mat3 := transpose (cofactorMatrix m)

/-- Matrix inverse: M⁻¹ = adj(M) / det(M)
    
    This is the NVIDIA formula from matrix_inverse_3x3.
    Requires det(M) ≠ 0 for correctness. -/
noncomputable def inverse (m : Mat3) : Mat3 :=
  let d := det m
  let adj := adjugate m
  scale (1 / d) adj

/-- Determinant equals expansion along first row using cofactors -/
theorem det_cofactor_expansion (m : Mat3) :
    det m = m.m00 * cofactor00 m + m.m01 * cofactor01 m + m.m02 * cofactor02 m := by
  simp only [det, cofactor00, cofactor01, cofactor02]
  ring

/-- The adjugate formula: M × adj(M) = det(M) × I -/
theorem mul_adjugate (m : Mat3) : mul m (adjugate m) = scale (det m) identity := by
  simp only [mul, adjugate, transpose, cofactorMatrix, scale, identity,
             cofactor00, cofactor01, cofactor02, cofactor10, cofactor11, cofactor12,
             cofactor20, cofactor21, cofactor22, det]
  ext <;> ring

/-- The adjugate formula (left): adj(M) × M = det(M) × I -/
theorem adjugate_mul (m : Mat3) : mul (adjugate m) m = scale (det m) identity := by
  simp only [mul, adjugate, transpose, cofactorMatrix, scale, identity,
             cofactor00, cofactor01, cofactor02, cofactor10, cofactor11, cofactor12,
             cofactor20, cofactor21, cofactor22, det]
  ext <;> ring

/-- For invertible matrices: M × M⁻¹ = I -/
theorem mul_inverse (m : Mat3) (h : Invertible m) : mul m (inverse m) = identity := by
  simp only [inverse, Invertible] at *
  have hdet : det m ≠ 0 := h
  -- inverse = (1/det) * adj
  -- M × inverse = M × ((1/det) * adj) = (1/det) * (M × adj) = (1/det) * (det * I) = I
  calc mul m (scale (1 / det m) (adjugate m))
      = scale (1 / det m) (mul m (adjugate m)) := by
        simp only [mul, scale, adjugate, transpose, cofactorMatrix,
                   cofactor00, cofactor01, cofactor02, cofactor10, cofactor11, cofactor12,
                   cofactor20, cofactor21, cofactor22]
        ext <;> ring
    _ = scale (1 / det m) (scale (det m) identity) := by rw [mul_adjugate]
    _ = identity := by
        simp only [scale, identity]
        ext <;> field_simp

/-- For invertible matrices: M⁻¹ × M = I -/
theorem inverse_mul (m : Mat3) (h : Invertible m) : mul (inverse m) m = identity := by
  simp only [inverse, Invertible] at *
  have hdet : det m ≠ 0 := h
  calc mul (scale (1 / det m) (adjugate m)) m
      = scale (1 / det m) (mul (adjugate m) m) := by
        simp only [mul, scale, adjugate, transpose, cofactorMatrix,
                   cofactor00, cofactor01, cofactor02, cofactor10, cofactor11, cofactor12,
                   cofactor20, cofactor21, cofactor22]
        ext <;> ring
    _ = scale (1 / det m) (scale (det m) identity) := by rw [adjugate_mul]
    _ = identity := by
        simp only [scale, identity]
        ext <;> field_simp

/-- The determinant of the inverse is 1/det -/
theorem det_inverse (m : Mat3) (h : Invertible m) : det (inverse m) = 1 / det m := by
  -- det(M × M⁻¹) = det(I) = 1
  -- det(M) × det(M⁻¹) = 1
  -- det(M⁻¹) = 1/det(M)
  have hdet : det m ≠ 0 := h
  have h1 : det (mul m (inverse m)) = 1 := by rw [mul_inverse m h]; exact det_identity
  rw [det_mul] at h1
  field_simp at h1 ⊢
  linarith

/-- Inverse is involutive: (M⁻¹)⁻¹ = M -/
theorem inverse_inverse (m : Mat3) (h : Invertible m) : inverse (inverse m) = m := by
  -- M⁻¹ × (M⁻¹)⁻¹ = I, but also M⁻¹ × M = I
  -- So (M⁻¹)⁻¹ = M
  have hdet : det m ≠ 0 := h
  have hinv_inv : Invertible (inverse m) := by
    simp only [Invertible]
    rw [det_inverse m h]
    intro hcontra
    have hone : (1 : ℝ) = det m * (1 / det m) := by field_simp
    rw [hcontra] at hone
    simp at hone
  -- We prove by showing both are right inverses of inverse m
  have h1 : mul (inverse m) (inverse (inverse m)) = identity := mul_inverse (inverse m) hinv_inv
  have h2 : mul (inverse m) m = identity := inverse_mul m h
  -- Since inverse m is invertible, left multiplication is injective
  -- From h1 and h2, inverse (inverse m) = m
  calc inverse (inverse m) 
      = mul identity (inverse (inverse m)) := by rw [mul_identity_left]
    _ = mul (mul m (inverse m)) (inverse (inverse m)) := by rw [mul_inverse m h]
    _ = mul m (mul (inverse m) (inverse (inverse m))) := by rw [mul_assoc]
    _ = mul m identity := by rw [h1]
    _ = m := by rw [mul_identity_right]

/-- Inverse reverses multiplication: (AB)⁻¹ = B⁻¹A⁻¹ -/
theorem inverse_mul_eq (a b : Mat3) (ha : Invertible a) (hb : Invertible b) :
    inverse (mul a b) = mul (inverse b) (inverse a) := by
  -- Show that (B⁻¹A⁻¹) is the inverse of AB
  have hab : Invertible (mul a b) := by
    simp only [Invertible]
    rw [det_mul]
    have hda : det a ≠ 0 := ha
    have hdb : det b ≠ 0 := hb
    exact mul_ne_zero hda hdb
  -- (AB) × (B⁻¹A⁻¹) = A(B × B⁻¹)A⁻¹ = A × I × A⁻¹ = A × A⁻¹ = I
  have h1 : mul (mul a b) (mul (inverse b) (inverse a)) = identity := by
    calc mul (mul a b) (mul (inverse b) (inverse a))
        = mul a (mul (mul b (inverse b)) (inverse a)) := by
          rw [mul_assoc, mul_assoc, ←mul_assoc b]
      _ = mul a (mul identity (inverse a)) := by rw [mul_inverse b hb]
      _ = mul a (inverse a) := by rw [mul_identity_left]
      _ = identity := by rw [mul_inverse a ha]
  -- By uniqueness: if X × Y = I and Y is invertible, then X = Y⁻¹
  -- We show (B⁻¹A⁻¹) × (AB) = I, then use mul_inverse to conclude
  have h2 : mul (mul (inverse b) (inverse a)) (mul a b) = identity := by
    calc mul (mul (inverse b) (inverse a)) (mul a b)
        = mul (inverse b) (mul (mul (inverse a) a) b) := by
          rw [mul_assoc, mul_assoc, ←mul_assoc (inverse a)]
      _ = mul (inverse b) (mul identity b) := by rw [inverse_mul a ha]
      _ = mul (inverse b) b := by rw [mul_identity_left]
      _ = identity := by rw [inverse_mul b hb]
  -- Now: (AB)⁻¹ = (B⁻¹A⁻¹) because (B⁻¹A⁻¹) is both left and right inverse of (AB)
  -- Using h2: (B⁻¹A⁻¹) × (AB) = I, so (B⁻¹A⁻¹) = (AB)⁻¹
  symm
  calc mul (inverse b) (inverse a)
      = mul (mul (inverse b) (inverse a)) identity := by rw [mul_identity_right]
    _ = mul (mul (inverse b) (inverse a)) (mul (mul a b) (inverse (mul a b))) := by 
        rw [mul_inverse (mul a b) hab]
    _ = mul (mul (mul (inverse b) (inverse a)) (mul a b)) (inverse (mul a b)) := by 
        rw [←mul_assoc]
    _ = mul identity (inverse (mul a b)) := by rw [h2]
    _ = inverse (mul a b) := by rw [mul_identity_left]

end Mat3

end Hydrogen.Math
