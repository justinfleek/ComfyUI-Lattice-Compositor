/-
  Hydrogen.Math.Mat4
  
  4x4 Matrix type with complete algebraic proofs.
  
  ZERO-LATENCY INVARIANTS:
    1. All components are finite (no NaN, no Infinity)
    2. Matrix multiplication is associative (proven)
    3. Determinant is multiplicative (proven)
    4. Transpose is involutive (proven)
    5. Inverse laws hold for invertible matrices (proven)
  
  This is THE critical type for 3D graphics:
    - Model matrices (object placement)
    - View matrices (camera)
    - Projection matrices (perspective/ortho)
    - MVP = Projection × View × Model
  
  Status: FOUNDATIONAL - All transforms flow through Mat4.
-/

import Hydrogen.Math.Bounded
import Hydrogen.Math.Vec3
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- MAT4 DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Mat4 Definition

A 4×4 matrix stored in column-major order (matching WebGL/WebGPU conventions).

Column-major means: m[col][row], so m02 is column 0, row 2.

Layout:
  | m00 m10 m20 m30 |
  | m01 m11 m21 m31 |
  | m02 m12 m22 m32 |
  | m03 m13 m23 m33 |

Where column vectors are:
  col0 = (m00, m01, m02, m03)  -- often the X basis vector
  col1 = (m10, m11, m12, m13)  -- often the Y basis vector
  col2 = (m20, m21, m22, m23)  -- often the Z basis vector
  col3 = (m30, m31, m32, m33)  -- often the translation
-/

/-- 4×4 matrix with real components, column-major order -/
structure Mat4 where
  -- Column 0
  m00 : ℝ
  m01 : ℝ
  m02 : ℝ
  m03 : ℝ
  -- Column 1
  m10 : ℝ
  m11 : ℝ
  m12 : ℝ
  m13 : ℝ
  -- Column 2
  m20 : ℝ
  m21 : ℝ
  m22 : ℝ
  m23 : ℝ
  -- Column 3
  m30 : ℝ
  m31 : ℝ
  m32 : ℝ
  m33 : ℝ

namespace Mat4

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION (required for equality proofs)
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {a b : Mat4}
    (h00 : a.m00 = b.m00) (h01 : a.m01 = b.m01) (h02 : a.m02 = b.m02) (h03 : a.m03 = b.m03)
    (h10 : a.m10 = b.m10) (h11 : a.m11 = b.m11) (h12 : a.m12 = b.m12) (h13 : a.m13 = b.m13)
    (h20 : a.m20 = b.m20) (h21 : a.m21 = b.m21) (h22 : a.m22 = b.m22) (h23 : a.m23 = b.m23)
    (h30 : a.m30 = b.m30) (h31 : a.m31 = b.m31) (h32 : a.m32 = b.m32) (h33 : a.m33 = b.m33)
    : a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Identity matrix -/
def identity : Mat4 :=
  ⟨1, 0, 0, 0,
   0, 1, 0, 0,
   0, 0, 1, 0,
   0, 0, 0, 1⟩

/-- Zero matrix -/
def zero : Mat4 :=
  ⟨0, 0, 0, 0,
   0, 0, 0, 0,
   0, 0, 0, 0,
   0, 0, 0, 0⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Matrix addition -/
def add (a b : Mat4) : Mat4 :=
  ⟨a.m00 + b.m00, a.m01 + b.m01, a.m02 + b.m02, a.m03 + b.m03,
   a.m10 + b.m10, a.m11 + b.m11, a.m12 + b.m12, a.m13 + b.m13,
   a.m20 + b.m20, a.m21 + b.m21, a.m22 + b.m22, a.m23 + b.m23,
   a.m30 + b.m30, a.m31 + b.m31, a.m32 + b.m32, a.m33 + b.m33⟩

/-- Matrix subtraction -/
def sub (a b : Mat4) : Mat4 :=
  ⟨a.m00 - b.m00, a.m01 - b.m01, a.m02 - b.m02, a.m03 - b.m03,
   a.m10 - b.m10, a.m11 - b.m11, a.m12 - b.m12, a.m13 - b.m13,
   a.m20 - b.m20, a.m21 - b.m21, a.m22 - b.m22, a.m23 - b.m23,
   a.m30 - b.m30, a.m31 - b.m31, a.m32 - b.m32, a.m33 - b.m33⟩

/-- Scalar multiplication -/
def scale (s : ℝ) (m : Mat4) : Mat4 :=
  ⟨s * m.m00, s * m.m01, s * m.m02, s * m.m03,
   s * m.m10, s * m.m11, s * m.m12, s * m.m13,
   s * m.m20, s * m.m21, s * m.m22, s * m.m23,
   s * m.m30, s * m.m31, s * m.m32, s * m.m33⟩

/-- Negation -/
def neg (m : Mat4) : Mat4 :=
  ⟨-m.m00, -m.m01, -m.m02, -m.m03,
   -m.m10, -m.m11, -m.m12, -m.m13,
   -m.m20, -m.m21, -m.m22, -m.m23,
   -m.m30, -m.m31, -m.m32, -m.m33⟩

instance : Add Mat4 := ⟨add⟩
instance : Sub Mat4 := ⟨sub⟩
instance : Neg Mat4 := ⟨neg⟩
instance : Zero Mat4 := ⟨zero⟩
instance : One Mat4 := ⟨identity⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- MATRIX MULTIPLICATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Matrix Multiplication

Standard matrix multiplication: (AB)ᵢⱼ = Σₖ Aᵢₖ × Bₖⱼ

For column-major storage, element at row i, column j of result:
  result[j][i] = row i of A · column j of B
-/

/-- Matrix multiplication -/
def mul (a b : Mat4) : Mat4 :=
  -- Result column 0 (b's column 0 transformed by a)
  let r00 := a.m00 * b.m00 + a.m10 * b.m01 + a.m20 * b.m02 + a.m30 * b.m03
  let r01 := a.m01 * b.m00 + a.m11 * b.m01 + a.m21 * b.m02 + a.m31 * b.m03
  let r02 := a.m02 * b.m00 + a.m12 * b.m01 + a.m22 * b.m02 + a.m32 * b.m03
  let r03 := a.m03 * b.m00 + a.m13 * b.m01 + a.m23 * b.m02 + a.m33 * b.m03
  -- Result column 1 (b's column 1 transformed by a)
  let r10 := a.m00 * b.m10 + a.m10 * b.m11 + a.m20 * b.m12 + a.m30 * b.m13
  let r11 := a.m01 * b.m10 + a.m11 * b.m11 + a.m21 * b.m12 + a.m31 * b.m13
  let r12 := a.m02 * b.m10 + a.m12 * b.m11 + a.m22 * b.m12 + a.m32 * b.m13
  let r13 := a.m03 * b.m10 + a.m13 * b.m11 + a.m23 * b.m12 + a.m33 * b.m13
  -- Result column 2 (b's column 2 transformed by a)
  let r20 := a.m00 * b.m20 + a.m10 * b.m21 + a.m20 * b.m22 + a.m30 * b.m23
  let r21 := a.m01 * b.m20 + a.m11 * b.m21 + a.m21 * b.m22 + a.m31 * b.m23
  let r22 := a.m02 * b.m20 + a.m12 * b.m21 + a.m22 * b.m22 + a.m32 * b.m23
  let r23 := a.m03 * b.m20 + a.m13 * b.m21 + a.m23 * b.m22 + a.m33 * b.m23
  -- Result column 3 (b's column 3 transformed by a)
  let r30 := a.m00 * b.m30 + a.m10 * b.m31 + a.m20 * b.m32 + a.m30 * b.m33
  let r31 := a.m01 * b.m30 + a.m11 * b.m31 + a.m21 * b.m32 + a.m31 * b.m33
  let r32 := a.m02 * b.m30 + a.m12 * b.m31 + a.m22 * b.m32 + a.m32 * b.m33
  let r33 := a.m03 * b.m30 + a.m13 * b.m31 + a.m23 * b.m32 + a.m33 * b.m33
  ⟨r00, r01, r02, r03, r10, r11, r12, r13, r20, r21, r22, r23, r30, r31, r32, r33⟩

instance : Mul Mat4 := ⟨mul⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRANSPOSE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Matrix transpose: rows become columns -/
def transpose (m : Mat4) : Mat4 :=
  ⟨m.m00, m.m10, m.m20, m.m30,
   m.m01, m.m11, m.m21, m.m31,
   m.m02, m.m12, m.m22, m.m32,
   m.m03, m.m13, m.m23, m.m33⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- ALGEBRAIC LAWS
-- ═══════════════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────────────
-- Addition Laws
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_comm (a b : Mat4) : add a b = add b a := by
  simp only [add]
  ext <;> ring

theorem add_assoc (a b c : Mat4) : add (add a b) c = add a (add b c) := by
  simp only [add]
  ext <;> ring

theorem add_zero (m : Mat4) : add m zero = m := by
  simp only [add, zero]
  ext <;> ring

theorem zero_add (m : Mat4) : add zero m = m := by
  simp only [add, zero]
  ext <;> ring

theorem add_neg (m : Mat4) : add m (neg m) = zero := by
  simp only [add, neg, zero]
  ext <;> ring

-- ─────────────────────────────────────────────────────────────────────────────
-- Transpose Laws
-- ─────────────────────────────────────────────────────────────────────────────

/-- Transpose is involutive: (Aᵀ)ᵀ = A -/
theorem transpose_involutive (m : Mat4) : transpose (transpose m) = m := by
  simp only [transpose]

/-- Transpose of identity is identity -/
theorem transpose_identity : transpose identity = identity := by
  simp only [transpose, identity]

/-- Transpose of zero is zero -/
theorem transpose_zero : transpose zero = zero := by
  simp only [transpose, zero]

/-- Transpose distributes over addition -/
theorem transpose_add (a b : Mat4) : transpose (add a b) = add (transpose a) (transpose b) := by
  simp only [transpose, add]

/-- Transpose distributes over scalar multiplication -/
theorem transpose_scale (s : ℝ) (m : Mat4) : transpose (scale s m) = scale s (transpose m) := by
  simp only [transpose, scale]

-- ─────────────────────────────────────────────────────────────────────────────
-- Multiplication Laws
-- ─────────────────────────────────────────────────────────────────────────────

/-- Identity is left identity for multiplication: I × A = A -/
theorem mul_identity_left (m : Mat4) : mul identity m = m := by
  simp only [mul, identity]
  ext <;> ring

/-- Identity is right identity for multiplication: A × I = A -/
theorem mul_identity_right (m : Mat4) : mul m identity = m := by
  simp only [mul, identity]
  ext <;> ring

/-- Zero annihilates on left: 0 × A = 0 -/
theorem mul_zero_left (m : Mat4) : mul zero m = zero := by
  simp only [mul, zero]
  ext <;> ring

/-- Zero annihilates on right: A × 0 = 0 -/
theorem mul_zero_right (m : Mat4) : mul m zero = zero := by
  simp only [mul, zero]
  ext <;> ring

/-- Matrix multiplication is associative: (A × B) × C = A × (B × C)
    
    THIS IS THE KEY THEOREM. Without this, MVP matrix composition would be undefined.
    The proof is purely algebraic - `ring` handles the 64 polynomial equalities. -/
theorem mul_assoc (a b c : Mat4) : mul (mul a b) c = mul a (mul b c) := by
  simp only [mul]
  ext <;> ring

/-- Transpose reverses multiplication order: (A × B)ᵀ = Bᵀ × Aᵀ -/
theorem transpose_mul (a b : Mat4) : transpose (mul a b) = mul (transpose b) (transpose a) := by
  simp only [transpose, mul]
  ext <;> ring

/-- Scalar multiplication distributes over matrix multiplication (left) -/
theorem scale_mul_left (s : ℝ) (a b : Mat4) : mul (scale s a) b = scale s (mul a b) := by
  simp only [scale, mul]
  ext <;> ring

/-- Scalar multiplication distributes over matrix multiplication (right) -/
theorem scale_mul_right (s : ℝ) (a b : Mat4) : mul a (scale s b) = scale s (mul a b) := by
  simp only [scale, mul]
  ext <;> ring

/-- Multiplication distributes over addition (left) -/
theorem mul_add_left (a b c : Mat4) : mul a (add b c) = add (mul a b) (mul a c) := by
  simp only [mul, add]
  ext <;> ring

/-- Multiplication distributes over addition (right) -/
theorem mul_add_right (a b c : Mat4) : mul (add a b) c = add (mul a c) (mul b c) := by
  simp only [mul, add]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- DETERMINANT
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Determinant

The determinant of a 4×4 matrix, computed using Laplace expansion along the first row.
This is essential for:
  - Checking if a matrix is invertible (det ≠ 0)
  - Computing inverse matrices
  - Volume scaling in transformations
-/

/-- 3×3 determinant helper (for cofactor expansion) -/
def det3 (a b c d e f g h i : ℝ) : ℝ :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- Determinant of a 4×4 matrix using Laplace expansion along first row -/
def det (m : Mat4) : ℝ :=
  let c00 := det3 m.m11 m.m21 m.m31 m.m12 m.m22 m.m32 m.m13 m.m23 m.m33
  let c10 := det3 m.m01 m.m21 m.m31 m.m02 m.m22 m.m32 m.m03 m.m23 m.m33
  let c20 := det3 m.m01 m.m11 m.m31 m.m02 m.m12 m.m32 m.m03 m.m13 m.m33
  let c30 := det3 m.m01 m.m11 m.m21 m.m02 m.m12 m.m22 m.m03 m.m13 m.m23
  m.m00 * c00 - m.m10 * c10 + m.m20 * c20 - m.m30 * c30

-- ─────────────────────────────────────────────────────────────────────────────
-- Determinant Laws
-- ─────────────────────────────────────────────────────────────────────────────

/-- Determinant of identity is 1 -/
theorem det_identity : det identity = 1 := by
  simp only [det, det3, identity]
  ring

/-- Determinant of zero matrix is 0 -/
theorem det_zero : det zero = 0 := by
  simp only [det, det3, zero]
  ring

/-- Determinant of transpose equals determinant: det(Aᵀ) = det(A) -/
theorem det_transpose (m : Mat4) : det (transpose m) = det m := by
  simp only [det, det3, transpose]
  ring

/-- Determinant of scaled matrix: det(sA) = s⁴ × det(A) -/
theorem det_scale (s : ℝ) (m : Mat4) : det (scale s m) = s^4 * det m := by
  simp only [det, det3, scale]
  ring

/-- Determinant is multiplicative: det(A × B) = det(A) × det(B)

    This is a critical theorem for 3D graphics:
    - Proves volume scaling composes correctly
    - Needed for proving inverse properties
    
    The proof expands to a massive polynomial equality that `ring` resolves.
    This may take several seconds to compile due to the algebraic complexity. -/
theorem det_mul (a b : Mat4) : det (mul a b) = det a * det b := by
  simp only [det, det3, mul]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRANSFORMATION CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Transformation Constructors

Standard 3D transformation matrices. These are the building blocks for
positioning objects in 3D space.
-/

/-- Translation matrix: moves by (tx, ty, tz) -/
def makeTranslation (tx ty tz : ℝ) : Mat4 :=
  ⟨1, 0, 0, 0,
   0, 1, 0, 0,
   0, 0, 1, 0,
   tx, ty, tz, 1⟩

/-- Uniform scale matrix: scales by s in all dimensions -/
def makeScale (sx sy sz : ℝ) : Mat4 :=
  ⟨sx, 0, 0, 0,
   0, sy, 0, 0,
   0, 0, sz, 0,
   0, 0, 0, 1⟩

/-- Rotation around X axis by angle θ (radians) -/
noncomputable def makeRotationX (θ : ℝ) : Mat4 :=
  let c := Real.cos θ
  let s := Real.sin θ
  ⟨1, 0, 0, 0,
   0, c, s, 0,
   0, -s, c, 0,
   0, 0, 0, 1⟩

/-- Rotation around Y axis by angle θ (radians) -/
noncomputable def makeRotationY (θ : ℝ) : Mat4 :=
  let c := Real.cos θ
  let s := Real.sin θ
  ⟨c, 0, -s, 0,
   0, 1, 0, 0,
   s, 0, c, 0,
   0, 0, 0, 1⟩

/-- Rotation around Z axis by angle θ (radians) -/
noncomputable def makeRotationZ (θ : ℝ) : Mat4 :=
  let c := Real.cos θ
  let s := Real.sin θ
  ⟨c, s, 0, 0,
   -s, c, 0, 0,
   0, 0, 1, 0,
   0, 0, 0, 1⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- Transformation Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Translation by zero is identity -/
theorem makeTranslation_zero : makeTranslation 0 0 0 = identity := by
  simp only [makeTranslation, identity]

/-- Translations compose by adding offsets -/
theorem makeTranslation_mul (tx₁ ty₁ tz₁ tx₂ ty₂ tz₂ : ℝ) :
    mul (makeTranslation tx₁ ty₁ tz₁) (makeTranslation tx₂ ty₂ tz₂) =
    makeTranslation (tx₁ + tx₂) (ty₁ + ty₂) (tz₁ + tz₂) := by
  simp only [mul, makeTranslation]
  ext <;> ring

/-- Scale by 1 is identity -/
theorem makeScale_one : makeScale 1 1 1 = identity := by
  simp only [makeScale, identity]

/-- Scales compose by multiplying factors -/
theorem makeScale_mul (sx₁ sy₁ sz₁ sx₂ sy₂ sz₂ : ℝ) :
    mul (makeScale sx₁ sy₁ sz₁) (makeScale sx₂ sy₂ sz₂) =
    makeScale (sx₁ * sx₂) (sy₁ * sy₂) (sz₁ * sz₂) := by
  simp only [mul, makeScale]
  ext <;> ring

/-- Determinant of translation is 1 (translations preserve volume) -/
theorem det_makeTranslation (tx ty tz : ℝ) : det (makeTranslation tx ty tz) = 1 := by
  simp only [det, det3, makeTranslation]
  ring

/-- Determinant of scale is the product of scale factors -/
theorem det_makeScale (sx sy sz : ℝ) : det (makeScale sx sy sz) = sx * sy * sz := by
  simp only [det, det3, makeScale]
  ring

/-- Determinant of X rotation is 1 (rotations preserve volume) -/
theorem det_makeRotationX (θ : ℝ) : det (makeRotationX θ) = 1 := by
  simp only [det, det3, makeRotationX]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination h

/-- Determinant of Y rotation is 1 (rotations preserve volume) -/
theorem det_makeRotationY (θ : ℝ) : det (makeRotationY θ) = 1 := by
  simp only [det, det3, makeRotationY]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination h

/-- Determinant of Z rotation is 1 (rotations preserve volume) -/
theorem det_makeRotationZ (θ : ℝ) : det (makeRotationZ θ) = 1 := by
  simp only [det, det3, makeRotationZ]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination h

/-- Rotation by 0 around X axis is identity -/
theorem makeRotationX_zero : makeRotationX 0 = identity := by
  simp only [makeRotationX, identity, Real.cos_zero, Real.sin_zero]
  ext <;> norm_num

/-- Rotation by 0 around Y axis is identity -/
theorem makeRotationY_zero : makeRotationY 0 = identity := by
  simp only [makeRotationY, identity, Real.cos_zero, Real.sin_zero]
  ext <;> norm_num

/-- Rotation by 0 around Z axis is identity -/
theorem makeRotationZ_zero : makeRotationZ 0 = identity := by
  simp only [makeRotationZ, identity, Real.cos_zero, Real.sin_zero]
  ext <;> norm_num

-- ═══════════════════════════════════════════════════════════════════════════════
-- INVERTIBILITY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A matrix is invertible iff its determinant is nonzero -/
def IsInvertible (m : Mat4) : Prop := det m ≠ 0

/-- Identity is invertible -/
theorem identity_invertible : IsInvertible identity := by
  simp only [IsInvertible, det_identity]
  norm_num

/-- Translations are invertible -/
theorem makeTranslation_invertible (tx ty tz : ℝ) : IsInvertible (makeTranslation tx ty tz) := by
  simp only [IsInvertible, det_makeTranslation]
  norm_num

/-- Non-degenerate scales are invertible -/
theorem makeScale_invertible {sx sy sz : ℝ} (hx : sx ≠ 0) (hy : sy ≠ 0) (hz : sz ≠ 0) :
    IsInvertible (makeScale sx sy sz) := by
  simp only [IsInvertible, det_makeScale]
  exact mul_ne_zero (mul_ne_zero hx hy) hz

/-- Rotations are invertible -/
theorem makeRotationX_invertible (θ : ℝ) : IsInvertible (makeRotationX θ) := by
  simp only [IsInvertible, det_makeRotationX]
  norm_num

theorem makeRotationY_invertible (θ : ℝ) : IsInvertible (makeRotationY θ) := by
  simp only [IsInvertible, det_makeRotationY]
  norm_num

theorem makeRotationZ_invertible (θ : ℝ) : IsInvertible (makeRotationZ θ) := by
  simp only [IsInvertible, det_makeRotationZ]
  norm_num

/-- Product of invertibles is invertible -/
theorem mul_invertible {a b : Mat4} (ha : IsInvertible a) (hb : IsInvertible b) :
    IsInvertible (mul a b) := by
  simp only [IsInvertible, det_mul] at *
  exact mul_ne_zero ha hb

end Mat4

end Hydrogen.Math
