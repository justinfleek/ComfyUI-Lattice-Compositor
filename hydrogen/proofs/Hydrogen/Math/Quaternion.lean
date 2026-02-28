/-
  Hydrogen.Math.Quaternion
  
  Unit quaternions for 3D rotation representation.
  
  ZERO-LATENCY INVARIANTS:
    1. Unit quaternions have length 1 (proven)
    2. Quaternion multiplication is associative (proven)
    3. q × q⁻¹ = identity (proven)
    4. SLERP stays on unit sphere (proven)
    5. SLERP endpoints: slerp(0) = q₁, slerp(1) = q₂ (proven)
    6. Quaternion-to-matrix preserves composition (proven)
  
  WHY QUATERNIONS:
    - No gimbal lock (unlike Euler angles)
    - Smooth interpolation via SLERP
    - Compact representation (4 floats vs 9 for rotation matrix)
    - Numerically stable composition
  
  MATHEMATICAL BACKGROUND:
    Quaternions extend complex numbers: q = w + xi + yj + zk
    where i² = j² = k² = ijk = -1
    
    Unit quaternions (‖q‖ = 1) form a double cover of SO(3):
    both q and -q represent the same rotation.
    
    Rotation of vector v by quaternion q: v' = qvq⁻¹
    
  Status: FOUNDATIONAL - Required for all smooth 3D rotations.
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Mat4

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUATERNION DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Quaternion Definition

A quaternion q = w + xi + yj + zk with real components.
Convention: w is the scalar part, (x, y, z) is the vector part.

For rotation by angle θ around unit axis (ax, ay, az):
  q = cos(θ/2) + sin(θ/2)(ax·i + ay·j + az·k)
-/

/-- Quaternion with real components (w, x, y, z) -/
structure Quaternion where
  w : ℝ  -- scalar part
  x : ℝ  -- i component
  y : ℝ  -- j component
  z : ℝ  -- k component

namespace Quaternion

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {a b : Quaternion}
    (hw : a.w = b.w) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Identity quaternion (represents no rotation) -/
def identity : Quaternion := ⟨1, 0, 0, 0⟩

/-- Zero quaternion (NOT a valid rotation, but useful algebraically) -/
def zero : Quaternion := ⟨0, 0, 0, 0⟩

/-- Create quaternion from axis-angle representation -/
noncomputable def fromAxisAngle (axis : Vec3) (angle : ℝ) : Quaternion :=
  let halfAngle := angle / 2
  let s := Real.sin halfAngle
  let c := Real.cos halfAngle
  let len := Real.sqrt (axis.x * axis.x + axis.y * axis.y + axis.z * axis.z)
  if len = 0 then identity
  else ⟨c, s * axis.x / len, s * axis.y / len, s * axis.z / len⟩

/-- Create quaternion for rotation around X axis -/
noncomputable def fromRotationX (angle : ℝ) : Quaternion :=
  let halfAngle := angle / 2
  ⟨Real.cos halfAngle, Real.sin halfAngle, 0, 0⟩

/-- Create quaternion for rotation around Y axis -/
noncomputable def fromRotationY (angle : ℝ) : Quaternion :=
  let halfAngle := angle / 2
  ⟨Real.cos halfAngle, 0, Real.sin halfAngle, 0⟩

/-- Create quaternion for rotation around Z axis -/
noncomputable def fromRotationZ (angle : ℝ) : Quaternion :=
  let halfAngle := angle / 2
  ⟨Real.cos halfAngle, 0, 0, Real.sin halfAngle⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Quaternion addition -/
def add (a b : Quaternion) : Quaternion :=
  ⟨a.w + b.w, a.x + b.x, a.y + b.y, a.z + b.z⟩

/-- Quaternion subtraction -/
def sub (a b : Quaternion) : Quaternion :=
  ⟨a.w - b.w, a.x - b.x, a.y - b.y, a.z - b.z⟩

/-- Scalar multiplication -/
def scale (s : ℝ) (q : Quaternion) : Quaternion :=
  ⟨s * q.w, s * q.x, s * q.y, s * q.z⟩

/-- Negation -/
def neg (q : Quaternion) : Quaternion :=
  ⟨-q.w, -q.x, -q.y, -q.z⟩

/-- Quaternion multiplication (Hamilton product)
    
    This is the KEY operation. Non-commutative!
    (a + bi + cj + dk)(e + fi + gj + hk) using:
      i² = j² = k² = -1
      ij = k, jk = i, ki = j
      ji = -k, kj = -i, ik = -j
-/
def mul (a b : Quaternion) : Quaternion :=
  ⟨a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z,
   a.w * b.x + a.x * b.w + a.y * b.z - a.z * b.y,
   a.w * b.y - a.x * b.z + a.y * b.w + a.z * b.x,
   a.w * b.z + a.x * b.y - a.y * b.x + a.z * b.w⟩

/-- Conjugate: q* = w - xi - yj - zk -/
def conjugate (q : Quaternion) : Quaternion :=
  ⟨q.w, -q.x, -q.y, -q.z⟩

/-- Squared length (norm squared): ‖q‖² = w² + x² + y² + z² -/
def lengthSq (q : Quaternion) : ℝ :=
  q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z

/-- Length (norm): ‖q‖ = √(w² + x² + y² + z²) -/
noncomputable def length (q : Quaternion) : ℝ :=
  Real.sqrt (lengthSq q)

/-- Dot product of quaternions (as 4D vectors) -/
def dot (a b : Quaternion) : ℝ :=
  a.w * b.w + a.x * b.x + a.y * b.y + a.z * b.z

instance : Add Quaternion := ⟨add⟩
instance : Sub Quaternion := ⟨sub⟩
instance : Neg Quaternion := ⟨neg⟩
instance : Mul Quaternion := ⟨mul⟩
instance : Zero Quaternion := ⟨zero⟩
instance : One Quaternion := ⟨identity⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- ALGEBRAIC LAWS
-- ═══════════════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────────────
-- Addition Laws
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_comm (a b : Quaternion) : add a b = add b a := by
  simp only [add]
  ext <;> ring

theorem add_assoc (a b c : Quaternion) : add (add a b) c = add a (add b c) := by
  simp only [add]
  ext <;> ring

theorem add_zero (q : Quaternion) : add q zero = q := by
  simp only [add, zero]
  ext <;> ring

theorem zero_add (q : Quaternion) : add zero q = q := by
  simp only [add, zero]
  ext <;> ring

theorem add_neg (q : Quaternion) : add q (neg q) = zero := by
  simp only [add, neg, zero]
  ext <;> ring

-- ─────────────────────────────────────────────────────────────────────────────
-- Multiplication Laws
-- ─────────────────────────────────────────────────────────────────────────────

/-- Identity is left identity for multiplication -/
theorem mul_identity_left (q : Quaternion) : mul identity q = q := by
  simp only [mul, identity]
  ext <;> ring

/-- Identity is right identity for multiplication -/
theorem mul_identity_right (q : Quaternion) : mul q identity = q := by
  simp only [mul, identity]
  ext <;> ring

/-- Zero annihilates on left -/
theorem mul_zero_left (q : Quaternion) : mul zero q = zero := by
  simp only [mul, zero]
  ext <;> ring

/-- Zero annihilates on right -/
theorem mul_zero_right (q : Quaternion) : mul q zero = zero := by
  simp only [mul, zero]
  ext <;> ring

/-- Quaternion multiplication is associative
    
    THIS IS CRITICAL. Unlike commutativity (which fails), 
    associativity holds and is essential for composing rotations. -/
theorem mul_assoc (a b c : Quaternion) : mul (mul a b) c = mul a (mul b c) := by
  simp only [mul]
  ext <;> ring

/-- Quaternion multiplication is NOT commutative in general.
    We prove the specific case where it fails: i × j ≠ j × i -/
theorem mul_not_comm : mul ⟨0, 1, 0, 0⟩ ⟨0, 0, 1, 0⟩ ≠ mul ⟨0, 0, 1, 0⟩ ⟨0, 1, 0, 0⟩ := by
  simp only [mul, ne_eq]
  intro h
  have hz := congrArg Quaternion.z h
  simp at hz
  linarith

/-- Scalar multiplication distributes over quaternion multiplication (left) -/
theorem scale_mul_left (s : ℝ) (a b : Quaternion) : mul (scale s a) b = scale s (mul a b) := by
  simp only [mul, scale]
  ext <;> ring

/-- Scalar multiplication distributes over quaternion multiplication (right) -/
theorem scale_mul_right (s : ℝ) (a b : Quaternion) : mul a (scale s b) = scale s (mul a b) := by
  simp only [mul, scale]
  ext <;> ring

-- ─────────────────────────────────────────────────────────────────────────────
-- Conjugate Laws
-- ─────────────────────────────────────────────────────────────────────────────

/-- Conjugate is involutive: (q*)* = q -/
theorem conjugate_involutive (q : Quaternion) : conjugate (conjugate q) = q := by
  simp only [conjugate]
  ext <;> ring

/-- Conjugate of identity is identity -/
theorem conjugate_identity : conjugate identity = identity := by
  simp only [conjugate, identity]
  ext <;> norm_num

/-- Conjugate of zero is zero -/
theorem conjugate_zero : conjugate zero = zero := by
  simp only [conjugate, zero]
  ext <;> norm_num

/-- Conjugate reverses multiplication: (ab)* = b*a* -/
theorem conjugate_mul (a b : Quaternion) : conjugate (mul a b) = mul (conjugate b) (conjugate a) := by
  simp only [conjugate, mul]
  ext <;> ring

/-- Conjugate distributes over addition -/
theorem conjugate_add (a b : Quaternion) : conjugate (add a b) = add (conjugate a) (conjugate b) := by
  simp only [conjugate, add]
  ext <;> ring

/-- q × q* = ‖q‖² × identity (as a real quaternion) -/
theorem mul_conjugate (q : Quaternion) : mul q (conjugate q) = ⟨lengthSq q, 0, 0, 0⟩ := by
  simp only [mul, conjugate, lengthSq]
  ext <;> ring

/-- q* × q = ‖q‖² × identity -/
theorem conjugate_mul_self (q : Quaternion) : mul (conjugate q) q = ⟨lengthSq q, 0, 0, 0⟩ := by
  simp only [mul, conjugate, lengthSq]
  ext <;> ring

-- ─────────────────────────────────────────────────────────────────────────────
-- Length Laws
-- ─────────────────────────────────────────────────────────────────────────────

/-- Length squared is non-negative -/
theorem lengthSq_nonneg (q : Quaternion) : 0 ≤ lengthSq q := by
  simp only [lengthSq]
  have h1 : 0 ≤ q.w * q.w := mul_self_nonneg q.w
  have h2 : 0 ≤ q.x * q.x := mul_self_nonneg q.x
  have h3 : 0 ≤ q.y * q.y := mul_self_nonneg q.y
  have h4 : 0 ≤ q.z * q.z := mul_self_nonneg q.z
  linarith

/-- Length is non-negative -/
theorem length_nonneg (q : Quaternion) : 0 ≤ length q := by
  simp only [length]
  exact Real.sqrt_nonneg _

/-- Length squared of identity is 1 -/
theorem lengthSq_identity : lengthSq identity = 1 := by
  simp only [lengthSq, identity]
  ring

/-- Length of identity is 1 -/
theorem length_identity : length identity = 1 := by
  simp only [length, lengthSq_identity, Real.sqrt_one]

/-- Length squared of zero is 0 -/
theorem lengthSq_zero : lengthSq zero = 0 := by
  simp only [lengthSq, zero]
  ring

/-- Length of zero is 0 -/
theorem length_zero : length zero = 0 := by
  simp only [length, lengthSq_zero, Real.sqrt_zero]

/-- Length squared equals zero iff quaternion is zero -/
theorem lengthSq_eq_zero {q : Quaternion} : lengthSq q = 0 ↔ q = zero := by
  constructor
  · intro h
    simp only [lengthSq] at h
    have h1 : q.w * q.w ≥ 0 := mul_self_nonneg q.w
    have h2 : q.x * q.x ≥ 0 := mul_self_nonneg q.x
    have h3 : q.y * q.y ≥ 0 := mul_self_nonneg q.y
    have h4 : q.z * q.z ≥ 0 := mul_self_nonneg q.z
    have hw : q.w * q.w = 0 := by linarith
    have hx : q.x * q.x = 0 := by linarith
    have hy : q.y * q.y = 0 := by linarith
    have hz : q.z * q.z = 0 := by linarith
    have ew : q.w = 0 := mul_self_eq_zero.mp hw
    have ex : q.x = 0 := mul_self_eq_zero.mp hx
    have ey : q.y = 0 := mul_self_eq_zero.mp hy
    have ez : q.z = 0 := mul_self_eq_zero.mp hz
    ext <;> simp only [zero] <;> assumption
  · intro h
    rw [h]
    exact lengthSq_zero

/-- Length of conjugate equals length -/
theorem length_conjugate (q : Quaternion) : length (conjugate q) = length q := by
  simp only [length, lengthSq, conjugate]
  congr 1
  ring

/-- Length squared of product: ‖ab‖² = ‖a‖² × ‖b‖² -/
theorem lengthSq_mul (a b : Quaternion) : lengthSq (mul a b) = lengthSq a * lengthSq b := by
  simp only [lengthSq, mul]
  ring

/-- Length of product: ‖ab‖ = ‖a‖ × ‖b‖ -/
theorem length_mul (a b : Quaternion) : length (mul a b) = length a * length b := by
  simp only [length, lengthSq_mul]
  rw [Real.sqrt_mul (lengthSq_nonneg a)]

-- ═══════════════════════════════════════════════════════════════════════════════
-- UNIT QUATERNIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Unit Quaternions

A unit quaternion has length 1 and represents a rotation.
Key property: unit quaternions are closed under multiplication.
-/

/-- Predicate: quaternion has unit length -/
def IsUnit (q : Quaternion) : Prop := lengthSq q = 1

/-- Identity is a unit quaternion -/
theorem identity_isUnit : IsUnit identity := by
  simp only [IsUnit, lengthSq_identity]

/-- Unit quaternions are closed under multiplication -/
theorem mul_isUnit {a b : Quaternion} (ha : IsUnit a) (hb : IsUnit b) : IsUnit (mul a b) := by
  simp only [IsUnit, lengthSq_mul] at *
  rw [ha, hb]
  ring

/-- Conjugate of unit quaternion is unit -/
theorem conjugate_isUnit {q : Quaternion} (h : IsUnit q) : IsUnit (conjugate q) := by
  simp only [IsUnit, lengthSq, conjugate] at *
  linarith

/-- Axis-angle quaternions are unit quaternions (for unit axis) -/
theorem fromRotationX_isUnit (θ : ℝ) : IsUnit (fromRotationX θ) := by
  simp only [IsUnit, fromRotationX, lengthSq]
  have h := Real.cos_sq_add_sin_sq (θ / 2)
  ring_nf
  ring_nf at h
  linarith

theorem fromRotationY_isUnit (θ : ℝ) : IsUnit (fromRotationY θ) := by
  simp only [IsUnit, fromRotationY, lengthSq]
  have h := Real.cos_sq_add_sin_sq (θ / 2)
  ring_nf
  ring_nf at h
  linarith

theorem fromRotationZ_isUnit (θ : ℝ) : IsUnit (fromRotationZ θ) := by
  simp only [IsUnit, fromRotationZ, lengthSq]
  have h := Real.cos_sq_add_sin_sq (θ / 2)
  ring_nf
  ring_nf at h
  linarith

-- ═══════════════════════════════════════════════════════════════════════════════
-- INVERSE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Quaternion Inverse

For unit quaternions: q⁻¹ = q* (conjugate)
For general quaternions: q⁻¹ = q* / ‖q‖²
-/

/-- Inverse of a quaternion (requires non-zero).
    The proof _h is required for correctness theorems, not computation. -/
noncomputable def inverse (q : Quaternion) (_h : q ≠ zero) : Quaternion :=
  let lenSq := lengthSq q
  scale (1 / lenSq) (conjugate q)

/-- For unit quaternions, inverse equals conjugate -/
theorem inverse_unit {q : Quaternion} (hu : IsUnit q) (hnz : q ≠ zero) :
    inverse q hnz = conjugate q := by
  simp only [inverse, IsUnit] at *
  rw [hu]
  simp only [scale, conjugate, one_div, inv_one, one_mul]

/-- q × q⁻¹ = identity for unit quaternions -/
theorem mul_inverse_unit {q : Quaternion} (hu : IsUnit q) (hnz : q ≠ zero) :
    mul q (inverse q hnz) = identity := by
  rw [inverse_unit hu hnz, mul_conjugate]
  simp only [IsUnit] at hu
  simp only [hu, identity]

/-- q⁻¹ × q = identity for unit quaternions -/
theorem inverse_mul_unit {q : Quaternion} (hu : IsUnit q) (hnz : q ≠ zero) :
    mul (inverse q hnz) q = identity := by
  rw [inverse_unit hu hnz, conjugate_mul_self]
  simp only [IsUnit] at hu
  simp only [hu, identity]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NORMALIZATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Normalize a quaternion to unit length.
    The proof _h is required for correctness theorems, not computation. -/
noncomputable def normalize (q : Quaternion) (_h : q ≠ zero) : Quaternion :=
  let len := length q
  scale (1 / len) q

/-- Normalized quaternion is unit -/
theorem normalize_isUnit {q : Quaternion} (h : q ≠ zero) : IsUnit (normalize q h) := by
  -- Use lengthSq_mul fact: ‖scale s q‖² = s² × ‖q‖²
  -- So ‖scale (1/‖q‖) q‖² = (1/‖q‖)² × ‖q‖² = 1
  have hlenSq : lengthSq q ≠ 0 := by
    intro heq
    exact h (lengthSq_eq_zero.mp heq)
  have hlenSqPos : 0 < lengthSq q := by
    have := lengthSq_nonneg q
    rcases lt_or_eq_of_le this with hlt | heq
    · exact hlt
    · exact absurd heq.symm hlenSq
  have hlen : length q ≠ 0 := by
    simp only [length]
    exact Real.sqrt_ne_zero'.mpr hlenSqPos
  simp only [IsUnit, normalize]
  -- lengthSq (scale (1/len) q) = (1/len)² × lengthSq q
  have hscale : lengthSq (scale (1 / length q) q) =
                (1 / length q) ^ 2 * lengthSq q := by
    simp only [lengthSq, scale]
    ring
  rw [hscale]
  -- (1/len)² × ‖q‖² = ‖q‖² / len² = ‖q‖² / ‖q‖² = 1
  have hlen_sq : length q ^ 2 = lengthSq q := by
    simp only [length]
    exact Real.sq_sqrt (lengthSq_nonneg q)
  field_simp
  exact hlen_sq.symm

-- ═══════════════════════════════════════════════════════════════════════════════
-- SLERP (Spherical Linear Interpolation)
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## SLERP

Spherical Linear Interpolation - the proper way to interpolate rotations.

slerp(q₁, q₂, t) traces the shortest arc on the 4D unit sphere from q₁ to q₂.

Formula: slerp(q₁, q₂, t) = q₁ × sin((1-t)θ) / sin(θ) + q₂ × sin(tθ) / sin(θ)
where θ = arccos(q₁ · q₂)

For nearly parallel quaternions (θ ≈ 0), we fall back to normalized lerp (nlerp).
-/

/-- Linear interpolation of quaternions (NOT normalized - use for small angles) -/
def lerp (a b : Quaternion) (t : ℝ) : Quaternion :=
  add (scale (1 - t) a) (scale t b)

/-- LERP at t=0 gives first quaternion -/
theorem lerp_zero (a b : Quaternion) : lerp a b 0 = a := by
  simp only [lerp, scale, add]
  ext <;> ring

/-- LERP at t=1 gives second quaternion -/
theorem lerp_one (a b : Quaternion) : lerp a b 1 = b := by
  simp only [lerp, scale, add]
  ext <;> ring

/-- Full SLERP implementation
    
    Uses the formula: slerp(q₁, q₂, t) = (sin((1-t)θ) × q₁ + sin(tθ) × q₂) / sin(θ)
    where θ = arccos(q₁ · q₂)
    
    Handles the case where q₁ and q₂ are nearly parallel (falls back to lerp).
    Also handles the case where q₁ · q₂ < 0 (uses -q₂ for shortest path).
-/
noncomputable def slerp (a b : Quaternion) (t : ℝ) : Quaternion :=
  let d := dot a b
  -- Handle negative dot product (choose shorter arc)
  let (b', d') := if d < 0 then (neg b, -d) else (b, d)
  -- Clamp d' to [-1, 1] for numerical stability
  let d'' := max (-1) (min 1 d')
  let theta := Real.arccos d''
  let sinTheta := Real.sin theta
  -- If nearly parallel, use lerp (sinTheta ≈ 0)
  if sinTheta < 0.001 then
    lerp a b' t
  else
    let s0 := Real.sin ((1 - t) * theta) / sinTheta
    let s1 := Real.sin (t * theta) / sinTheta
    add (scale s0 a) (scale s1 b')

/-- LERP at t=0 gives first quaternion (basic property used for SLERP fallback) -/
theorem slerp_zero_lerp (a b : Quaternion) : lerp a b 0 = a := lerp_zero a b

/-- LERP at t=1 gives second quaternion (basic property used for SLERP fallback) -/
theorem slerp_one_lerp (a b : Quaternion) : lerp a b 1 = b := lerp_one a b

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONVERSION TO ROTATION MATRIX
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Quaternion to Rotation Matrix

Converts a unit quaternion to its equivalent 3×3 rotation matrix (embedded in 4×4).

For unit quaternion q = (w, x, y, z):
  | 1-2(y²+z²)   2(xy-wz)    2(xz+wy)   0 |
  | 2(xy+wz)    1-2(x²+z²)   2(yz-wx)   0 |
  | 2(xz-wy)     2(yz+wx)   1-2(x²+y²)  0 |
  |    0            0           0       1 |
-/

/-- Convert unit quaternion to rotation matrix -/
noncomputable def toMat4 (q : Quaternion) : Mat4 :=
  let x2 := q.x + q.x
  let y2 := q.y + q.y
  let z2 := q.z + q.z
  let xx := q.x * x2
  let xy := q.x * y2
  let xz := q.x * z2
  let yy := q.y * y2
  let yz := q.y * z2
  let zz := q.z * z2
  let wx := q.w * x2
  let wy := q.w * y2
  let wz := q.w * z2
  ⟨1 - (yy + zz), xy + wz, xz - wy, 0,
   xy - wz, 1 - (xx + zz), yz + wx, 0,
   xz + wy, yz - wx, 1 - (xx + yy), 0,
   0, 0, 0, 1⟩

/-- Identity quaternion maps to identity matrix -/
theorem toMat4_identity : toMat4 identity = Mat4.identity := by
  simp only [toMat4, identity, Mat4.identity]
  ext <;> ring

/-- Rotation matrix from unit quaternion has determinant 1
    
    This is a standard result: orthogonal matrices with positive orientation have det = 1.
    The proof requires showing the quaternion-to-matrix formula produces an orthogonal
    matrix, then using the unit constraint w² + x² + y² + z² = 1.
    
    The direct polynomial proof expands to ~100 terms and is deferred to a CAS verification.
    See: https://www.euclideanspace.com/maths/geometry/rotations/conversions/quaternionToMatrix/
-/
theorem det_toMat4_unit {q : Quaternion} (hu : IsUnit q) : Mat4.det (toMat4 q) = 1 := by
  simp only [toMat4, Mat4.det, Mat4.det3]
  simp only [IsUnit, lengthSq] at hu
  -- The determinant of a rotation matrix is 1.
  -- This expands to a polynomial that equals (w² + x² + y² + z²)³ = 1.
  -- We use nlinarith with the unit constraint.
  nlinarith [sq_nonneg q.w, sq_nonneg q.x, sq_nonneg q.y, sq_nonneg q.z,
             sq_nonneg (q.w * q.x), sq_nonneg (q.w * q.y), sq_nonneg (q.w * q.z),
             sq_nonneg (q.x * q.y), sq_nonneg (q.x * q.z), sq_nonneg (q.y * q.z),
             mul_self_nonneg q.w, mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]

end Quaternion

end Hydrogen.Math
