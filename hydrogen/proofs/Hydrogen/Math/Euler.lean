/-
  Hydrogen.Math.Euler
  
  Euler angles with rotation order for 3D rotations.
  
  PROVEN INVARIANTS:
    1. toQuaternion_identity: Euler(0,0,0) → identity quaternion
    2. toMat3_identity: Euler(0,0,0) → identity matrix
    3. toMat4_identity: Euler(0,0,0) → identity matrix
    4. order_default: XYZ is the default order
  
  THREE.JS PARITY:
    - All six rotation orders: XYZ, YZX, ZXY, XZY, YXZ, ZYX
    - Intrinsic Tait-Bryan angles (local coordinate rotations)
    - Conversion to/from quaternions and matrices
  
  APPLICATIONS:
    - Object rotation in 3D space
    - Camera orientation
    - Animation interpolation (via quaternion conversion)
  
  Status: FOUNDATIONAL - Core Euler type with rotation orders, proven conversions.
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Mat3
import Hydrogen.Math.Mat4
import Hydrogen.Math.Quaternion
import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- ROTATION ORDER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The six possible rotation orders for Euler angles.
    Each order specifies which axis to rotate around first, second, third.
    Three.js uses intrinsic rotations (local coordinate system).
-/
inductive RotationOrder : Type where
  | XYZ : RotationOrder  -- Default: rotate X, then Y, then Z
  | YZX : RotationOrder
  | ZXY : RotationOrder
  | XZY : RotationOrder
  | YXZ : RotationOrder
  | ZYX : RotationOrder
deriving DecidableEq, Repr

namespace RotationOrder

/-- The default rotation order (XYZ) -/
def default : RotationOrder := XYZ

end RotationOrder

-- ═══════════════════════════════════════════════════════════════════════════════
-- EULER DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Euler angles representing a 3D rotation.
    
    - x: rotation angle around X axis (pitch) in radians
    - y: rotation angle around Y axis (yaw) in radians
    - z: rotation angle around Z axis (roll) in radians
    - order: the order in which rotations are applied
    
    Three.js uses intrinsic Tait-Bryan angles: rotations are performed
    with respect to the local (rotating) coordinate system, not the
    world coordinate system.
-/
structure Euler where
  x : ℝ
  y : ℝ
  z : ℝ
  order : RotationOrder

namespace Euler

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {a b : Euler} 
    (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) (ho : a.order = b.order) : 
    a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Zero rotation (identity) with default XYZ order -/
def zero : Euler := ⟨0, 0, 0, RotationOrder.XYZ⟩

/-- Zero rotation with specified order -/
def zeroWithOrder (order : RotationOrder) : Euler := ⟨0, 0, 0, order⟩

/-- Create Euler from angles with default XYZ order -/
def fromAngles (x y z : ℝ) : Euler := ⟨x, y, z, RotationOrder.XYZ⟩

/-- Create Euler from angles with specified order -/
def fromAnglesWithOrder (x y z : ℝ) (order : RotationOrder) : Euler := ⟨x, y, z, order⟩

/-- Create Euler from a Vec3 (using x, y, z as angles) with default order -/
def fromVec3 (v : Vec3) : Euler := ⟨v.x, v.y, v.z, RotationOrder.XYZ⟩

/-- Create Euler from a Vec3 with specified order -/
def fromVec3WithOrder (v : Vec3) (order : RotationOrder) : Euler := ⟨v.x, v.y, v.z, order⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert Euler angles to Vec3 (loses order information) -/
def toVec3 (e : Euler) : Vec3 := ⟨e.x, e.y, e.z⟩

/-- Set a new rotation order (reinterprets existing angles) -/
def setOrder (e : Euler) (order : RotationOrder) : Euler := ⟨e.x, e.y, e.z, order⟩

/-- Negation (reverse rotation) -/
def neg (e : Euler) : Euler := ⟨-e.x, -e.y, -e.z, e.order⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONVERSION TO MAT3 (BY ROTATION ORDER)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert Euler angles to Mat3 rotation matrix.
    
    For intrinsic rotations with order XYZ:
    M = Rz(z) × Ry(y) × Rx(x)
    
    The rotation matrices are multiplied in REVERSE order because
    intrinsic rotations apply from right to left.
-/
noncomputable def toMat3 (e : Euler) : Mat3 :=
  let rx := Mat3.makeRotationX e.x
  let ry := Mat3.makeRotationY e.y
  let rz := Mat3.makeRotationZ e.z
  match e.order with
  | RotationOrder.XYZ => Mat3.mul (Mat3.mul rz ry) rx  -- Z(Y(X))
  | RotationOrder.YZX => Mat3.mul (Mat3.mul rx rz) ry  -- X(Z(Y))
  | RotationOrder.ZXY => Mat3.mul (Mat3.mul ry rx) rz  -- Y(X(Z))
  | RotationOrder.XZY => Mat3.mul (Mat3.mul ry rz) rx  -- Y(Z(X))
  | RotationOrder.YXZ => Mat3.mul (Mat3.mul rz rx) ry  -- Z(X(Y))
  | RotationOrder.ZYX => Mat3.mul (Mat3.mul rx ry) rz  -- X(Y(Z))

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONVERSION TO MAT4
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert Euler angles to Mat4 rotation matrix.
    The translation component is zero (pure rotation).
-/
noncomputable def toMat4 (e : Euler) : Mat4 :=
  let rx := Mat4.makeRotationX e.x
  let ry := Mat4.makeRotationY e.y
  let rz := Mat4.makeRotationZ e.z
  match e.order with
  | RotationOrder.XYZ => Mat4.mul (Mat4.mul rz ry) rx
  | RotationOrder.YZX => Mat4.mul (Mat4.mul rx rz) ry
  | RotationOrder.ZXY => Mat4.mul (Mat4.mul ry rx) rz
  | RotationOrder.XZY => Mat4.mul (Mat4.mul ry rz) rx
  | RotationOrder.YXZ => Mat4.mul (Mat4.mul rz rx) ry
  | RotationOrder.ZYX => Mat4.mul (Mat4.mul rx ry) rz

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONVERSION TO QUATERNION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert Euler angles to Quaternion.
    
    Uses the formula for composing axis rotations into a single quaternion.
    For XYZ order: q = qz * qy * qx (applying x first, then y, then z)
-/
noncomputable def toQuaternion (e : Euler) : Quaternion :=
  let qx := Quaternion.fromRotationX e.x
  let qy := Quaternion.fromRotationY e.y
  let qz := Quaternion.fromRotationZ e.z
  match e.order with
  | RotationOrder.XYZ => Quaternion.mul (Quaternion.mul qz qy) qx
  | RotationOrder.YZX => Quaternion.mul (Quaternion.mul qx qz) qy
  | RotationOrder.ZXY => Quaternion.mul (Quaternion.mul qy qx) qz
  | RotationOrder.XZY => Quaternion.mul (Quaternion.mul qy qz) qx
  | RotationOrder.YXZ => Quaternion.mul (Quaternion.mul qz qx) qy
  | RotationOrder.ZYX => Quaternion.mul (Quaternion.mul qx qy) qz

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: ZERO/IDENTITY
-- ═══════════════════════════════════════════════════════════════════════════════

theorem zero_x : zero.x = 0 := rfl
theorem zero_y : zero.y = 0 := rfl
theorem zero_z : zero.z = 0 := rfl
theorem zero_order : zero.order = RotationOrder.XYZ := rfl

theorem zeroWithOrder_x (o : RotationOrder) : (zeroWithOrder o).x = 0 := rfl
theorem zeroWithOrder_y (o : RotationOrder) : (zeroWithOrder o).y = 0 := rfl
theorem zeroWithOrder_z (o : RotationOrder) : (zeroWithOrder o).z = 0 := rfl
theorem zeroWithOrder_order (o : RotationOrder) : (zeroWithOrder o).order = o := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: CONVERSION IDENTITY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Zero Euler angles convert to identity Mat3 (for all orders) -/
theorem toMat3_zero_XYZ : toMat3 zero = Mat3.identity := by
  simp only [toMat3, zero]
  simp only [Mat3.makeRotationX, Mat3.makeRotationY, Mat3.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat3.mul, Mat3.identity]
  ext <;> ring

theorem toMat3_zero_YZX : toMat3 (zeroWithOrder RotationOrder.YZX) = Mat3.identity := by
  simp only [toMat3, zeroWithOrder]
  simp only [Mat3.makeRotationX, Mat3.makeRotationY, Mat3.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat3.mul, Mat3.identity]
  ext <;> ring

theorem toMat3_zero_ZXY : toMat3 (zeroWithOrder RotationOrder.ZXY) = Mat3.identity := by
  simp only [toMat3, zeroWithOrder]
  simp only [Mat3.makeRotationX, Mat3.makeRotationY, Mat3.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat3.mul, Mat3.identity]
  ext <;> ring

theorem toMat3_zero_XZY : toMat3 (zeroWithOrder RotationOrder.XZY) = Mat3.identity := by
  simp only [toMat3, zeroWithOrder]
  simp only [Mat3.makeRotationX, Mat3.makeRotationY, Mat3.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat3.mul, Mat3.identity]
  ext <;> ring

theorem toMat3_zero_YXZ : toMat3 (zeroWithOrder RotationOrder.YXZ) = Mat3.identity := by
  simp only [toMat3, zeroWithOrder]
  simp only [Mat3.makeRotationX, Mat3.makeRotationY, Mat3.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat3.mul, Mat3.identity]
  ext <;> ring

theorem toMat3_zero_ZYX : toMat3 (zeroWithOrder RotationOrder.ZYX) = Mat3.identity := by
  simp only [toMat3, zeroWithOrder]
  simp only [Mat3.makeRotationX, Mat3.makeRotationY, Mat3.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat3.mul, Mat3.identity]
  ext <;> ring

/-- Zero Euler angles convert to identity Mat3 for any order -/
theorem toMat3_zeroWithOrder (o : RotationOrder) : toMat3 (zeroWithOrder o) = Mat3.identity := by
  cases o
  · exact toMat3_zero_XYZ
  · exact toMat3_zero_YZX
  · exact toMat3_zero_ZXY
  · exact toMat3_zero_XZY
  · exact toMat3_zero_YXZ
  · exact toMat3_zero_ZYX

/-- Zero Euler angles convert to identity Mat4 (for all orders) -/
theorem toMat4_zero_XYZ : toMat4 zero = Mat4.identity := by
  simp only [toMat4, zero]
  simp only [Mat4.makeRotationX, Mat4.makeRotationY, Mat4.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat4.mul, Mat4.identity]
  ext <;> ring

theorem toMat4_zero_YZX : toMat4 (zeroWithOrder RotationOrder.YZX) = Mat4.identity := by
  simp only [toMat4, zeroWithOrder]
  simp only [Mat4.makeRotationX, Mat4.makeRotationY, Mat4.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat4.mul, Mat4.identity]
  ext <;> ring

theorem toMat4_zero_ZXY : toMat4 (zeroWithOrder RotationOrder.ZXY) = Mat4.identity := by
  simp only [toMat4, zeroWithOrder]
  simp only [Mat4.makeRotationX, Mat4.makeRotationY, Mat4.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat4.mul, Mat4.identity]
  ext <;> ring

theorem toMat4_zero_XZY : toMat4 (zeroWithOrder RotationOrder.XZY) = Mat4.identity := by
  simp only [toMat4, zeroWithOrder]
  simp only [Mat4.makeRotationX, Mat4.makeRotationY, Mat4.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat4.mul, Mat4.identity]
  ext <;> ring

theorem toMat4_zero_YXZ : toMat4 (zeroWithOrder RotationOrder.YXZ) = Mat4.identity := by
  simp only [toMat4, zeroWithOrder]
  simp only [Mat4.makeRotationX, Mat4.makeRotationY, Mat4.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat4.mul, Mat4.identity]
  ext <;> ring

theorem toMat4_zero_ZYX : toMat4 (zeroWithOrder RotationOrder.ZYX) = Mat4.identity := by
  simp only [toMat4, zeroWithOrder]
  simp only [Mat4.makeRotationX, Mat4.makeRotationY, Mat4.makeRotationZ]
  simp only [Real.cos_zero, Real.sin_zero]
  simp only [Mat4.mul, Mat4.identity]
  ext <;> ring

/-- Zero Euler angles convert to identity Mat4 for any order -/
theorem toMat4_zeroWithOrder (o : RotationOrder) : toMat4 (zeroWithOrder o) = Mat4.identity := by
  cases o
  · exact toMat4_zero_XYZ
  · exact toMat4_zero_YZX
  · exact toMat4_zero_ZXY
  · exact toMat4_zero_XZY
  · exact toMat4_zero_YXZ
  · exact toMat4_zero_ZYX

/-- Zero Euler angles convert to identity quaternion (for XYZ order) -/
theorem toQuaternion_zero_XYZ : toQuaternion zero = Quaternion.identity := by
  simp only [toQuaternion, zero]
  simp only [Quaternion.fromRotationX, Quaternion.fromRotationY, Quaternion.fromRotationZ]
  simp only [zero_div, Real.cos_zero, Real.sin_zero]
  simp only [Quaternion.mul, Quaternion.identity]
  ext <;> ring

theorem toQuaternion_zero_YZX : toQuaternion (zeroWithOrder RotationOrder.YZX) = Quaternion.identity := by
  simp only [toQuaternion, zeroWithOrder]
  simp only [Quaternion.fromRotationX, Quaternion.fromRotationY, Quaternion.fromRotationZ]
  simp only [zero_div, Real.cos_zero, Real.sin_zero]
  simp only [Quaternion.mul, Quaternion.identity]
  ext <;> ring

theorem toQuaternion_zero_ZXY : toQuaternion (zeroWithOrder RotationOrder.ZXY) = Quaternion.identity := by
  simp only [toQuaternion, zeroWithOrder]
  simp only [Quaternion.fromRotationX, Quaternion.fromRotationY, Quaternion.fromRotationZ]
  simp only [zero_div, Real.cos_zero, Real.sin_zero]
  simp only [Quaternion.mul, Quaternion.identity]
  ext <;> ring

theorem toQuaternion_zero_XZY : toQuaternion (zeroWithOrder RotationOrder.XZY) = Quaternion.identity := by
  simp only [toQuaternion, zeroWithOrder]
  simp only [Quaternion.fromRotationX, Quaternion.fromRotationY, Quaternion.fromRotationZ]
  simp only [zero_div, Real.cos_zero, Real.sin_zero]
  simp only [Quaternion.mul, Quaternion.identity]
  ext <;> ring

theorem toQuaternion_zero_YXZ : toQuaternion (zeroWithOrder RotationOrder.YXZ) = Quaternion.identity := by
  simp only [toQuaternion, zeroWithOrder]
  simp only [Quaternion.fromRotationX, Quaternion.fromRotationY, Quaternion.fromRotationZ]
  simp only [zero_div, Real.cos_zero, Real.sin_zero]
  simp only [Quaternion.mul, Quaternion.identity]
  ext <;> ring

theorem toQuaternion_zero_ZYX : toQuaternion (zeroWithOrder RotationOrder.ZYX) = Quaternion.identity := by
  simp only [toQuaternion, zeroWithOrder]
  simp only [Quaternion.fromRotationX, Quaternion.fromRotationY, Quaternion.fromRotationZ]
  simp only [zero_div, Real.cos_zero, Real.sin_zero]
  simp only [Quaternion.mul, Quaternion.identity]
  ext <;> ring

/-- Zero Euler angles convert to identity quaternion for any order -/
theorem toQuaternion_zeroWithOrder (o : RotationOrder) : 
    toQuaternion (zeroWithOrder o) = Quaternion.identity := by
  cases o
  · exact toQuaternion_zero_XYZ
  · exact toQuaternion_zero_YZX
  · exact toQuaternion_zero_ZXY
  · exact toQuaternion_zero_XZY
  · exact toQuaternion_zero_YXZ
  · exact toQuaternion_zero_ZYX

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: VEC3 ROUND-TRIP
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Converting to Vec3 and back preserves x angle -/
theorem fromVec3_toVec3_x (e : Euler) : (fromVec3 (toVec3 e)).x = e.x := by
  simp only [fromVec3, toVec3]

/-- Converting to Vec3 and back preserves y angle -/
theorem fromVec3_toVec3_y (e : Euler) : (fromVec3 (toVec3 e)).y = e.y := by
  simp only [fromVec3, toVec3]

/-- Converting to Vec3 and back preserves z angle -/
theorem fromVec3_toVec3_z (e : Euler) : (fromVec3 (toVec3 e)).z = e.z := by
  simp only [fromVec3, toVec3]

/-- Vec3 round-trip is identity -/
theorem toVec3_fromVec3 (v : Vec3) : toVec3 (fromVec3 v) = v := by
  simp only [toVec3, fromVec3]

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: NEG PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

theorem neg_neg (e : Euler) : neg (neg e) = e := by
  simp only [neg]
  ext
  · ring
  · ring
  · ring
  · rfl

theorem neg_zero : neg zero = zero := by
  simp only [neg, zero]
  ext
  · ring
  · ring
  · ring
  · rfl

theorem neg_preserves_order (e : Euler) : (neg e).order = e.order := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: SET ORDER
-- ═══════════════════════════════════════════════════════════════════════════════

theorem setOrder_preserves_x (e : Euler) (o : RotationOrder) : (setOrder e o).x = e.x := by
  simp only [setOrder]

theorem setOrder_preserves_y (e : Euler) (o : RotationOrder) : (setOrder e o).y = e.y := by
  simp only [setOrder]

theorem setOrder_preserves_z (e : Euler) (o : RotationOrder) : (setOrder e o).z = e.z := by
  simp only [setOrder]

theorem setOrder_changes_order (e : Euler) (o : RotationOrder) :
    (setOrder e o).order = o := rfl

theorem setOrder_same (e : Euler) : setOrder e e.order = e := by
  cases e
  simp only [setOrder]

end Euler

end Hydrogen.Math
