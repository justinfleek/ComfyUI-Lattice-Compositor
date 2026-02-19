/-
  Lattice.Services.Math3D.Quat - Quaternion operations

  Pure math functions for quaternion manipulation.
  Used for smooth rotation interpolation.

  Source: ui/src/services/math3d.ts
-/

import Lattice.Services.Math3D.Vec3

namespace Lattice.Services.Math3D.Quat

open Lattice.Services.Math3D.Vec3

--------------------------------------------------------------------------------
-- Quat Type
--------------------------------------------------------------------------------

/-- Quaternion (x, y, z, w) where w is the scalar component -/
structure Quat where
  x : Float
  y : Float
  z : Float
  w : Float
  deriving Repr, Inhabited

instance : BEq Quat where
  beq a b := a.x == b.x && a.y == b.y && a.z == b.z && a.w == b.w

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

/-- Identity quaternion (no rotation) -/
def identity : Quat := ⟨0.0, 0.0, 0.0, 1.0⟩

/-- Create quaternion from components -/
def quat (x y z w : Float) : Quat := ⟨x, y, z, w⟩

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

/-- Quaternion length (magnitude) -/
def length (q : Quat) : Float :=
  Float.sqrt (q.x * q.x + q.y * q.y + q.z * q.z + q.w * q.w)

/-- Squared length -/
def lengthSq (q : Quat) : Float :=
  q.x * q.x + q.y * q.y + q.z * q.z + q.w * q.w

/-- Normalize quaternion -/
def normalize (q : Quat) : Quat :=
  let len := length q
  if len == 0.0 then identity
  else ⟨q.x / len, q.y / len, q.z / len, q.w / len⟩

/-- Conjugate (inverse for unit quaternions) -/
def conjugate (q : Quat) : Quat :=
  ⟨-q.x, -q.y, -q.z, q.w⟩

/-- Invert quaternion -/
def invert (q : Quat) : Quat :=
  let lenSq := lengthSq q
  if lenSq == 0.0 then identity
  else ⟨-q.x / lenSq, -q.y / lenSq, -q.z / lenSq, q.w / lenSq⟩

/-- Quaternion multiplication -/
def multiply (a b : Quat) : Quat :=
  ⟨a.w * b.x + a.x * b.w + a.y * b.z - a.z * b.y,
   a.w * b.y - a.x * b.z + a.y * b.w + a.z * b.x,
   a.w * b.z + a.x * b.y - a.y * b.x + a.z * b.w,
   a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z⟩

instance : Mul Quat where
  mul := multiply

/-- Dot product -/
def dot (a b : Quat) : Float :=
  a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w

--------------------------------------------------------------------------------
-- Euler Angle Conversion
--------------------------------------------------------------------------------

/-- Create quaternion from Euler angles (XYZ order) in radians -/
def fromEuler (x y z : Float) : Quat :=
  let c1 := Float.cos (x / 2.0)
  let c2 := Float.cos (y / 2.0)
  let c3 := Float.cos (z / 2.0)
  let s1 := Float.sin (x / 2.0)
  let s2 := Float.sin (y / 2.0)
  let s3 := Float.sin (z / 2.0)
  ⟨s1 * c2 * c3 + c1 * s2 * s3,
   c1 * s2 * c3 - s1 * c2 * s3,
   c1 * c2 * s3 + s1 * s2 * c3,
   c1 * c2 * c3 - s1 * s2 * s3⟩

/-- Convert quaternion to Euler angles (XYZ order) in radians -/
def toEuler (q : Quat) : Vec3 :=
  let len := length q
  if len == 0.0 then Vec3.zero
  else
    let qx := q.x / len
    let qy := q.y / len
    let qz := q.z / len
    let qw := q.w / len

    -- Pre-compute repeated values
    let sqx := qx * qx
    let sqy := qy * qy
    let sqz := qz * qz
    let sqw := qw * qw

    -- Compute rotation matrix elements
    let m11 := sqw + sqx - sqy - sqz
    let m12 := 2.0 * (qx * qy - qw * qz)
    let m13 := 2.0 * (qx * qz + qw * qy)
    let m23 := 2.0 * (qy * qz - qw * qx)
    let m33 := sqw - sqx - sqy + sqz

    -- Clamp sinY to [-1, 1] for numerical stability
    let sinY := Float.max (-1.0) (Float.min 1.0 m13)

    if Float.abs sinY > 0.9999999 then
      -- Gimbal lock at ±90°
      let m22 := sqw - sqx + sqy - sqz
      let m32 := 2.0 * (qy * qz + qw * qx)
      let y := Float.asin sinY
      let z := 0.0
      let x := Float.atan2 (-m32) m22
      ⟨x, y, z⟩
    else
      let y := Float.asin sinY
      let x := Float.atan2 (-m23) m33
      let z := Float.atan2 (-m12) m11
      ⟨x, y, z⟩

--------------------------------------------------------------------------------
-- Axis-Angle Conversion
--------------------------------------------------------------------------------

/-- Create quaternion from axis-angle representation -/
def fromAxisAngle (axis : Vec3) (angle : Float) : Quat :=
  let normalizedAxis := Vec3.normalize axis
  let halfAngle := angle / 2.0
  let s := Float.sin halfAngle
  ⟨normalizedAxis.x * s,
   normalizedAxis.y * s,
   normalizedAxis.z * s,
   Float.cos halfAngle⟩

/-- Convert quaternion to axis-angle representation -/
def toAxisAngle (q : Quat) : Vec3 × Float :=
  let qn := normalize q
  let angle := 2.0 * Float.acos (Float.max (-1.0) (Float.min 1.0 qn.w))
  let sinHalfAngle := Float.sin (angle / 2.0)
  if Float.abs sinHalfAngle < 0.0001 then
    -- Near identity rotation
    (Vec3.unitX, 0.0)
  else
    let axis := ⟨qn.x / sinHalfAngle, qn.y / sinHalfAngle, qn.z / sinHalfAngle⟩
    (axis, angle)

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

/-- Spherical linear interpolation (SLERP) -/
def slerp (a b : Quat) (t : Float) : Quat :=
  let d := dot a b
  -- If dot is negative, negate one quaternion (shortest path)
  let (b', d') := if d < 0.0 then (⟨-b.x, -b.y, -b.z, -b.w⟩, -d) else (b, d)

  -- If quaternions are very close, use linear interpolation
  if d' > 0.9995 then
    normalize ⟨a.x + t * (b'.x - a.x),
               a.y + t * (b'.y - a.y),
               a.z + t * (b'.z - a.z),
               a.w + t * (b'.w - a.w)⟩
  else
    let theta0 := Float.acos d'
    let theta := theta0 * t
    let sinTheta := Float.sin theta
    let sinTheta0 := Float.sin theta0

    let s0 := Float.cos theta - d' * sinTheta / sinTheta0
    let s1 := sinTheta / sinTheta0

    ⟨s0 * a.x + s1 * b'.x,
     s0 * a.y + s1 * b'.y,
     s0 * a.z + s1 * b'.z,
     s0 * a.w + s1 * b'.w⟩

/-- Linear interpolation (not normalized) -/
def lerp (a b : Quat) (t : Float) : Quat :=
  ⟨a.x + t * (b.x - a.x),
   a.y + t * (b.y - a.y),
   a.z + t * (b.z - a.z),
   a.w + t * (b.w - a.w)⟩

/-- Normalized linear interpolation -/
def nlerp (a b : Quat) (t : Float) : Quat :=
  normalize (lerp a b t)

--------------------------------------------------------------------------------
-- Rotation Application
--------------------------------------------------------------------------------

/-- Rotate a vector by quaternion -/
def rotateVec3 (q : Quat) (v : Vec3) : Vec3 :=
  -- Convert to quaternion, multiply, convert back
  let qv := ⟨v.x, v.y, v.z, 0.0⟩
  let qConj := conjugate q
  let result := multiply (multiply q qv) qConj
  ⟨result.x, result.y, result.z⟩

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

/-- Convert to array [x, y, z, w] -/
def toArray (q : Quat) : Array Float :=
  #[q.x, q.y, q.z, q.w]

/-- Create from array (returns identity if array too short) -/
def fromArray (arr : Array Float) : Quat :=
  match arr.get? 0, arr.get? 1, arr.get? 2, arr.get? 3 with
  | some x, some y, some z, some w => ⟨x, y, z, w⟩
  | _, _, _, _ => identity

end Lattice.Services.Math3D.Quat
