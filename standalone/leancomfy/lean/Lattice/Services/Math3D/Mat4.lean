/-
  Lattice.Services.Math3D.Mat4 - 4x4 Matrix operations

  Pure math functions for 4x4 matrix manipulation.
  Column-major order for GPU compatibility.

  Source: ui/src/services/math3d.ts
-/

import Lattice.Services.Math3D.Vec3

namespace Lattice.Services.Math3D.Mat4

open Lattice.Services.Math3D.Vec3

--------------------------------------------------------------------------------
-- Mat4 Type (Column-Major, GPU-compatible)
--------------------------------------------------------------------------------

/-- 4x4 Matrix in column-major order -/
structure Mat4 where
  -- Column 0
  m00 : Float; m10 : Float; m20 : Float; m30 : Float
  -- Column 1
  m01 : Float; m11 : Float; m21 : Float; m31 : Float
  -- Column 2
  m02 : Float; m12 : Float; m22 : Float; m32 : Float
  -- Column 3
  m03 : Float; m13 : Float; m23 : Float; m33 : Float
  deriving Repr, Inhabited

instance : BEq Mat4 where
  beq a b :=
    a.m00 == b.m00 && a.m10 == b.m10 && a.m20 == b.m20 && a.m30 == b.m30 &&
    a.m01 == b.m01 && a.m11 == b.m11 && a.m21 == b.m21 && a.m31 == b.m31 &&
    a.m02 == b.m02 && a.m12 == b.m12 && a.m22 == b.m22 && a.m32 == b.m32 &&
    a.m03 == b.m03 && a.m13 == b.m13 && a.m23 == b.m23 && a.m33 == b.m33

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

/-- Matrix multiplication -/
def multiply (a b : Mat4) : Mat4 :=
  let r00 := a.m00*b.m00 + a.m01*b.m10 + a.m02*b.m20 + a.m03*b.m30
  let r10 := a.m10*b.m00 + a.m11*b.m10 + a.m12*b.m20 + a.m13*b.m30
  let r20 := a.m20*b.m00 + a.m21*b.m10 + a.m22*b.m20 + a.m23*b.m30
  let r30 := a.m30*b.m00 + a.m31*b.m10 + a.m32*b.m20 + a.m33*b.m30

  let r01 := a.m00*b.m01 + a.m01*b.m11 + a.m02*b.m21 + a.m03*b.m31
  let r11 := a.m10*b.m01 + a.m11*b.m11 + a.m12*b.m21 + a.m13*b.m31
  let r21 := a.m20*b.m01 + a.m21*b.m11 + a.m22*b.m21 + a.m23*b.m31
  let r31 := a.m30*b.m01 + a.m31*b.m11 + a.m32*b.m21 + a.m33*b.m31

  let r02 := a.m00*b.m02 + a.m01*b.m12 + a.m02*b.m22 + a.m03*b.m32
  let r12 := a.m10*b.m02 + a.m11*b.m12 + a.m12*b.m22 + a.m13*b.m32
  let r22 := a.m20*b.m02 + a.m21*b.m12 + a.m22*b.m22 + a.m23*b.m32
  let r32 := a.m30*b.m02 + a.m31*b.m12 + a.m32*b.m22 + a.m33*b.m32

  let r03 := a.m00*b.m03 + a.m01*b.m13 + a.m02*b.m23 + a.m03*b.m33
  let r13 := a.m10*b.m03 + a.m11*b.m13 + a.m12*b.m23 + a.m13*b.m33
  let r23 := a.m20*b.m03 + a.m21*b.m13 + a.m22*b.m23 + a.m23*b.m33
  let r33 := a.m30*b.m03 + a.m31*b.m13 + a.m32*b.m23 + a.m33*b.m33

  ⟨r00, r10, r20, r30,
   r01, r11, r21, r31,
   r02, r12, r22, r32,
   r03, r13, r23, r33⟩

instance : Mul Mat4 where
  mul := multiply

--------------------------------------------------------------------------------
-- Transform Matrices
--------------------------------------------------------------------------------

/-- Translation matrix -/
def translate (v : Vec3) : Mat4 :=
  ⟨1, 0, 0, 0,
   0, 1, 0, 0,
   0, 0, 1, 0,
   v.x, v.y, v.z, 1⟩

/-- Scale matrix -/
def scale (s : Vec3) : Mat4 :=
  ⟨s.x, 0, 0, 0,
   0, s.y, 0, 0,
   0, 0, s.z, 0,
   0, 0, 0, 1⟩

/-- Uniform scale matrix -/
def scaleUniform (s : Float) : Mat4 :=
  ⟨s, 0, 0, 0,
   0, s, 0, 0,
   0, 0, s, 0,
   0, 0, 0, 1⟩

/-- Rotation around X axis -/
def rotateX (angle : Float) : Mat4 :=
  let c := Float.cos angle
  let s := Float.sin angle
  ⟨1, 0, 0, 0,
   0, c, s, 0,
   0, -s, c, 0,
   0, 0, 0, 1⟩

/-- Rotation around Y axis -/
def rotateY (angle : Float) : Mat4 :=
  let c := Float.cos angle
  let s := Float.sin angle
  ⟨c, 0, -s, 0,
   0, 1, 0, 0,
   s, 0, c, 0,
   0, 0, 0, 1⟩

/-- Rotation around Z axis -/
def rotateZ (angle : Float) : Mat4 :=
  let c := Float.cos angle
  let s := Float.sin angle
  ⟨c, s, 0, 0,
   -s, c, 0, 0,
   0, 0, 1, 0,
   0, 0, 0, 1⟩

--------------------------------------------------------------------------------
-- Projection Matrices
--------------------------------------------------------------------------------

/-- Perspective projection matrix -/
def perspective (fovY aspect near far : Float) : Mat4 :=
  let f := 1.0 / Float.tan (fovY / 2.0)
  let nf := 1.0 / (near - far)
  ⟨f / aspect, 0, 0, 0,
   0, f, 0, 0,
   0, 0, (far + near) * nf, -1,
   0, 0, 2.0 * far * near * nf, 0⟩

/-- Orthographic projection matrix -/
def orthographic (left right bottom top near far : Float) : Mat4 :=
  let w := 1.0 / (right - left)
  let h := 1.0 / (top - bottom)
  let p := 1.0 / (far - near)
  ⟨2.0 * w, 0, 0, 0,
   0, 2.0 * h, 0, 0,
   0, 0, -2.0 * p, 0,
   -(right + left) * w, -(top + bottom) * h, -(far + near) * p, 1⟩

--------------------------------------------------------------------------------
-- View Matrix
--------------------------------------------------------------------------------

/-- Look-at view matrix -/
def lookAt (eye target up : Vec3) : Mat4 :=
  let zAxis := Vec3.normalize (Vec3.sub eye target)
  let xAxis := Vec3.normalize (Vec3.cross up zAxis)
  let yAxis := Vec3.cross zAxis xAxis
  ⟨xAxis.x, yAxis.x, zAxis.x, 0,
   xAxis.y, yAxis.y, zAxis.y, 0,
   xAxis.z, yAxis.z, zAxis.z, 0,
   -Vec3.dot xAxis eye, -Vec3.dot yAxis eye, -Vec3.dot zAxis eye, 1⟩

--------------------------------------------------------------------------------
-- Transform Application
--------------------------------------------------------------------------------

/-- Transform a point (applies translation) -/
def transformPoint (m : Mat4) (p : Vec3) : Vec3 :=
  let w := m.m30 * p.x + m.m31 * p.y + m.m32 * p.z + m.m33
  let invW := if w == 0.0 then 1.0 else 1.0 / w
  ⟨(m.m00 * p.x + m.m01 * p.y + m.m02 * p.z + m.m03) * invW,
   (m.m10 * p.x + m.m11 * p.y + m.m12 * p.z + m.m13) * invW,
   (m.m20 * p.x + m.m21 * p.y + m.m22 * p.z + m.m23) * invW⟩

/-- Transform a direction (ignores translation) -/
def transformDirection (m : Mat4) (v : Vec3) : Vec3 :=
  ⟨m.m00 * v.x + m.m01 * v.y + m.m02 * v.z,
   m.m10 * v.x + m.m11 * v.y + m.m12 * v.z,
   m.m20 * v.x + m.m21 * v.y + m.m22 * v.z⟩

--------------------------------------------------------------------------------
-- Matrix Inversion
--------------------------------------------------------------------------------

/-- Compute determinant -/
def determinant (m : Mat4) : Float :=
  let a := m.m00; let b := m.m01; let c := m.m02; let d := m.m03
  let e := m.m10; let f := m.m11; let g := m.m12; let h := m.m13
  let i := m.m20; let j := m.m21; let k := m.m22; let l := m.m23
  let mm := m.m30; let n := m.m31; let o := m.m32; let p := m.m33

  let kp_lo := k*p - l*o
  let jp_ln := j*p - l*n
  let jo_kn := j*o - k*n
  let ip_lm := i*p - l*mm
  let io_km := i*o - k*mm
  let in_jm := i*n - j*mm

  a*(f*kp_lo - g*jp_ln + h*jo_kn) -
  b*(e*kp_lo - g*ip_lm + h*io_km) +
  c*(e*jp_ln - f*ip_lm + h*in_jm) -
  d*(e*jo_kn - f*io_km + g*in_jm)

/-- Inversion result type -/
inductive InvertResult where
  | success (m : Mat4)
  | singularMatrix
  deriving Repr

/-- Invert matrix (returns Option to handle singular case) -/
def invert (m : Mat4) : InvertResult :=
  let det := determinant m
  if det == 0.0 then .singularMatrix
  else
    let invDet := 1.0 / det

    let a := m.m00; let b := m.m01; let c := m.m02; let d := m.m03
    let e := m.m10; let f := m.m11; let g := m.m12; let h := m.m13
    let i := m.m20; let j := m.m21; let k := m.m22; let l := m.m23
    let mm := m.m30; let n := m.m31; let o := m.m32; let p := m.m33

    -- Compute cofactors
    let c00 := f*(k*p - l*o) - g*(j*p - l*n) + h*(j*o - k*n)
    let c01 := -(e*(k*p - l*o) - g*(i*p - l*mm) + h*(i*o - k*mm))
    let c02 := e*(j*p - l*n) - f*(i*p - l*mm) + h*(i*n - j*mm)
    let c03 := -(e*(j*o - k*n) - f*(i*o - k*mm) + g*(i*n - j*mm))

    let c10 := -(b*(k*p - l*o) - c*(j*p - l*n) + d*(j*o - k*n))
    let c11 := a*(k*p - l*o) - c*(i*p - l*mm) + d*(i*o - k*mm)
    let c12 := -(a*(j*p - l*n) - b*(i*p - l*mm) + d*(i*n - j*mm))
    let c13 := a*(j*o - k*n) - b*(i*o - k*mm) + c*(i*n - j*mm)

    let c20 := b*(g*p - h*o) - c*(f*p - h*n) + d*(f*o - g*n)
    let c21 := -(a*(g*p - h*o) - c*(e*p - h*mm) + d*(e*o - g*mm))
    let c22 := a*(f*p - h*n) - b*(e*p - h*mm) + d*(e*n - f*mm)
    let c23 := -(a*(f*o - g*n) - b*(e*o - g*mm) + c*(e*n - f*mm))

    let c30 := -(b*(g*l - h*k) - c*(f*l - h*j) + d*(f*k - g*j))
    let c31 := a*(g*l - h*k) - c*(e*l - h*i) + d*(e*k - g*i)
    let c32 := -(a*(f*l - h*j) - b*(e*l - h*i) + d*(e*j - f*i))
    let c33 := a*(f*k - g*j) - b*(e*k - g*i) + c*(e*j - f*i)

    .success ⟨c00 * invDet, c01 * invDet, c02 * invDet, c03 * invDet,
              c10 * invDet, c11 * invDet, c12 * invDet, c13 * invDet,
              c20 * invDet, c21 * invDet, c22 * invDet, c23 * invDet,
              c30 * invDet, c31 * invDet, c32 * invDet, c33 * invDet⟩

--------------------------------------------------------------------------------
-- Transpose
--------------------------------------------------------------------------------

/-- Transpose matrix -/
def transpose (m : Mat4) : Mat4 :=
  ⟨m.m00, m.m01, m.m02, m.m03,
   m.m10, m.m11, m.m12, m.m13,
   m.m20, m.m21, m.m22, m.m23,
   m.m30, m.m31, m.m32, m.m33⟩

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

/-- Convert to flat array (column-major) -/
def toArray (m : Mat4) : Array Float :=
  #[m.m00, m.m10, m.m20, m.m30,
    m.m01, m.m11, m.m21, m.m31,
    m.m02, m.m12, m.m22, m.m32,
    m.m03, m.m13, m.m23, m.m33]

end Lattice.Services.Math3D.Mat4
