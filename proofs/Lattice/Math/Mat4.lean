/-
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // lattice // math // mat4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  MAT4 — 4x4 MATRICES FOR AGENT TRANSFORMS

  "The rendering system knows which agents affect which pixels."

  4x4 matrices are the universal language of 3D transforms:
  - Translation: where the agent moves
  - Rotation: how the agent orients
  - Scale: how the agent appears sized

  This module provides:
  1. Mat4 — 4x4 matrix with standard operations
  2. Identity and composition
  3. Transform builders (translate, rotate, scale)
  4. Proven properties (associativity, identity)

-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Lattice.Math.Vec3

namespace Lattice.Math.Mat4

open Lattice.Math.Vec3

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // mat4 type
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Mat4: A 4x4 matrix stored in column-major order.

Column-major matches GPU layout (WebGL, OpenGL, Vulkan).
m[col][row] indexing.

Layout:
  m00 m10 m20 m30
  m01 m11 m21 m31
  m02 m12 m22 m32
  m03 m13 m23 m33
-/
structure Mat4 where
  -- Column 0
  m00 : ℝ; m01 : ℝ; m02 : ℝ; m03 : ℝ
  -- Column 1
  m10 : ℝ; m11 : ℝ; m12 : ℝ; m13 : ℝ
  -- Column 2
  m20 : ℝ; m21 : ℝ; m22 : ℝ; m23 : ℝ
  -- Column 3
  m30 : ℝ; m31 : ℝ; m32 : ℝ; m33 : ℝ
  deriving Repr, DecidableEq

namespace Mat4

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // identity matrix
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
--                                                         // matrix multiplication
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Matrix multiplication (A * B) -/
def mul (a b : Mat4) : Mat4 :=
  ⟨-- Column 0
   a.m00*b.m00 + a.m10*b.m01 + a.m20*b.m02 + a.m30*b.m03,
   a.m01*b.m00 + a.m11*b.m01 + a.m21*b.m02 + a.m31*b.m03,
   a.m02*b.m00 + a.m12*b.m01 + a.m22*b.m02 + a.m32*b.m03,
   a.m03*b.m00 + a.m13*b.m01 + a.m23*b.m02 + a.m33*b.m03,
   -- Column 1
   a.m00*b.m10 + a.m10*b.m11 + a.m20*b.m12 + a.m30*b.m13,
   a.m01*b.m10 + a.m11*b.m11 + a.m21*b.m12 + a.m31*b.m13,
   a.m02*b.m10 + a.m12*b.m11 + a.m22*b.m12 + a.m32*b.m13,
   a.m03*b.m10 + a.m13*b.m11 + a.m23*b.m12 + a.m33*b.m13,
   -- Column 2
   a.m00*b.m20 + a.m10*b.m21 + a.m20*b.m22 + a.m30*b.m23,
   a.m01*b.m20 + a.m11*b.m21 + a.m21*b.m22 + a.m31*b.m23,
   a.m02*b.m20 + a.m12*b.m21 + a.m22*b.m22 + a.m32*b.m23,
   a.m03*b.m20 + a.m13*b.m21 + a.m23*b.m22 + a.m33*b.m23,
   -- Column 3
   a.m00*b.m30 + a.m10*b.m31 + a.m20*b.m32 + a.m30*b.m33,
   a.m01*b.m30 + a.m11*b.m31 + a.m21*b.m32 + a.m31*b.m33,
   a.m02*b.m30 + a.m12*b.m31 + a.m22*b.m32 + a.m32*b.m33,
   a.m03*b.m30 + a.m13*b.m31 + a.m23*b.m32 + a.m33*b.m33⟩

/-- Identity is left identity for multiplication -/
theorem identity_mul (m : Mat4) : mul identity m = m := by
  simp only [mul, identity]
  constructor <;> ring

/-- Identity is right identity for multiplication -/
theorem mul_identity (m : Mat4) : mul m identity = m := by
  simp only [mul, identity]
  constructor <;> ring

/-- Matrix multiplication is associative -/
theorem mul_assoc (a b c : Mat4) : mul (mul a b) c = mul a (mul b c) := by
  simp only [mul]
  constructor <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // transform builders
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Translation matrix -/
def translate (x y z : ℝ) : Mat4 :=
  ⟨1, 0, 0, 0,
   0, 1, 0, 0,
   0, 0, 1, 0,
   x, y, z, 1⟩

/-- Scale matrix -/
def scale (x y z : ℝ) : Mat4 :=
  ⟨x, 0, 0, 0,
   0, y, 0, 0,
   0, 0, z, 0,
   0, 0, 0, 1⟩

/-- Uniform scale matrix -/
def uniformScale (s : ℝ) : Mat4 :=
  scale s s s

/-- Translation by zero is identity -/
theorem translate_zero : translate 0 0 0 = identity := by
  simp only [translate, identity]

/-- Uniform scale by 1 is identity -/
theorem scale_one : uniformScale 1 = identity := by
  simp only [uniformScale, scale, identity]

/-- Translation composition -/
theorem translate_compose (x1 y1 z1 x2 y2 z2 : ℝ) :
    mul (translate x1 y1 z1) (translate x2 y2 z2) = translate (x1 + x2) (y1 + y2) (z1 + z2) := by
  simp only [mul, translate]
  constructor <;> ring

/-- Scale composition -/
theorem scale_compose (x1 y1 z1 x2 y2 z2 : ℝ) :
    mul (scale x1 y1 z1) (scale x2 y2 z2) = scale (x1 * x2) (y1 * y2) (z1 * z2) := by
  simp only [mul, scale]
  constructor <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // vector transformation
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Transform a point (w=1) -/
def transformPoint (m : Mat4) (v : Vec3) : Vec3 :=
  ⟨m.m00*v.x + m.m10*v.y + m.m20*v.z + m.m30,
   m.m01*v.x + m.m11*v.y + m.m21*v.z + m.m31,
   m.m02*v.x + m.m12*v.y + m.m22*v.z + m.m32⟩

/-- Transform a direction (w=0, no translation) -/
def transformDir (m : Mat4) (v : Vec3) : Vec3 :=
  ⟨m.m00*v.x + m.m10*v.y + m.m20*v.z,
   m.m01*v.x + m.m11*v.y + m.m21*v.z,
   m.m02*v.x + m.m12*v.y + m.m22*v.z⟩

/-- Identity transform preserves points -/
theorem identity_transform_point (v : Vec3) : transformPoint identity v = v := by
  simp only [transformPoint, identity]
  constructor <;> ring

/-- Identity transform preserves directions -/
theorem identity_transform_dir (v : Vec3) : transformDir identity v = v := by
  simp only [transformDir, identity]
  constructor <;> ring

/-- Translation moves points -/
theorem translate_point (x y z : ℝ) (v : Vec3) :
    transformPoint (translate x y z) v = Vec3.add v ⟨x, y, z⟩ := by
  simp only [transformPoint, translate, Vec3.add]
  constructor <;> ring

/-- Translation doesn't affect directions -/
theorem translate_dir (x y z : ℝ) (v : Vec3) :
    transformDir (translate x y z) v = v := by
  simp only [transformDir, translate]
  constructor <;> ring

/-- Transform composition matches matrix multiplication -/
theorem transform_compose (a b : Mat4) (v : Vec3) :
    transformPoint (mul a b) v = transformPoint a (transformPoint b v) := by
  simp only [transformPoint, mul]
  constructor <;> ring

end Mat4

end Lattice.Math.Mat4
