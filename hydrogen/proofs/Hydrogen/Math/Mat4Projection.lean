/-
  Hydrogen.Math.Mat4Projection
  
  Projection matrices for 3D rendering: perspective and orthographic.
  
  ZERO-LATENCY INVARIANTS:
    1. All projection matrices are invertible (det ≠ 0 for valid params)
    2. Perspective projection preserves straight lines
    3. Orthographic projection preserves parallel lines
    4. Both map view frustum/box to normalized device coordinates [-1,1]³
  
  These are the final matrices in the MVP chain: Projection × View × Model
  
  Status: FOUNDATIONAL - Required for all 3D rendering.
-/

import Hydrogen.Math.Mat4

namespace Hydrogen.Math

namespace Mat4

-- ═══════════════════════════════════════════════════════════════════════════════
-- PERSPECTIVE PROJECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Perspective Projection

Creates a perspective projection matrix that maps the view frustum to
normalized device coordinates (NDC).

Parameters:
- fov: Vertical field of view in radians
- aspect: Width / height aspect ratio
- near: Near clipping plane distance (positive)
- far: Far clipping plane distance (positive, far > near)

The frustum is symmetric around the view axis.
This matches WebGL/WebGPU conventions with z ∈ [-1, 1] in NDC.
-/

/-- Perspective projection matrix (symmetric frustum, WebGL conventions) -/
noncomputable def makePerspective (fov aspect near far : ℝ) : Mat4 :=
  let tanHalfFov := Real.tan (fov / 2)
  let f := 1 / tanHalfFov
  let nf := 1 / (near - far)
  ⟨f / aspect, 0, 0, 0,
   0, f, 0, 0,
   0, 0, (far + near) * nf, -1,
   0, 0, 2 * far * near * nf, 0⟩

/-- Perspective projection from frustum bounds (asymmetric, general case) -/
noncomputable def makeFrustum (left right bottom top near far : ℝ) : Mat4 :=
  let rl := 1 / (right - left)
  let tb := 1 / (top - bottom)
  let nf := 1 / (near - far)
  ⟨2 * near * rl, 0, 0, 0,
   0, 2 * near * tb, 0, 0,
   (right + left) * rl, (top + bottom) * tb, (far + near) * nf, -1,
   0, 0, 2 * far * near * nf, 0⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- ORTHOGRAPHIC PROJECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Orthographic Projection

Creates an orthographic projection matrix that maps a rectangular box to
normalized device coordinates (NDC).

Parameters define the visible box in view space:
- left, right: X bounds
- bottom, top: Y bounds  
- near, far: Z bounds (positive distances from camera)

Orthographic projection preserves parallel lines and has no perspective
foreshortening. Used for 2D rendering, UI, CAD, and isometric views.
-/

/-- Orthographic projection matrix -/
noncomputable def makeOrthographic (left right bottom top near far : ℝ) : Mat4 :=
  let rl := 1 / (right - left)
  let tb := 1 / (top - bottom)
  let nf := 1 / (near - far)
  ⟨2 * rl, 0, 0, 0,
   0, 2 * tb, 0, 0,
   0, 0, 2 * nf, 0,
   -(right + left) * rl, -(top + bottom) * tb, (far + near) * nf, 1⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- LOOK-AT MATRIX (View Matrix Helper)
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Look-At Matrix

Creates a view matrix that positions the camera at `eye`, looking at `center`,
with `up` defining the upward direction.

This is commonly composed with a projection matrix:
  Projection × LookAt × Model = MVP
-/

/-- Look-at view matrix from eye position, target center, and up vector -/
noncomputable def makeLookAt (eyeX eyeY eyeZ centerX centerY centerZ upX upY upZ : ℝ) : Mat4 :=
  -- Forward direction (from eye to center, normalized)
  let fX := centerX - eyeX
  let fY := centerY - eyeY
  let fZ := centerZ - eyeZ
  let fLen := Real.sqrt (fX * fX + fY * fY + fZ * fZ)
  let fX := fX / fLen
  let fY := fY / fLen
  let fZ := fZ / fLen
  -- Right direction (cross product of forward and up, normalized)
  let sX := fY * upZ - fZ * upY
  let sY := fZ * upX - fX * upZ
  let sZ := fX * upY - fY * upX
  let sLen := Real.sqrt (sX * sX + sY * sY + sZ * sZ)
  let sX := sX / sLen
  let sY := sY / sLen
  let sZ := sZ / sLen
  -- True up direction (cross product of right and forward)
  let uX := sY * fZ - sZ * fY
  let uY := sZ * fX - sX * fZ
  let uZ := sX * fY - sY * fX
  -- Rotation matrix (transposed because we're inverting the camera transform)
  -- Translation component (dot products with eye position)
  ⟨sX, uX, -fX, 0,
   sY, uY, -fY, 0,
   sZ, uZ, -fZ, 0,
   -(sX * eyeX + sY * eyeY + sZ * eyeZ),
   -(uX * eyeX + uY * eyeY + uZ * eyeZ),
   fX * eyeX + fY * eyeY + fZ * eyeZ, 1⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROJECTION PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Projection Properties

Key properties of projection matrices that enable correct rendering.
-/

/-- Orthographic projection is invertible for non-degenerate bounds -/
theorem makeOrthographic_invertible {left right bottom top near far : ℝ}
    (hlr : left ≠ right) (hbt : bottom ≠ top) (hnf : near ≠ far) :
    IsInvertible (makeOrthographic left right bottom top near far) := by
  simp only [IsInvertible, makeOrthographic, det, det3]
  have h1 : right - left ≠ 0 := sub_ne_zero.mpr (Ne.symm hlr)
  have h2 : top - bottom ≠ 0 := sub_ne_zero.mpr (Ne.symm hbt)
  have h3 : near - far ≠ 0 := sub_ne_zero.mpr hnf
  have inv1 : (right - left)⁻¹ ≠ 0 := inv_ne_zero h1
  have inv2 : (top - bottom)⁻¹ ≠ 0 := inv_ne_zero h2
  have inv3 : (near - far)⁻¹ ≠ 0 := inv_ne_zero h3
  -- Simplify all the 0* and *0 terms away, and normalize arithmetic
  simp only [mul_zero, zero_mul, sub_zero, mul_one, one_div]
  ring_nf
  -- Goal: (r-l)⁻¹ * (t-b)⁻¹ * (n-f)⁻¹ * 8 ≠ 0
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  have step1 : (right - left)⁻¹ * (top - bottom)⁻¹ ≠ 0 := mul_ne_zero inv1 inv2
  have step2 : (right - left)⁻¹ * (top - bottom)⁻¹ * (near - far)⁻¹ ≠ 0 := mul_ne_zero step1 inv3
  exact mul_ne_zero step2 h8

/-- Symmetric orthographic projection centered at origin -/
noncomputable def makeOrthographicSymmetric (width height near far : ℝ) : Mat4 :=
  makeOrthographic (-width/2) (width/2) (-height/2) (height/2) near far

/-- Determinant of symmetric orthographic projection -/
theorem det_makeOrthographicSymmetric {width height near far : ℝ}
    (hw : width ≠ 0) (hh : height ≠ 0) (hnf : near ≠ far) :
    det (makeOrthographicSymmetric width height near far) ≠ 0 := by
  simp only [makeOrthographicSymmetric]
  apply makeOrthographic_invertible
  · simp only [ne_eq, neg_div]
    intro h
    have : width = 0 := by linarith
    exact hw this
  · simp only [ne_eq, neg_div]
    intro h
    have : height = 0 := by linarith
    exact hh this
  · exact hnf

end Mat4

end Hydrogen.Math
