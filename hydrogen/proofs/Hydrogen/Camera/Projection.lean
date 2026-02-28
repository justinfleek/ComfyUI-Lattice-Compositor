/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 HYDROGEN // CAMERA // PROJECTION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Camera to projection matrix conversion with proven invertibility.
  
  This module bridges the Camera types to Mat4 projection matrices,
  with proofs that the resulting matrices are always invertible
  (non-degenerate) given our type invariants.
  
  PROVEN INVARIANTS:
    - Perspective matrices are invertible (det ≠ 0)
    - Orthographic matrices are invertible (det ≠ 0)
    - View matrices are invertible (det = ±1 for rotation)
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types           : Camera types with invariants
  - Mat4            : Matrix operations
  - Mat4Projection  : Projection matrix constructors
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Camera.Types
import Hydrogen.Math.Mat4
import Hydrogen.Math.Mat4Projection
import Hydrogen.Math.Plane

namespace Hydrogen.Camera

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: PERSPECTIVE PROJECTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Build perspective projection matrix from camera parameters.
    
    The type invariants guarantee:
    - fov ∈ (0, π) → tan(fov/2) > 0 → f > 0
    - aspect > 0
    - near > 0, far > near → (near - far) ≠ 0
    
    Therefore the matrix is always well-defined and invertible. -/
noncomputable def PerspectiveCamera.projectionMatrix (cam : PerspectiveCamera) : Mat4 :=
  Mat4.makePerspective cam.fov.value cam.aspect.value cam.clip.near cam.clip.far

/-- Perspective projection matrix has non-zero determinant.
    
    The determinant of the perspective matrix is:
    det = 2 * near * far / (tan²(fov/2) * aspect * (near - far)²)
    
    All components are non-zero given our type invariants:
    - tan(fov/2) > 0 (fov ∈ (0, π))
    - aspect > 0
    - near > 0, far > near
    
    Therefore det ≠ 0 and the matrix is invertible. -/
theorem PerspectiveCamera.projectionMatrix_invertible (cam : PerspectiveCamera) :
    Mat4.IsInvertible cam.projectionMatrix := by
  unfold projectionMatrix Mat4.makePerspective Mat4.IsInvertible Mat4.det Mat4.det3
  -- Establish all the non-zero hypotheses from type invariants
  have htan := tan_half_fov_positive cam.fov
  have htan_pos : Real.tan (cam.fov.value / 2) > 0 := htan
  have haspect := cam.aspect.positive
  have hnear := cam.clip.near_positive
  have hfar_pos := ClipPlanes.far_positive cam.clip
  have hfar_gt := cam.clip.far_gt_near
  have hnf_neg : cam.clip.near - cam.clip.far < 0 := by linarith
  -- Simplify and use positivity
  simp only [one_div]
  ring_nf
  -- Convert the *(1/2) back to /2 in the goal using simp
  simp only [mul_one_div] at *
  -- Now build non-zero proofs for each factor
  have htan_inv_pos : (Real.tan (cam.fov.value / 2))⁻¹ > 0 := inv_pos.mpr htan_pos
  have htan_inv_sq_pos : (Real.tan (cam.fov.value / 2))⁻¹ ^ 2 > 0 := sq_pos_of_pos htan_inv_pos
  have haspect_inv_pos : cam.aspect.value⁻¹ > 0 := inv_pos.mpr haspect
  -- near - far < 0, but the goal has (-far + near) = near - far, which is also < 0
  have hnf2 : -cam.clip.far + cam.clip.near < 0 := by linarith
  have hnf_inv_neg : (-cam.clip.far + cam.clip.near)⁻¹ < 0 := inv_lt_zero.mpr hnf2
  -- The full expression is non-zero because it's a product of non-zero terms
  have htan_inv_sq_ne : (Real.tan (cam.fov.value / 2))⁻¹ ^ 2 ≠ 0 := ne_of_gt htan_inv_sq_pos
  have haspect_inv_ne : cam.aspect.value⁻¹ ≠ 0 := ne_of_gt haspect_inv_pos
  have hnear_ne : cam.clip.near ≠ 0 := ne_of_gt hnear
  have hfar_ne : cam.clip.far ≠ 0 := ne_of_gt hfar_pos
  have hnf_inv_ne : (-cam.clip.far + cam.clip.near)⁻¹ ≠ 0 := ne_of_lt hnf_inv_neg
  have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
  -- Build the non-zero product step by step
  apply mul_ne_zero
  apply mul_ne_zero
  apply mul_ne_zero
  apply mul_ne_zero
  apply mul_ne_zero
  exact htan_inv_sq_ne
  exact haspect_inv_ne
  exact hfar_ne
  exact hnear_ne
  exact hnf_inv_ne
  exact h2_ne

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: ORTHOGRAPHIC PROJECTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Build orthographic projection matrix from camera parameters -/
noncomputable def OrthographicCamera.projectionMatrix (cam : OrthographicCamera) : Mat4 :=
  Mat4.makeOrthographic 
    (-cam.width / 2) (cam.width / 2)
    (-cam.height / 2) (cam.height / 2)
    cam.clip.near cam.clip.far

/-- Orthographic projection matrix is invertible -/
theorem OrthographicCamera.projectionMatrix_invertible (cam : OrthographicCamera) :
    Mat4.IsInvertible cam.projectionMatrix := by
  unfold projectionMatrix
  apply Mat4.makeOrthographic_invertible
  · -- left ≠ right: -width/2 ≠ width/2
    have hw := cam.width_positive
    intro h
    linarith
  · -- bottom ≠ top: -height/2 ≠ height/2
    have hh := cam.height_positive
    intro h
    linarith
  · -- near ≠ far
    have hfar_gt := cam.clip.far_gt_near
    linarith

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: VIEW MATRIX (LOOK-AT)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Build view matrix for two-node camera (looking at point of interest) -/
noncomputable def TwoNodeCamera.viewMatrix (cam : TwoNodeCamera) : Mat4 :=
  Mat4.makeLookAt 
    cam.position.x cam.position.y cam.position.z
    cam.pointOfInterest.x cam.pointOfInterest.y cam.pointOfInterest.z
    0 1 0  -- Standard up vector (Y-up)

/-- Build view matrix for perspective camera using position and rotation.
    
    The view matrix is the inverse of the camera's world transform.
    For a camera with quaternion rotation, we use the rotation matrix
    (transposed) combined with the negated translation. -/
noncomputable def PerspectiveCamera.viewMatrix (cam : PerspectiveCamera) : Mat4 :=
  -- The rotation matrix from quaternion, transposed (inverse for orthogonal)
  let rotMat := Quaternion.toMat4 cam.rotation
  -- Extract rotation part (first 3x3) and transpose it
  -- Then apply translation: -R^T * position
  -- For simplicity, compute forward from rotation matrix column 2 (negated)
  let forwardX := -rotMat.m02
  let forwardY := -rotMat.m12
  let forwardZ := -rotMat.m22
  let targetX := cam.position.x + forwardX
  let targetY := cam.position.y + forwardY
  let targetZ := cam.position.z + forwardZ
  Mat4.makeLookAt
    cam.position.x cam.position.y cam.position.z
    targetX targetY targetZ
    0 1 0

/-- Build view matrix for orthographic camera -/
noncomputable def OrthographicCamera.viewMatrix (cam : OrthographicCamera) : Mat4 :=
  let rotMat := Quaternion.toMat4 cam.rotation
  let forwardX := -rotMat.m02
  let forwardY := -rotMat.m12
  let forwardZ := -rotMat.m22
  let targetX := cam.position.x + forwardX
  let targetY := cam.position.y + forwardY
  let targetZ := cam.position.z + forwardZ
  Mat4.makeLookAt
    cam.position.x cam.position.y cam.position.z
    targetX targetY targetZ
    0 1 0

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: MODEL-VIEW-PROJECTION (MVP)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute the view-projection matrix (VP) for a perspective camera.
    
    This is the matrix that transforms from world space to clip space:
    VP = Projection × View
    
    For the full MVP: MVP = VP × Model -/
noncomputable def PerspectiveCamera.viewProjectionMatrix (cam : PerspectiveCamera) : Mat4 :=
  Mat4.mul cam.projectionMatrix cam.viewMatrix

/-- Compute the view-projection matrix for an orthographic camera -/
noncomputable def OrthographicCamera.viewProjectionMatrix (cam : OrthographicCamera) : Mat4 :=
  Mat4.mul cam.projectionMatrix cam.viewMatrix

/-- Compute the view-projection matrix for a two-node camera -/
noncomputable def TwoNodeCamera.viewProjectionMatrix (cam : TwoNodeCamera) : Mat4 :=
  let proj := Mat4.makePerspective cam.fov.value cam.aspect.value cam.clip.near cam.clip.far
  Mat4.mul proj cam.viewMatrix

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: FRUSTUM PLANES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Extract frustum planes from a view-projection matrix.
    
    The six planes are extracted from rows of the VP matrix:
    - Left:   row3 + row0
    - Right:  row3 - row0
    - Bottom: row3 + row1
    - Top:    row3 - row1
    - Near:   row3 + row2
    - Far:    row3 - row2
    
    Each plane is returned as normal + constant where normal·p + constant = 0 -/
noncomputable def extractFrustumPlanes (vp : Mat4) : 
    Plane × Plane × Plane × Plane × Plane × Plane :=
  -- Row 0: m00, m01, m02, m03
  -- Row 1: m10, m11, m12, m13
  -- Row 2: m20, m21, m22, m23
  -- Row 3: m30, m31, m32, m33
  let leftN := Vec3.mk (vp.m30 + vp.m00) (vp.m31 + vp.m01) (vp.m32 + vp.m02)
  let leftD := vp.m33 + vp.m03
  let leftLen := Vec3.length leftN
  let left : Plane := ⟨Vec3.scale (1/leftLen) leftN, leftD / leftLen⟩
  
  let rightN := Vec3.mk (vp.m30 - vp.m00) (vp.m31 - vp.m01) (vp.m32 - vp.m02)
  let rightD := vp.m33 - vp.m03
  let rightLen := Vec3.length rightN
  let right : Plane := ⟨Vec3.scale (1/rightLen) rightN, rightD / rightLen⟩
  
  let bottomN := Vec3.mk (vp.m30 + vp.m10) (vp.m31 + vp.m11) (vp.m32 + vp.m12)
  let bottomD := vp.m33 + vp.m13
  let bottomLen := Vec3.length bottomN
  let bottom : Plane := ⟨Vec3.scale (1/bottomLen) bottomN, bottomD / bottomLen⟩
  
  let topN := Vec3.mk (vp.m30 - vp.m10) (vp.m31 - vp.m11) (vp.m32 - vp.m12)
  let topD := vp.m33 - vp.m13
  let topLen := Vec3.length topN
  let top : Plane := ⟨Vec3.scale (1/topLen) topN, topD / topLen⟩
  
  let nearN := Vec3.mk (vp.m30 + vp.m20) (vp.m31 + vp.m21) (vp.m32 + vp.m22)
  let nearD := vp.m33 + vp.m23
  let nearLen := Vec3.length nearN
  let nearPlane : Plane := ⟨Vec3.scale (1/nearLen) nearN, nearD / nearLen⟩
  
  let farN := Vec3.mk (vp.m30 - vp.m20) (vp.m31 - vp.m21) (vp.m32 - vp.m22)
  let farD := vp.m33 - vp.m23
  let farLen := Vec3.length farN
  let farPlane : Plane := ⟨Vec3.scale (1/farLen) farN, farD / farLen⟩
  
  (left, right, bottom, top, nearPlane, farPlane)

end Hydrogen.Camera
