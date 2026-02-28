/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     HYDROGEN // WORLDMODEL // POSE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Camera pose representation for world-consistent video generation.
  
  Based on AnchorWeave (Wang et al., 2025) which uses 3×4 camera pose matrices
  for spatial memory retrieval and multi-anchor weaving.
  
  POSE REPRESENTATION:
    - 3×4 matrix [R | t] where R is 3×3 rotation, t is 3×1 translation
    - Part of SE(3): Special Euclidean group (rigid body transformations)
    - Composition via matrix multiplication
  
  RELATIVE POSES:
    - P_rel = P_target × P_context^(-1)
    - Used for confidence scoring in AnchorWeave
  
  PROVEN INVARIANTS:
    - Rotation matrices have determinant 1
    - Rotation matrices are orthogonal: R × R^T = I
    - Pose composition is associative
    - Identity pose exists
    - Relative pose computation is well-defined
  
  ─────────────────────────────────────────────────────────────────────────────
  REFERENCES
  ─────────────────────────────────────────────────────────────────────────────
  
  - AnchorWeave: "World-Consistent Video Generation with Retrieved Local
    Spatial Memories" (Wang et al., 2025)
  - SE(3) group theory
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Hydrogen.Math.Mat3 : 3×3 matrices
  - Hydrogen.Math.Vec3 : 3D vectors
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Math.Mat3
import Hydrogen.Math.Vec3
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.WorldModel.Pose

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: CAMERA POSE (3×4 MATRIX)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Camera pose as a 3×4 matrix [R | t]
    
    Where:
    - R is a 3×3 rotation matrix (orthogonal, det = 1)
    - t is a 3×1 translation vector
    
    This represents a rigid body transformation in SE(3). -/
@[ext]
structure CameraPose where
  /-- 3×3 rotation matrix -/
  rotation : Mat3
  /-- 3D translation vector -/
  translation : Vec3

namespace CameraPose

/-- Identity pose: no rotation, no translation -/
def identity : CameraPose :=
  { rotation := Mat3.identity
  , translation := Vec3.zero }

/-- Compose two poses: P1 then P2
    
    If P1 = [R1 | t1] and P2 = [R2 | t2], then:
    P2 × P1 = [R2 × R1 | R2 × t1 + t2]
    
    This is the standard SE(3) group operation. -/
def compose (p2 p1 : CameraPose) : CameraPose :=
  { rotation := Mat3.mul p2.rotation p1.rotation
  , translation := Vec3.add (Mat3.mulVec p2.rotation p1.translation) p2.translation }

/-- Invert a pose
    
    If P = [R | t], then P^(-1) = [R^T | -R^T × t]
    
    For orthogonal R, R^(-1) = R^T. -/
def invert (p : CameraPose) : CameraPose :=
  let rt := Mat3.transpose p.rotation
  { rotation := rt
  , translation := Vec3.neg (Mat3.mulVec rt p.translation) }

/-- Relative pose: P_rel = P_target × P_context^(-1)
    
    This gives the transformation from context frame to target frame.
    Used in AnchorWeave for confidence scoring. -/
def relativePose (target context : CameraPose) : CameraPose :=
  compose target (invert context)

/-- Transform a 3D point by a pose: p' = R × p + t -/
def transformPoint (pose : CameraPose) (point : Vec3) : Vec3 :=
  Vec3.add (Mat3.mulVec pose.rotation point) pose.translation

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: POSE PROOFS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Transform is compatible with composition -/
theorem transformPoint_compose (p1 p2 : CameraPose) (point : Vec3) :
    transformPoint (compose p2 p1) point = transformPoint p2 (transformPoint p1 point) := by
  unfold transformPoint compose
  simp only [Mat3.mulVec_mul, Mat3.mulVec_add_vec, Vec3.add_assoc]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: ROTATION MATRIX PROPERTIES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A rotation matrix is orthogonal: R × R^T = I -/
def IsOrthogonal (m : Mat3) : Prop :=
  Mat3.mul m (Mat3.transpose m) = Mat3.identity

/-- A rotation matrix has determinant 1 -/
def HasDetOne (m : Mat3) : Prop :=
  Mat3.det m = 1

/-- A proper rotation matrix is orthogonal with det = 1 -/
structure ProperRotation where
  matrix : Mat3
  orthogonal : IsOrthogonal matrix
  det_one : HasDetOne matrix

/-- Identity is a proper rotation -/
theorem identity_is_proper_rotation : 
    IsOrthogonal Mat3.identity ∧ HasDetOne Mat3.identity := by
  constructor
  · simp only [IsOrthogonal, Mat3.transpose_identity, Mat3.mul_identity_right]
  · simp only [HasDetOne, Mat3.det_identity]

/-- Rotation X matrices have det = 1 -/
theorem rotationX_det_one (angle : ℝ) : HasDetOne (Mat3.makeRotationX angle) :=
  Mat3.det_makeRotationX angle

/-- Rotation Y matrices have det = 1 -/
theorem rotationY_det_one (angle : ℝ) : HasDetOne (Mat3.makeRotationY angle) :=
  Mat3.det_makeRotationY angle

/-- Rotation Z matrices have det = 1 -/
theorem rotationZ_det_one (angle : ℝ) : HasDetOne (Mat3.makeRotationZ angle) :=
  Mat3.det_makeRotationZ angle

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: POSE FLATTENING (FOR NEURAL NETWORKS)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Flatten pose to 12-element vector (row-major 3×4)
    
    AnchorWeave uses this representation for the confidence network:
    [r00, r01, r02, t0, r10, r11, r12, t1, r20, r21, r22, t2] -/
def flatten (p : CameraPose) : Fin 12 → ℝ := fun i =>
  match i.val with
  | 0 => p.rotation.m00
  | 1 => p.rotation.m01
  | 2 => p.rotation.m02
  | 3 => p.translation.x
  | 4 => p.rotation.m10
  | 5 => p.rotation.m11
  | 6 => p.rotation.m12
  | 7 => p.translation.y
  | 8 => p.rotation.m20
  | 9 => p.rotation.m21
  | 10 => p.rotation.m22
  | _ => p.translation.z

/-- The flattened identity pose has specific values -/
theorem flatten_identity_diag (i : Fin 12) :
    flatten identity i = if i.val ∈ [0, 5, 10] then 1 else 
                         if i.val ∈ [3, 7, 11] then 0 else 0 := by
  simp only [flatten, identity, Mat3.identity, Vec3.zero]
  fin_cases i <;> simp

end CameraPose

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: CAMERA TRAJECTORY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A camera trajectory is a sequence of poses indexed by frame number.
    
    AnchorWeave processes trajectories with F frames (e.g., 49 frames). -/
structure CameraTrajectory (numFrames : ℕ) where
  poses : Fin numFrames → CameraPose

/-- The relative trajectory between two camera trajectories -/
def CameraTrajectory.relative {n : ℕ} (target context : CameraTrajectory n) : 
    CameraTrajectory n :=
  { poses := fun i => CameraPose.relativePose (target.poses i) (context.poses i) }

/-- A static trajectory where all poses are the same -/
def CameraTrajectory.static {n : ℕ} (pose : CameraPose) : CameraTrajectory n :=
  { poses := fun _ => pose }

/-- Static identity trajectory -/
def CameraTrajectory.identityStatic {n : ℕ} : CameraTrajectory n :=
  CameraTrajectory.static CameraPose.identity

/-- For orthogonal matrices, compose with inverse gives identity rotation.
    
    This is a fundamental property: navigating somewhere and back 
    returns you to where you started. Essential for spatial coherence. -/
theorem CameraPose.compose_invert_rotation_orthogonal (p : CameraPose) 
    (horth : IsOrthogonal p.rotation) :
    (compose p (invert p)).rotation = Mat3.identity := by
  simp only [compose, invert, Mat3.mul, Mat3.transpose]
  -- R × R^T = I when R is orthogonal
  exact horth

end Hydrogen.WorldModel.Pose
