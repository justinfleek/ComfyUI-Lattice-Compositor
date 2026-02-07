/-
  Lattice.CameraTracking - Camera tracking data import types

  Max 500 lines.

  Source: ui/src/types/cameraTracking.ts (297 lines)
-/

import Lattice.Primitives

namespace Lattice.CameraTracking

open Lattice.Primitives

/-! ## Enumerations -/

/-- Camera tracking coordinate system -/
inductive CoordinateSystem where
  | blender   -- Right-handed, Z-up
  | opengl    -- Right-handed, Y-up
  | unity     -- Left-handed, Y-up
  | unreal    -- Left-handed, Z-up
  deriving Repr, BEq, DecidableEq

/-- Tracking solve quality -/
inductive SolveQuality where
  | poor | fair | good | excellent
  deriving Repr, BEq, DecidableEq

/-- Track point state -/
inductive TrackPointState where
  | tracked | interpolated | keyframed | lost
  deriving Repr, BEq, DecidableEq

/-! ## 2D Track Point -/

/-- 2D track point (normalized coordinates) -/
structure TrackPoint2D where
  frame : FrameNumber
  x : Float         -- 0-1 normalized
  y : Float         -- 0-1 normalized
  confidence : Float -- 0-1
  state : TrackPointState
  x_ge_0 : x ≥ 0
  x_le_1 : x ≤ 1
  x_finite : x.isFinite
  y_ge_0 : y ≥ 0
  y_le_1 : y ≤ 1
  y_finite : y.isFinite
  confidence_ge_0 : confidence ≥ 0
  confidence_le_1 : confidence ≤ 1
  confidence_finite : confidence.isFinite
  deriving Repr

/-! ## 3D Track Point -/

/-- 3D track point in world space -/
structure TrackPoint3D where
  x : Float
  y : Float
  z : Float
  reprojectionError : Float  -- Pixels
  x_finite : x.isFinite
  y_finite : y.isFinite
  z_finite : z.isFinite
  reprojectionError_ge_0 : reprojectionError ≥ 0
  reprojectionError_finite : reprojectionError.isFinite
  deriving Repr

/-! ## Camera Intrinsics -/

/-- Camera intrinsic parameters -/
structure CameraIntrinsics where
  focalLengthX : Float      -- Pixels
  focalLengthY : Float      -- Pixels
  principalPointX : Float   -- Pixels
  principalPointY : Float   -- Pixels
  skew : Float              -- Usually 0
  -- Distortion coefficients (radial k1-k6, tangential p1-p2)
  k1 : Float
  k2 : Float
  k3 : Float
  k4 : Float
  k5 : Float
  k6 : Float
  p1 : Float
  p2 : Float
  -- Image dimensions
  imageWidth : Nat
  imageHeight : Nat
  -- Proofs
  focalLengthX_positive : focalLengthX > 0
  focalLengthX_finite : focalLengthX.isFinite
  focalLengthY_positive : focalLengthY > 0
  focalLengthY_finite : focalLengthY.isFinite
  principalPointX_finite : principalPointX.isFinite
  principalPointY_finite : principalPointY.isFinite
  skew_finite : skew.isFinite
  k1_finite : k1.isFinite
  k2_finite : k2.isFinite
  k3_finite : k3.isFinite
  k4_finite : k4.isFinite
  k5_finite : k5.isFinite
  k6_finite : k6.isFinite
  p1_finite : p1.isFinite
  p2_finite : p2.isFinite
  imageWidth_positive : imageWidth > 0
  imageHeight_positive : imageHeight > 0
  deriving Repr

/-! ## Camera Pose -/

/-- Camera pose (rotation quaternion + translation) -/
structure CameraPose where
  frame : FrameNumber
  -- Rotation quaternion (w, x, y, z)
  rotationW : Float
  rotationX : Float
  rotationY : Float
  rotationZ : Float
  -- Translation
  translationX : Float
  translationY : Float
  translationZ : Float
  -- Proofs
  rotationW_finite : rotationW.isFinite
  rotationX_finite : rotationX.isFinite
  rotationY_finite : rotationY.isFinite
  rotationZ_finite : rotationZ.isFinite
  translationX_finite : translationX.isFinite
  translationY_finite : translationY.isFinite
  translationZ_finite : translationZ.isFinite
  deriving Repr

/-! ## Ground Plane -/

/-- Ground plane definition -/
structure GroundPlane where
  -- Normal vector (unit)
  normalX : Float
  normalY : Float
  normalZ : Float
  -- Distance from origin
  distance : Float
  -- Origin point on plane
  originX : Float
  originY : Float
  originZ : Float
  -- Proofs
  normalX_finite : normalX.isFinite
  normalY_finite : normalY.isFinite
  normalZ_finite : normalZ.isFinite
  distance_finite : distance.isFinite
  originX_finite : originX.isFinite
  originY_finite : originY.isFinite
  originZ_finite : originZ.isFinite
  deriving Repr

/-! ## Camera Tracking Solve -/

/-- Complete camera tracking solve -/
structure CameraTrackingSolve where
  id : NonEmptyString
  name : NonEmptyString
  -- Coordinate system
  coordinateSystem : CoordinateSystem
  -- Camera data
  intrinsics : CameraIntrinsics
  poses : Array CameraPose
  -- Track points
  trackPoints2D : Array (Array TrackPoint2D)  -- Per-tracker, per-frame
  trackPoints3D : Array TrackPoint3D          -- Reconstructed 3D points
  -- Quality
  solveQuality : SolveQuality
  reprojectionErrorMean : Float
  reprojectionErrorMax : Float
  -- Ground plane (optional)
  groundPlane : Option GroundPlane
  -- Scene scale (units per meter)
  sceneScale : Float
  -- Frame range
  startFrame : FrameNumber
  endFrame : FrameNumber
  -- Proofs
  reprojectionErrorMean_ge_0 : reprojectionErrorMean ≥ 0
  reprojectionErrorMean_finite : reprojectionErrorMean.isFinite
  reprojectionErrorMax_ge_0 : reprojectionErrorMax ≥ 0
  reprojectionErrorMax_finite : reprojectionErrorMax.isFinite
  sceneScale_positive : sceneScale > 0
  sceneScale_finite : sceneScale.isFinite
  deriving Repr

/-! ## COLMAP Format Types -/

namespace COLMAP

/-- COLMAP camera model -/
inductive CameraModel where
  | simple_pinhole
  | pinhole
  | simple_radial
  | radial
  | opencv
  | opencv_fisheye
  | full_opencv
  | fov
  | simple_radial_fisheye
  | radial_fisheye
  | thin_prism_fisheye
  deriving Repr, BEq, DecidableEq

/-- COLMAP camera entry -/
structure CameraEntry where
  cameraId : Nat
  model : CameraModel
  width : Nat
  height : Nat
  params : Array Float  -- Model-dependent parameters
  width_positive : width > 0
  height_positive : height > 0
  deriving Repr

/-- COLMAP image entry -/
structure ImageEntry where
  imageId : Nat
  quaternionW : Float
  quaternionX : Float
  quaternionY : Float
  quaternionZ : Float
  translationX : Float
  translationY : Float
  translationZ : Float
  cameraId : Nat
  name : NonEmptyString
  points2D : Array (Float × Float × Nat)  -- (x, y, point3DId)
  deriving Repr

/-- COLMAP 3D point entry -/
structure Point3DEntry where
  point3DId : Nat
  x : Float
  y : Float
  z : Float
  r : Nat  -- 0-255
  g : Nat
  b : Nat
  error : Float
  trackIds : Array (Nat × Nat)  -- (imageId, point2DIdx)
  deriving Repr

end COLMAP

/-! ## Blender Format Types -/

namespace Blender

/-- Blender tracking marker -/
structure TrackingMarker where
  frame : FrameNumber
  coX : Float   -- Corner coordinates (normalized)
  coY : Float
  isEnabled : Bool
  deriving Repr

/-- Blender tracking track -/
structure TrackingTrack where
  name : NonEmptyString
  markers : Array TrackingMarker
  hasBundle : Bool
  bundleX : Option Float
  bundleY : Option Float
  bundleZ : Option Float
  deriving Repr

/-- Blender camera solve data -/
structure CameraSolveData where
  focalLength : Float       -- mm
  sensorWidth : Float       -- mm
  sensorHeight : Float      -- mm
  principalPointX : Float   -- Normalized offset from center
  principalPointY : Float
  k1 : Float
  k2 : Float
  k3 : Float
  tracks : Array TrackingTrack
  focalLength_positive : focalLength > 0
  focalLength_finite : focalLength.isFinite
  sensorWidth_positive : sensorWidth > 0
  sensorWidth_finite : sensorWidth.isFinite
  sensorHeight_positive : sensorHeight > 0
  sensorHeight_finite : sensorHeight.isFinite
  deriving Repr

end Blender

end Lattice.CameraTracking
