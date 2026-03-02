/-
  Lattice.Schemas.Imports.CameraTrackingSchema - Camera tracking import format enums and types

  Camera tracking import format enums and types from external tools.

  Source: ui/src/schemas/imports/cameraTracking-schema.ts
-/

namespace Lattice.Schemas.Imports.CameraTrackingSchema

--------------------------------------------------------------------------------
-- Camera Model
--------------------------------------------------------------------------------

/-- Camera model types for lens distortion -/
inductive CameraModel where
  | pinhole
  | radial
  | brown
  | fisheye
  deriving Repr, DecidableEq, Inhabited

def CameraModel.fromString : String → Option CameraModel
  | "pinhole" => some CameraModel.pinhole
  | "radial" => some CameraModel.radial
  | "brown" => some CameraModel.brown
  | "fisheye" => some CameraModel.fisheye
  | _ => none

def CameraModel.toString : CameraModel → String
  | CameraModel.pinhole => "pinhole"
  | CameraModel.radial => "radial"
  | CameraModel.brown => "brown"
  | CameraModel.fisheye => "fisheye"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def maxDimension : Nat := 16384
def maxFrames : Nat := 100000
def maxFPS : Float := 120.0
def maxTrackIDs : Nat := 1000
def maxCameraPoses : Nat := 100000
def maxTrackPoints3D : Nat := 100000
def maxTrackPoints2D : Nat := 1000000
def maxBlenderTracks : Nat := 10000
def maxBlenderPoints : Nat := 10000000
def maxDistortion : Float := 10.0
def maxTangentialDistortion : Float := 1.0
def quaternionTolerance : Float := 0.1

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- 2D vector -/
structure Vector2 where
  x : Float
  y : Float
  deriving Repr, DecidableEq, Inhabited

/-- 3D vector -/
structure Vector3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, DecidableEq, Inhabited

/-- Quaternion rotation -/
structure Quaternion where
  w : Float
  x : Float
  y : Float
  z : Float
  deriving Repr, DecidableEq, Inhabited

/-- RGB color (0-255) -/
structure RGBColor where
  r : Nat
  g : Nat
  b : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Lens distortion coefficients -/
structure Distortion where
  k1 : Option Float
  k2 : Option Float
  k3 : Option Float
  p1 : Option Float
  p2 : Option Float
  deriving Repr, DecidableEq, Inhabited

/-- Camera intrinsics -/
structure CameraIntrinsics where
  focalLength : Float
  principalPoint : Vector2
  width : Nat
  height : Nat
  distortion : Option Distortion
  model : Option CameraModel
  deriving Repr, DecidableEq, Inhabited

/-- Camera pose at a frame -/
structure CameraPose where
  frame : Nat
  position : Vector3
  rotation : Quaternion
  eulerAngles : Option Vector3
  fov : Option Float
  deriving Repr, DecidableEq, Inhabited

/-- Ground plane definition -/
structure GroundPlane where
  normal : Vector3
  origin : Vector3
  up : Vector3
  scale : Option Float
  deriving Repr, DecidableEq, Inhabited

/-- Tracking metadata -/
structure TrackingMetadata where
  sourceWidth : Nat
  sourceHeight : Nat
  frameRate : Float
  frameCount : Nat
  averageError : Option Float
  solveMethod : Option String
  solveDate : Option String
  deriving Repr, DecidableEq, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

def isValidVector2 (v : Vector2) : Bool :=
  v.x.isFinite && v.y.isFinite

def isValidVector3 (v : Vector3) : Bool :=
  v.x.isFinite && v.y.isFinite && v.z.isFinite

/-- Check if quaternion is approximately normalized -/
def isValidQuaternion (q : Quaternion) : Bool :=
  let len := Float.sqrt (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z)
  Float.abs (len - 1.0) < quaternionTolerance

def isValidRGBColor (c : RGBColor) : Bool :=
  c.r <= 255 && c.g <= 255 && c.b <= 255

def isValidDistortion (d : Distortion) : Bool :=
  match d.k1 with
  | some k => k.abs <= maxDistortion
  | none => true
  &&
  match d.k2 with
  | some k => k.abs <= maxDistortion
  | none => true
  &&
  match d.k3 with
  | some k => k.abs <= maxDistortion
  | none => true
  &&
  match d.p1 with
  | some p => p.abs <= maxTangentialDistortion
  | none => true
  &&
  match d.p2 with
  | some p => p.abs <= maxTangentialDistortion
  | none => true

def isValidCameraIntrinsics (ci : CameraIntrinsics) : Bool :=
  ci.focalLength > 0 && ci.focalLength <= 10000 &&
  ci.width > 0 && ci.width <= maxDimension &&
  ci.height > 0 && ci.height <= maxDimension &&
  isValidVector2 ci.principalPoint

def isValidCameraPose (cp : CameraPose) : Bool :=
  cp.frame <= maxFrames &&
  isValidVector3 cp.position &&
  isValidQuaternion cp.rotation

def isValidTrackingMetadata (m : TrackingMetadata) : Bool :=
  m.sourceWidth > 0 && m.sourceWidth <= maxDimension &&
  m.sourceHeight > 0 && m.sourceHeight <= maxDimension &&
  m.frameRate > 0 && m.frameRate <= maxFPS &&
  m.frameCount > 0 && m.frameCount <= maxFrames

end Lattice.Schemas.Imports.CameraTrackingSchema
