/-
  Lattice.Schemas.Exports.CameraSchema

  Camera export format enums and types.

  Source: ui/src/schemas/exports/camera-schema.ts
-/

namespace Lattice.Schemas.Exports.CameraSchema

--------------------------------------------------------------------------------
-- Camera Format
--------------------------------------------------------------------------------

/-- Camera export format options -/
inductive CameraFormat where
  | motionctrl
  | wan_move
  | uni3c
  | cameractrl
  | blender
  | fbx
  deriving Repr, DecidableEq, Inhabited

def cameraFormatFromString : String → Option CameraFormat
  | "motionctrl" => some .motionctrl
  | "wan-move" => some .wan_move
  | "uni3c" => some .uni3c
  | "cameractrl" => some .cameractrl
  | "blender" => some .blender
  | "fbx" => some .fbx
  | _ => Option.none

def cameraFormatToString : CameraFormat → String
  | .motionctrl => "motionctrl"
  | .wan_move => "wan-move"
  | .uni3c => "uni3c"
  | .cameractrl => "cameractrl"
  | .blender => "blender"
  | .fbx => "fbx"

--------------------------------------------------------------------------------
-- Coordinate System
--------------------------------------------------------------------------------

/-- Coordinate system conventions -/
inductive CoordinateSystem where
  | opengl   -- Y-up, right-handed
  | opencv   -- Y-down, right-handed
  | blender  -- Z-up, right-handed
  | unity    -- Y-up, left-handed
  deriving Repr, DecidableEq, Inhabited

def coordinateSystemFromString : String → Option CoordinateSystem
  | "opengl" => some .opengl
  | "opencv" => some .opencv
  | "blender" => some .blender
  | "unity" => some .unity
  | _ => Option.none

def coordinateSystemToString : CoordinateSystem → String
  | .opengl => "opengl"
  | .opencv => "opencv"
  | .blender => "blender"
  | .unity => "unity"

--------------------------------------------------------------------------------
-- Euler Order
--------------------------------------------------------------------------------

/-- Euler rotation order options -/
inductive EulerOrder where
  | XYZ
  | YXZ
  | ZXY
  | ZYX
  | XZY
  | YZX
  deriving Repr, DecidableEq, Inhabited

def eulerOrderFromString : String → Option EulerOrder
  | "XYZ" => some .XYZ
  | "YXZ" => some .YXZ
  | "ZXY" => some .ZXY
  | "ZYX" => some .ZYX
  | "XZY" => some .XZY
  | "YZX" => some .YZX
  | _ => Option.none

def eulerOrderToString : EulerOrder → String
  | .XYZ => "XYZ"
  | .YXZ => "YXZ"
  | .ZXY => "ZXY"
  | .ZYX => "ZYX"
  | .XZY => "XZY"
  | .YZX => "YZX"

--------------------------------------------------------------------------------
-- Camera Interpolation
--------------------------------------------------------------------------------

/-- Camera interpolation options -/
inductive CameraInterpolation where
  | linear
  | bezier
  | spline
  deriving Repr, DecidableEq, Inhabited

def cameraInterpolationFromString : String → Option CameraInterpolation
  | "linear" => some .linear
  | "bezier" => some .bezier
  | "spline" => some .spline
  | _ => Option.none

def cameraInterpolationToString : CameraInterpolation → String
  | .linear => "linear"
  | .bezier => "bezier"
  | .spline => "spline"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- 3D position -/
structure Position3D where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- Camera intrinsic parameters -/
structure CameraIntrinsics where
  focalLength : Float
  sensorWidth : Option Float
  sensorHeight : Option Float
  fov : Float
  aspectRatio : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_FOCAL_LENGTH : Float := 10000.0
def MAX_SENSOR_SIZE : Float := 100.0
def MAX_FOV : Float := 180.0
def MAX_ASPECT_RATIO : Float := 10.0
def MAX_ROTATION_DEGREES : Float := 360.0
def MAX_TIMESTAMP : Float := 86400.0  -- 24 hours
def QUATERNION_NORMALIZATION_TOLERANCE : Float := 0.1

end Lattice.Schemas.Exports.CameraSchema
