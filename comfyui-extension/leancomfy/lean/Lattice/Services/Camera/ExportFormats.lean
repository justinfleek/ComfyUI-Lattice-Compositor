/-
  Lattice.Services.Camera.ExportFormats - Camera Export Format Conversions

  Pure functions for exporting camera data to various AI video formats:
  - MotionCtrl format (4x4 RT matrices)
  - CameraCtrl poses format
  - Focal length to pixel conversion
  - Speed calculation from motion magnitude

  Source: ui/src/services/export/cameraExportFormats.ts (lines 294-1054)
-/

namespace Lattice.Services.Camera.ExportFormats

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 3D vector. -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr

/-- 4x4 matrix. -/
abbrev Mat4 := Array (Array Float)

/-- 3x4 matrix. -/
abbrev Mat3x4 := Array (Array Float)

/-- MotionCtrl pose entry (4x4 RT matrix). -/
structure MotionCtrlPose where
  rt : Mat4
  deriving Repr

/-- CameraCtrl pose entry.
    Format: [time, fx, fy, cx, cy, aspect, 0, 0, w2c[0..11]] -/
abbrev CameraCtrlPoseEntry := Array Float

/-- CameraCtrl poses result. -/
structure CameraCtrlPoses where
  motionType : String
  speed : Nat
  frameLength : Nat
  deriving Repr

/-- Full camera frame export. -/
structure FullCameraFrame where
  frame : Nat
  timestamp : Float
  viewMatrix : Mat4
  projectionMatrix : Mat4
  position : Array Float
  rotation : Array Float
  fov : Float
  focalLength : Float
  focusDistance : Float
  deriving Repr

/-- Full camera export metadata. -/
structure CameraExportMetadata where
  width : Nat
  height : Nat
  fps : Nat
  totalFrames : Nat
  cameraType : String
  filmSize : Float
  deriving Repr

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Default film size (36mm full frame). -/
def defaultFilmSize : Float := 36.0

/-- Minimum tan(halfFov) threshold. -/
def minTanHalfFov : Float := 0.001

--------------------------------------------------------------------------------
-- Focal Length Conversions
--------------------------------------------------------------------------------

/-- Convert focal length (mm) to pixels.
    fx = focalLength * imageWidth / sensorWidth -/
def focalLengthToPixels (focalLengthMM : Float) (imageWidth : Nat) (sensorWidth : Float) : Float :=
  let safeSensor := if sensorWidth > 0.0 then sensorWidth else defaultFilmSize
  (focalLengthMM * imageWidth.toFloat) / safeSensor

/-- Apply zoom to focal length. -/
def applyZoom (focalLength zoom : Float) : Float :=
  focalLength * (if zoom > 0.0 then zoom else 1.0)

--------------------------------------------------------------------------------
-- Speed Calculation
--------------------------------------------------------------------------------

/-- Calculate CameraCtrl speed from motion magnitude.
    Speed is clamped to [0, 100]. -/
def calculateSpeed (hasZoom hasPan hasRotation : Bool)
                   (zoomMagnitude panMagnitude rotationMagnitude : Float) : Nat :=
  let speed := if hasZoom then
    Float.min 100.0 (zoomMagnitude / 5.0)
  else if hasPan then
    Float.min 100.0 (panMagnitude / 3.0)
  else if hasRotation then
    Float.min 100.0 (rotationMagnitude * 2.0)
  else
    0.0
  speed.toUInt32.toNat

--------------------------------------------------------------------------------
-- Pose Entry Construction
--------------------------------------------------------------------------------

/-- Build CameraCtrl pose entry array.
    Format: [time, fx, fy, cx, cy, aspect, 0, 0, w2c[0..11]] -/
def buildCameraCtrlPoseEntry (frame : Nat) (fx fy cx cy aspect : Float)
                              (w2cFlat : Array Float) : CameraCtrlPoseEntry :=
  #[frame.toFloat, fx, fy, cx, cy, aspect, 0.0, 0.0] ++ w2cFlat

/-- Default principal point (image center, normalized). -/
def defaultPrincipalPoint : Float × Float := (0.5, 0.5)

--------------------------------------------------------------------------------
-- Aspect Ratio
--------------------------------------------------------------------------------

/-- Calculate aspect ratio from dimensions. -/
def calculateAspectRatio (width height : Nat) : Float :=
  if height > 0 then width.toFloat / height.toFloat else 1.0

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Validate export dimensions. -/
def validateDimensions (width height : Nat) : Bool :=
  width > 0 && height > 0

/-- Validate FPS. -/
def validateFps (fps : Nat) : Bool :=
  fps > 0

/-- Validate frame count. -/
def validateFrameCount (frameCount : Nat) : Bool :=
  frameCount >= 1

/-- Calculate frame timestamp from frame number and FPS. -/
def frameToTimestamp (frame fps : Nat) : Float :=
  if fps > 0 then frame.toFloat / fps.toFloat else 0.0

--------------------------------------------------------------------------------
-- Export Target Enumeration
--------------------------------------------------------------------------------

/-- Supported export targets. -/
inductive ExportTarget
  | motionctrl
  | motionctrlSvd
  | wan22FunCamera
  | uni3cCamera
  | uni3cMotion
  | animatediffCamerctrl
  | fullMatrices
  deriving Repr, DecidableEq

/-- Parse export target from string. -/
def parseExportTarget (s : String) : ExportTarget :=
  match s with
  | "motionctrl" => ExportTarget.motionctrl
  | "motionctrl-svd" => ExportTarget.motionctrlSvd
  | "wan22-fun-camera" => ExportTarget.wan22FunCamera
  | "uni3c-camera" => ExportTarget.uni3cCamera
  | "uni3c-motion" => ExportTarget.uni3cMotion
  | "animatediff-cameractrl" => ExportTarget.animatediffCamerctrl
  | _ => ExportTarget.fullMatrices

--------------------------------------------------------------------------------
-- String Conversion for Presets
--------------------------------------------------------------------------------

/-- Convert MotionCtrl SVD preset to string. -/
def motionCtrlSVDPresetToString (preset : String) : String :=
  preset

/-- Convert CameraCtrl motion type to string. -/
def cameraCtrlMotionTypeToString (motionType : String) : String :=
  motionType

/-- Capitalize first letter of string. -/
def capitalize (s : String) : String :=
  if s.length > 0 then
    let first := s.get 0
    let rest := s.drop 1
    String.singleton first.toUpper ++ rest
  else
    s

--------------------------------------------------------------------------------
-- Frame Sequence Generation
--------------------------------------------------------------------------------

/-- Generate frame indices for export. -/
def generateFrameIndices (frameCount : Nat) : Array Nat :=
  Array.range frameCount

/-- Check if frame index is valid. -/
def isValidFrameIndex (frame frameCount : Nat) : Bool :=
  frame < frameCount

end Lattice.Services.Camera.ExportFormats
