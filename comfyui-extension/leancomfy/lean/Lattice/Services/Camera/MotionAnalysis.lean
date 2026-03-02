/-
  Lattice.Services.Camera.MotionAnalysis - Camera Motion Pattern Detection

  Pure functions for analyzing camera motion patterns:
  - Pan, zoom, orbit, rotation detection
  - Motion magnitude calculations
  - Motion type classification for export formats

  Source: ui/src/services/export/cameraExportFormats.ts (lines 398-696)
-/

namespace Lattice.Services.Camera.MotionAnalysis

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 3D vector. -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr

/-- Camera keyframe with position and orientation. -/
structure CameraKeyframe where
  frame : Nat
  position : Option Vec3
  orientation : Option Vec3
  deriving Repr

/-- Pan direction. -/
inductive PanDirection
  | up | down | left | right
  deriving Repr, DecidableEq

/-- Zoom direction. -/
inductive ZoomDirection
  | zoomIn | zoomOut
  deriving Repr, DecidableEq

/-- Orbit direction. -/
inductive OrbitDirection
  | orbitLeft | orbitRight
  deriving Repr, DecidableEq

/-- Camera motion analysis result. -/
structure CameraMotionAnalysis where
  hasPan : Bool
  panDirection : Option PanDirection
  panMagnitude : Float
  hasZoom : Bool
  zoomDirection : Option ZoomDirection
  zoomMagnitude : Float
  hasOrbit : Bool
  orbitDirection : Option OrbitDirection
  orbitMagnitude : Float
  hasRotation : Bool
  rotationMagnitude : Float
  deriving Repr

--------------------------------------------------------------------------------
-- Constants/Thresholds
--------------------------------------------------------------------------------

/-- Movement threshold for pan detection. -/
def panThreshold : Float := 30.0

/-- Movement threshold for zoom detection. -/
def zoomThreshold : Float := 50.0

/-- Rotation threshold for orbit detection (degrees). -/
def orbitThreshold : Float := 20.0

/-- Rotation threshold for rotation detection (degrees). -/
def rotationThreshold : Float := 5.0

/-- Default position (origin). -/
def defaultPosition : Vec3 := { x := 0.0, y := 0.0, z := 0.0 }

--------------------------------------------------------------------------------
-- Motion Delta Calculations
--------------------------------------------------------------------------------

/-- Get position with default fallback. -/
def getPosition (kf : CameraKeyframe) : Vec3 :=
  match kf.position with
  | some pos => pos
  | none => defaultPosition

/-- Get orientation with default fallback. -/
def getOrientation (kf : CameraKeyframe) : Vec3 :=
  match kf.orientation with
  | some ori => ori
  | none => defaultPosition

/-- Calculate delta between first and last keyframe positions. -/
def calculatePositionDelta (first last : CameraKeyframe) : Vec3 :=
  let firstPos := getPosition first
  let lastPos := getPosition last
  { x := lastPos.x - firstPos.x
  , y := lastPos.y - firstPos.y
  , z := lastPos.z - firstPos.z
  }

/-- Calculate delta between first and last keyframe orientations. -/
def calculateOrientationDelta (first last : CameraKeyframe) : Vec3 :=
  let firstOri := getOrientation first
  let lastOri := getOrientation last
  { x := lastOri.x - firstOri.x
  , y := lastOri.y - firstOri.y
  , z := lastOri.z - firstOri.z
  }

--------------------------------------------------------------------------------
-- Pan Detection
--------------------------------------------------------------------------------

/-- Detect pan direction from position delta. -/
def detectPanDirection (deltaX deltaY : Float) : Option PanDirection :=
  let absX := Float.abs deltaX
  let absY := Float.abs deltaY
  if absX > panThreshold || absY > panThreshold then
    if absX > absY then
      some (if deltaX > 0.0 then PanDirection.right else PanDirection.left)
    else
      some (if deltaY > 0.0 then PanDirection.down else PanDirection.up)
  else
    none

/-- Calculate pan magnitude. -/
def calculatePanMagnitude (deltaX deltaY : Float) : Float :=
  Float.max (Float.abs deltaX) (Float.abs deltaY)

--------------------------------------------------------------------------------
-- Zoom Detection
--------------------------------------------------------------------------------

/-- Detect zoom direction from Z delta.
    Negative Z delta = moving toward origin = zoom in. -/
def detectZoomDirection (deltaZ : Float) : Option ZoomDirection :=
  if Float.abs deltaZ > zoomThreshold then
    some (if deltaZ < 0.0 then ZoomDirection.zoomIn else ZoomDirection.zoomOut)
  else
    none

--------------------------------------------------------------------------------
-- Orbit Detection
--------------------------------------------------------------------------------

/-- Detect orbit direction.
    Orbit = rotation around Y with position change. -/
def detectOrbitDirection (deltaRy deltaX : Float) : Option OrbitDirection :=
  if Float.abs deltaRy > orbitThreshold && Float.abs deltaX > panThreshold then
    some (if deltaRy > 0.0 then OrbitDirection.orbitRight else OrbitDirection.orbitLeft)
  else
    none

--------------------------------------------------------------------------------
-- Full Motion Analysis
--------------------------------------------------------------------------------

/-- Empty motion analysis (static camera). -/
def emptyMotionAnalysis : CameraMotionAnalysis :=
  { hasPan := false
  , panDirection := none
  , panMagnitude := 0.0
  , hasZoom := false
  , zoomDirection := none
  , zoomMagnitude := 0.0
  , hasOrbit := false
  , orbitDirection := none
  , orbitMagnitude := 0.0
  , hasRotation := false
  , rotationMagnitude := 0.0
  }

/-- Analyze camera motion from keyframes. -/
def analyzeCameraMotion (keyframes : Array CameraKeyframe) : CameraMotionAnalysis :=
  if keyframes.size < 2 then emptyMotionAnalysis
  else
    let first := keyframes[0]!
    let last := keyframes[keyframes.size - 1]!

    let posDelta := calculatePositionDelta first last
    let oriDelta := calculateOrientationDelta first last

    let panDir := detectPanDirection posDelta.x posDelta.y
    let zoomDir := detectZoomDirection posDelta.z
    let orbitDir := detectOrbitDirection oriDelta.y posDelta.x

    { hasPan := panDir.isSome
    , panDirection := panDir
    , panMagnitude := calculatePanMagnitude posDelta.x posDelta.y
    , hasZoom := zoomDir.isSome
    , zoomDirection := zoomDir
    , zoomMagnitude := Float.abs posDelta.z
    , hasOrbit := orbitDir.isSome
    , orbitDirection := orbitDir
    , orbitMagnitude := Float.abs oriDelta.y
    , hasRotation := Float.abs oriDelta.y > rotationThreshold
    , rotationMagnitude := Float.abs oriDelta.y
    }

--------------------------------------------------------------------------------
-- MotionCtrl SVD Preset Detection
--------------------------------------------------------------------------------

/-- MotionCtrl-SVD preset. -/
inductive MotionCtrlSVDPreset
  | static
  | zoomIn | zoomOut
  | rotateCW | rotateCCW
  | panLeft | panRight | panUp | panDown
  deriving Repr, DecidableEq

/-- Detect MotionCtrl-SVD preset from keyframes. -/
def detectMotionCtrlSVDPreset (keyframes : Array CameraKeyframe) : MotionCtrlSVDPreset :=
  if keyframes.size < 2 then MotionCtrlSVDPreset.static
  else
    let first := keyframes[0]!
    let last := keyframes[keyframes.size - 1]!
    let posDelta := calculatePositionDelta first last
    let oriDelta := calculateOrientationDelta first last

    let threshold := 50.0

    -- Check zoom (by distance to origin, not raw Z)
    if Float.abs posDelta.z > threshold then
      let distStart := Float.abs (getPosition first).z
      let distEnd := Float.abs (getPosition last).z
      if distEnd < distStart then MotionCtrlSVDPreset.zoomIn
      else MotionCtrlSVDPreset.zoomOut
    -- Check rotation
    else if Float.abs oriDelta.y > 15.0 then
      if oriDelta.y > 0.0 then MotionCtrlSVDPreset.rotateCW
      else MotionCtrlSVDPreset.rotateCCW
    -- Check pan X
    else if Float.abs posDelta.x > threshold then
      if posDelta.x > 0.0 then MotionCtrlSVDPreset.panRight
      else MotionCtrlSVDPreset.panLeft
    -- Check pan Y
    else if Float.abs posDelta.y > threshold then
      if posDelta.y > 0.0 then MotionCtrlSVDPreset.panDown
      else MotionCtrlSVDPreset.panUp
    else
      MotionCtrlSVDPreset.static

--------------------------------------------------------------------------------
-- CameraCtrl Motion Type Detection
--------------------------------------------------------------------------------

/-- AnimateDiff CameraCtrl motion type. -/
inductive CameraCtrlMotionType
  | static
  | moveForward | moveBackward
  | moveLeft | moveRight | moveUp | moveDown
  | rotateLeft | rotateRight | rotateUp | rotateDown
  | rollLeft | rollRight
  deriving Repr, DecidableEq

/-- Detect CameraCtrl motion type from keyframes. -/
def detectCameraCtrlMotionType (keyframes : Array CameraKeyframe) : CameraCtrlMotionType :=
  let motion := analyzeCameraMotion keyframes
  if !motion.hasPan && !motion.hasZoom && !motion.hasRotation then
    CameraCtrlMotionType.static
  else if motion.hasZoom then
    match motion.zoomDirection with
    | some ZoomDirection.zoomIn => CameraCtrlMotionType.moveForward
    | some ZoomDirection.zoomOut => CameraCtrlMotionType.moveBackward
    | none => CameraCtrlMotionType.static
  else if motion.hasPan then
    match motion.panDirection with
    | some PanDirection.left => CameraCtrlMotionType.moveLeft
    | some PanDirection.right => CameraCtrlMotionType.moveRight
    | some PanDirection.up => CameraCtrlMotionType.moveUp
    | some PanDirection.down => CameraCtrlMotionType.moveDown
    | none => CameraCtrlMotionType.static
  else if motion.hasRotation && keyframes.size >= 2 then
    let first := keyframes[0]!
    let last := keyframes[keyframes.size - 1]!
    let oriDelta := calculateOrientationDelta first last
    let absRx := Float.abs oriDelta.x
    let absRy := Float.abs oriDelta.y
    let absRz := Float.abs oriDelta.z
    if absRy > absRx && absRy > absRz then
      if oriDelta.y > 0.0 then CameraCtrlMotionType.rotateRight
      else CameraCtrlMotionType.rotateLeft
    else if absRx > absRz then
      if oriDelta.x > 0.0 then CameraCtrlMotionType.rotateDown
      else CameraCtrlMotionType.rotateUp
    else
      if oriDelta.z > 0.0 then CameraCtrlMotionType.rollRight
      else CameraCtrlMotionType.rollLeft
  else
    CameraCtrlMotionType.static

--------------------------------------------------------------------------------
-- Wan 2.2 Fun Camera Preset
--------------------------------------------------------------------------------

/-- Wan 2.2 Fun Camera motion preset. -/
inductive Wan22CameraMotion
  | static
  | zoomIn | zoomOut
  | panUp | panDown | panLeft | panRight
  | orbitalLeft | orbitalRight
  | panUpZoomIn | panUpZoomOut
  | panDownZoomIn | panDownZoomOut
  | panLeftZoomIn | panLeftZoomOut
  | panRightZoomIn | panRightZoomOut
  deriving Repr, DecidableEq

/-- Map motion analysis to Wan 2.2 Fun Camera preset. -/
def mapToWan22FunCamera (keyframes : Array CameraKeyframe) : Wan22CameraMotion :=
  let motion := analyzeCameraMotion keyframes

  -- Priority: Orbit > Zoom+Pan > Zoom > Pan
  if motion.hasOrbit then
    match motion.orbitDirection with
    | some OrbitDirection.orbitLeft => Wan22CameraMotion.orbitalLeft
    | some OrbitDirection.orbitRight => Wan22CameraMotion.orbitalRight
    | none => Wan22CameraMotion.static
  else if motion.hasZoom && motion.hasPan then
    -- Combined zoom + pan
    match (motion.panDirection, motion.zoomDirection) with
    | (some PanDirection.up, some ZoomDirection.zoomIn) => Wan22CameraMotion.panUpZoomIn
    | (some PanDirection.up, some ZoomDirection.zoomOut) => Wan22CameraMotion.panUpZoomOut
    | (some PanDirection.down, some ZoomDirection.zoomIn) => Wan22CameraMotion.panDownZoomIn
    | (some PanDirection.down, some ZoomDirection.zoomOut) => Wan22CameraMotion.panDownZoomOut
    | (some PanDirection.left, some ZoomDirection.zoomIn) => Wan22CameraMotion.panLeftZoomIn
    | (some PanDirection.left, some ZoomDirection.zoomOut) => Wan22CameraMotion.panLeftZoomOut
    | (some PanDirection.right, some ZoomDirection.zoomIn) => Wan22CameraMotion.panRightZoomIn
    | (some PanDirection.right, some ZoomDirection.zoomOut) => Wan22CameraMotion.panRightZoomOut
    | _ => Wan22CameraMotion.static
  else if motion.hasZoom then
    match motion.zoomDirection with
    | some ZoomDirection.zoomIn => Wan22CameraMotion.zoomIn
    | some ZoomDirection.zoomOut => Wan22CameraMotion.zoomOut
    | none => Wan22CameraMotion.static
  else if motion.hasPan then
    match motion.panDirection with
    | some PanDirection.up => Wan22CameraMotion.panUp
    | some PanDirection.down => Wan22CameraMotion.panDown
    | some PanDirection.left => Wan22CameraMotion.panLeft
    | some PanDirection.right => Wan22CameraMotion.panRight
    | none => Wan22CameraMotion.static
  else
    Wan22CameraMotion.static

--------------------------------------------------------------------------------
-- Uni3C Trajectory Type
--------------------------------------------------------------------------------

/-- Uni3C trajectory type. -/
inductive Uni3CTrajType
  | orbit | free1 | custom
  deriving Repr, DecidableEq

/-- Detect Uni3C trajectory type from keyframes. -/
def detectUni3CTrajectoryType (keyframes : Array CameraKeyframe) : Uni3CTrajType :=
  let motion := analyzeCameraMotion keyframes
  if motion.hasOrbit && motion.orbitMagnitude > 45.0 then
    Uni3CTrajType.orbit
  else if motion.hasPan && motion.hasZoom then
    Uni3CTrajType.custom
  else if !motion.hasPan && !motion.hasZoom && !motion.hasOrbit then
    Uni3CTrajType.free1
  else
    Uni3CTrajType.custom

end Lattice.Services.Camera.MotionAnalysis
