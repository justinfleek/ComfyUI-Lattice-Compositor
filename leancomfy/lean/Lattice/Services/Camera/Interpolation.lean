/-
  Lattice.Services.Camera.Interpolation - Camera Keyframe Interpolation

  Pure functions for camera keyframe interpolation:
  - Linear interpolation
  - Angle interpolation with wrapping
  - Keyframe search and blending
  - Camera state interpolation

  Source: ui/src/services/export/cameraExportFormats.ts (lines 28-165)
-/

namespace Lattice.Services.Camera.Interpolation

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 3D vector for position or rotation. -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr

/-- Interpolated camera state. -/
structure InterpolatedCamera where
  position : Vec3
  rotation : Vec3
  focalLength : Float
  zoom : Float
  focusDistance : Float
  deriving Repr

/-- Camera keyframe. -/
structure CameraKeyframe where
  frame : Nat
  position : Option Vec3
  orientation : Option Vec3
  focalLength : Option Float
  zoom : Option Float
  focusDistance : Option Float
  deriving Repr

/-- Base camera with default values. -/
structure BaseCamera where
  position : Vec3
  orientation : Vec3
  focalLength : Float
  zoom : Float
  focusDistance : Float
  deriving Repr

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

/-- Default position at origin. -/
def defaultPosition : Vec3 :=
  { x := 0.0, y := 0.0, z := 0.0 }

/-- Default orientation (no rotation). -/
def defaultOrientation : Vec3 :=
  { x := 0.0, y := 0.0, z := 0.0 }

/-- Default focal length (50mm standard lens). -/
def defaultFocalLength : Float := 50.0

/-- Default zoom (1x). -/
def defaultZoom : Float := 1.0

/-- Default focus distance (meters). -/
def defaultFocusDistance : Float := 10.0

/-- Default base camera. -/
def defaultBaseCamera : BaseCamera :=
  { position := defaultPosition
  , orientation := defaultOrientation
  , focalLength := defaultFocalLength
  , zoom := defaultZoom
  , focusDistance := defaultFocusDistance
  }

--------------------------------------------------------------------------------
-- Linear Interpolation
--------------------------------------------------------------------------------

/-- Linear interpolation between two values. -/
def lerp (a b t : Float) : Float :=
  a + (b - a) * t

/-- Interpolate Vec3 components. -/
def lerpVec3 (a b : Vec3) (t : Float) : Vec3 :=
  { x := lerp a.x b.x t
  , y := lerp a.y b.y t
  , z := lerp a.z b.z t
  }

--------------------------------------------------------------------------------
-- Angle Interpolation
--------------------------------------------------------------------------------

/-- Normalize angle to [0, 360) range. -/
def normalizeAngle (angle : Float) : Float :=
  let a := angle % 360.0
  if a < 0.0 then a + 360.0 else a

/-- Calculate shortest angle difference.
    Takes the shortest path around the circle. -/
def angleDiff (a b : Float) : Float :=
  let diff := b - a
  let adjusted := if diff > 180.0 then diff - 360.0
                  else if diff < -180.0 then diff + 360.0
                  else diff
  adjusted

/-- Interpolate between two angles, taking shortest path.
    Result normalized to [0, 360] range. -/
def lerpAngle (a b t : Float) : Float :=
  let diff := angleDiff a b
  let result := a + diff * t
  -- Normalize to [0, 360]
  let normalized := if result > 360.0 then result - 360.0
                    else if result < 0.0 then result + 360.0
                    else result
  normalized

/-- Interpolate rotation vector with angle wrapping. -/
def lerpRotation (a b : Vec3) (t : Float) : Vec3 :=
  { x := lerpAngle a.x b.x t
  , y := lerpAngle a.y b.y t
  , z := lerpAngle a.z b.z t
  }

--------------------------------------------------------------------------------
-- Keyframe Search
--------------------------------------------------------------------------------

/-- Find surrounding keyframes for a given frame.
    Returns (previous keyframe, next keyframe). -/
def findSurroundingKeyframes (keyframes : Array CameraKeyframe) (frame : Nat)
    : Option (CameraKeyframe × CameraKeyframe) :=
  if keyframes.size == 0 then none
  else
    let sorted := keyframes.qsort (fun a b => a.frame < b.frame)
    let first := sorted[0]!
    let last := sorted[sorted.size - 1]!

    let prev := sorted.foldl (fun acc kf =>
      if kf.frame <= frame then kf else acc) first
    let next := sorted.foldl (fun acc kf =>
      if kf.frame >= frame && acc.frame < frame then kf else acc) last

    some (prev, next)

/-- Calculate interpolation factor between two frames. -/
def calculateT (prevFrame nextFrame currentFrame : Nat) : Float :=
  if prevFrame == nextFrame then 0.0
  else
    (currentFrame.toFloat - prevFrame.toFloat) /
    (nextFrame.toFloat - prevFrame.toFloat)

--------------------------------------------------------------------------------
-- Value Extraction with Defaults
--------------------------------------------------------------------------------

/-- Get position from keyframe with default fallback. -/
def getPosition (kf : CameraKeyframe) (default : Vec3) : Vec3 :=
  match kf.position with
  | some pos => pos
  | none => default

/-- Get orientation from keyframe with default fallback. -/
def getOrientation (kf : CameraKeyframe) (default : Vec3) : Vec3 :=
  match kf.orientation with
  | some ori => ori
  | none => default

/-- Get focal length from keyframe with default fallback. -/
def getFocalLength (kf : CameraKeyframe) (default : Float) : Float :=
  match kf.focalLength with
  | some fl => if fl > 0.0 then fl else default
  | none => default

/-- Get zoom from keyframe with default fallback. -/
def getZoom (kf : CameraKeyframe) (default : Float) : Float :=
  match kf.zoom with
  | some z => if z > 0.0 then z else default
  | none => default

/-- Get focus distance from keyframe with default fallback. -/
def getFocusDistance (kf : CameraKeyframe) (default : Float) : Float :=
  match kf.focusDistance with
  | some fd => if fd > 0.0 then fd else default
  | none => default

--------------------------------------------------------------------------------
-- Camera Interpolation
--------------------------------------------------------------------------------

/-- Interpolate camera properties at a specific frame. -/
def interpolateCameraAtFrame (base : BaseCamera)
                              (keyframes : Array CameraKeyframe)
                              (frame : Nat) : InterpolatedCamera :=
  match findSurroundingKeyframes keyframes frame with
  | none =>
    -- No keyframes, use base camera
    { position := base.position
    , rotation := base.orientation
    , focalLength := base.focalLength
    , zoom := base.zoom
    , focusDistance := base.focusDistance
    }
  | some (prev, next) =>
    if prev.frame == next.frame then
      -- Same frame, use prev values
      { position := getPosition prev base.position
      , rotation := getOrientation prev base.orientation
      , focalLength := getFocalLength prev base.focalLength
      , zoom := getZoom prev base.zoom
      , focusDistance := getFocusDistance prev base.focusDistance
      }
    else
      -- Interpolate between prev and next
      let t := calculateT prev.frame next.frame frame
      let prevPos := getPosition prev base.position
      let nextPos := getPosition next base.position
      let prevOri := getOrientation prev base.orientation
      let nextOri := getOrientation next base.orientation

      { position := lerpVec3 prevPos nextPos t
      , rotation := lerpRotation prevOri nextOri t
      , focalLength := lerp (getFocalLength prev base.focalLength)
                            (getFocalLength next base.focalLength) t
      , zoom := lerp (getZoom prev base.zoom) (getZoom next base.zoom) t
      , focusDistance := lerp (getFocusDistance prev base.focusDistance)
                              (getFocusDistance next base.focusDistance) t
      }

--------------------------------------------------------------------------------
-- Frame Validation
--------------------------------------------------------------------------------

/-- Check if frame number is valid. -/
def isValidFrame (frame : Nat) : Bool :=
  true  -- Nat is always non-negative

/-- Check if float value is finite and positive. -/
def isPositiveFinite (value : Float) : Bool :=
  value.isFinite && value > 0.0

end Lattice.Services.Camera.Interpolation
