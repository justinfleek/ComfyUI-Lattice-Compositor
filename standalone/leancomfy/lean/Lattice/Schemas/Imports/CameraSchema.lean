/-
  Lattice.Schemas.Imports.CameraSchema - Camera import format enums and types

  Camera import format enums and types.

  Source: ui/src/schemas/imports/camera-schema.ts
-/

namespace Lattice.Schemas.Imports.CameraSchema

--------------------------------------------------------------------------------
-- Camera Type
--------------------------------------------------------------------------------

/-- Camera type (one-node vs two-node) -/
inductive CameraType where
  | oneNode
  | twoNode
  deriving Repr, DecidableEq, Inhabited

def CameraType.fromString : String → Option CameraType
  | "one-node" => some CameraType.oneNode
  | "two-node" => some CameraType.twoNode
  | _ => none

def CameraType.toString : CameraType → String
  | CameraType.oneNode => "one-node"
  | CameraType.twoNode => "two-node"

--------------------------------------------------------------------------------
-- Auto Orient Mode
--------------------------------------------------------------------------------

/-- Auto-orient mode for cameras -/
inductive AutoOrientMode where
  | off
  | orientAlongPath
  | orientTowardsPoi
  deriving Repr, DecidableEq, Inhabited

def AutoOrientMode.fromString : String → Option AutoOrientMode
  | "off" => some AutoOrientMode.off
  | "orient-along-path" => some AutoOrientMode.orientAlongPath
  | "orient-towards-poi" => some AutoOrientMode.orientTowardsPoi
  | _ => none

def AutoOrientMode.toString : AutoOrientMode → String
  | AutoOrientMode.off => "off"
  | AutoOrientMode.orientAlongPath => "orient-along-path"
  | AutoOrientMode.orientTowardsPoi => "orient-towards-poi"

--------------------------------------------------------------------------------
-- Measure Film Size
--------------------------------------------------------------------------------

/-- How to measure film size -/
inductive MeasureFilmSize where
  | horizontal
  | vertical
  | diagonal
  deriving Repr, DecidableEq, Inhabited

def MeasureFilmSize.fromString : String → Option MeasureFilmSize
  | "horizontal" => some MeasureFilmSize.horizontal
  | "vertical" => some MeasureFilmSize.vertical
  | "diagonal" => some MeasureFilmSize.diagonal
  | _ => none

def MeasureFilmSize.toString : MeasureFilmSize → String
  | MeasureFilmSize.horizontal => "horizontal"
  | MeasureFilmSize.vertical => "vertical"
  | MeasureFilmSize.diagonal => "diagonal"

--------------------------------------------------------------------------------
-- Spatial Interpolation
--------------------------------------------------------------------------------

/-- Spatial interpolation types -/
inductive SpatialInterpolation where
  | linear
  | bezier
  | autoBezier
  | continuousBezier
  deriving Repr, DecidableEq, Inhabited

def SpatialInterpolation.fromString : String → Option SpatialInterpolation
  | "linear" => some SpatialInterpolation.linear
  | "bezier" => some SpatialInterpolation.bezier
  | "auto-bezier" => some SpatialInterpolation.autoBezier
  | "continuous-bezier" => some SpatialInterpolation.continuousBezier
  | _ => none

def SpatialInterpolation.toString : SpatialInterpolation → String
  | SpatialInterpolation.linear => "linear"
  | SpatialInterpolation.bezier => "bezier"
  | SpatialInterpolation.autoBezier => "auto-bezier"
  | SpatialInterpolation.continuousBezier => "continuous-bezier"

--------------------------------------------------------------------------------
-- Temporal Interpolation
--------------------------------------------------------------------------------

/-- Temporal interpolation types -/
inductive TemporalInterpolation where
  | linear
  | bezier
  | hold
  deriving Repr, DecidableEq, Inhabited

def TemporalInterpolation.fromString : String → Option TemporalInterpolation
  | "linear" => some TemporalInterpolation.linear
  | "bezier" => some TemporalInterpolation.bezier
  | "hold" => some TemporalInterpolation.hold
  | _ => none

def TemporalInterpolation.toString : TemporalInterpolation → String
  | TemporalInterpolation.linear => "linear"
  | TemporalInterpolation.bezier => "bezier"
  | TemporalInterpolation.hold => "hold"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def maxFocalLength : Float := 10000.0
def maxRotation : Float := 360.0
def maxZoom : Float := 1000.0
def minZoom : Float := 0.1
def maxFilmSize : Float := 100.0
def maxFocusDistance : Float := 100000.0
def maxAperture : Float := 100.0
def maxKeyframes : Nat := 100000

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

/-- Depth of field settings -/
structure DepthOfField where
  enabled : Bool
  focusDistance : Float
  aperture : Float
  fStop : Float
  blurLevel : Float
  lockToZoom : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Iris settings -/
structure Iris where
  shape : Float
  rotation : Float
  roundness : Float
  aspectRatio : Float
  diffractionFringe : Float
  deriving Repr, DecidableEq, Inhabited

/-- Highlight settings -/
structure Highlight where
  gain : Float
  threshold : Float
  saturation : Float
  deriving Repr, DecidableEq, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

def isValidVector2 (v : Vector2) : Bool :=
  v.x.isFinite && v.y.isFinite

def isValidVector3 (v : Vector3) : Bool :=
  v.x.isFinite && v.y.isFinite && v.z.isFinite

def isValidDepthOfField (dof : DepthOfField) : Bool :=
  dof.focusDistance >= 0 && dof.focusDistance <= maxFocusDistance &&
  dof.aperture >= 0 && dof.aperture <= maxAperture &&
  dof.fStop > 0 && dof.fStop <= maxAperture &&
  dof.blurLevel >= 0 && dof.blurLevel <= 1

def isValidIris (iris : Iris) : Bool :=
  iris.shape >= 0 && iris.shape <= 10 &&
  iris.rotation <= maxRotation &&
  iris.roundness >= 0 && iris.roundness <= 1 &&
  iris.aspectRatio >= 0.5 && iris.aspectRatio <= 2 &&
  iris.diffractionFringe >= 0 && iris.diffractionFringe <= 1

def isValidHighlight (h : Highlight) : Bool :=
  h.gain >= 0 && h.gain <= 1 &&
  h.threshold >= 0 && h.threshold <= 1 &&
  h.saturation >= 0 && h.saturation <= 1

end Lattice.Schemas.Imports.CameraSchema
