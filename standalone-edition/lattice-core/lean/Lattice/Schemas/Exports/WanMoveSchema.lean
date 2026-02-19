/-
  Lattice.Schemas.Exports.WanMoveSchema

  WanMove trajectory export format enums and types.

  Source: ui/src/schemas/exports/wanmove-schema.ts
-/

namespace Lattice.Schemas.Exports.WanMoveSchema

--------------------------------------------------------------------------------
-- Flow Pattern
--------------------------------------------------------------------------------

/-- Available flow pattern types -/
inductive FlowPattern where
  | spiral
  | wave
  | explosion
  | vortex
  | dataRiver
  | morph
  | swarm
  deriving Repr, DecidableEq, Inhabited

def flowPatternFromString : String → Option FlowPattern
  | "spiral" => some .spiral
  | "wave" => some .wave
  | "explosion" => some .explosion
  | "vortex" => some .vortex
  | "data-river" => some .dataRiver
  | "morph" => some .morph
  | "swarm" => some .swarm
  | _ => Option.none

def flowPatternToString : FlowPattern → String
  | .spiral => "spiral"
  | .wave => "wave"
  | .explosion => "explosion"
  | .vortex => "vortex"
  | .dataRiver => "data-river"
  | .morph => "morph"
  | .swarm => "swarm"

--------------------------------------------------------------------------------
-- Morph Shape Type
--------------------------------------------------------------------------------

/-- Morph source/target types -/
inductive MorphShapeType where
  | circle
  | grid
  | text
  | custom
  deriving Repr, DecidableEq, Inhabited

def morphShapeTypeFromString : String → Option MorphShapeType
  | "circle" => some .circle
  | "grid" => some .grid
  | "text" => some .text
  | "custom" => some .custom
  | _ => Option.none

def morphShapeTypeToString : MorphShapeType → String
  | .circle => "circle"
  | .grid => "grid"
  | .text => "text"
  | .custom => "custom"

--------------------------------------------------------------------------------
-- Morph Easing
--------------------------------------------------------------------------------

/-- Morph easing types -/
inductive MorphEasing where
  | linear
  | easeIn
  | easeOut
  | easeInOut
  deriving Repr, DecidableEq, Inhabited

def morphEasingFromString : String → Option MorphEasing
  | "linear" => some .linear
  | "ease-in" => some .easeIn
  | "ease-out" => some .easeOut
  | "ease-in-out" => some .easeInOut
  | _ => Option.none

def morphEasingToString : MorphEasing → String
  | .linear => "linear"
  | .easeIn => "ease-in"
  | .easeOut => "ease-out"
  | .easeInOut => "ease-in-out"

--------------------------------------------------------------------------------
-- Shape Easing (extended)
--------------------------------------------------------------------------------

/-- Extended easing types for shape morphing -/
inductive ShapeEasing where
  | linear
  | easeIn
  | easeOut
  | easeInOut
  | elastic
  | bounce
  deriving Repr, DecidableEq, Inhabited

def shapeEasingFromString : String → Option ShapeEasing
  | "linear" => some .linear
  | "ease-in" => some .easeIn
  | "ease-out" => some .easeOut
  | "ease-in-out" => some .easeInOut
  | "elastic" => some .elastic
  | "bounce" => some .bounce
  | _ => Option.none

def shapeEasingToString : ShapeEasing → String
  | .linear => "linear"
  | .easeIn => "ease-in"
  | .easeOut => "ease-out"
  | .easeInOut => "ease-in-out"
  | .elastic => "elastic"
  | .bounce => "bounce"

--------------------------------------------------------------------------------
-- Attractor Type
--------------------------------------------------------------------------------

/-- Available strange attractor types -/
inductive AttractorType where
  | lorenz
  | rossler
  | aizawa
  | thomas
  | halvorsen
  deriving Repr, DecidableEq, Inhabited

def attractorTypeFromString : String → Option AttractorType
  | "lorenz" => some .lorenz
  | "rossler" => some .rossler
  | "aizawa" => some .aizawa
  | "thomas" => some .thomas
  | "halvorsen" => some .halvorsen
  | _ => Option.none

def attractorTypeToString : AttractorType → String
  | .lorenz => "lorenz"
  | .rossler => "rossler"
  | .aizawa => "aizawa"
  | .thomas => "thomas"
  | .halvorsen => "halvorsen"

--------------------------------------------------------------------------------
-- Data Mapping
--------------------------------------------------------------------------------

/-- Data mapping types for data-driven flows -/
inductive DataMapping where
  | speed
  | direction
  | amplitude
  | phase
  | size
  deriving Repr, DecidableEq, Inhabited

def dataMappingFromString : String → Option DataMapping
  | "speed" => some .speed
  | "direction" => some .direction
  | "amplitude" => some .amplitude
  | "phase" => some .phase
  | "size" => some .size
  | _ => Option.none

def dataMappingToString : DataMapping → String
  | .speed => "speed"
  | .direction => "direction"
  | .amplitude => "amplitude"
  | .phase => "phase"
  | .size => "size"

--------------------------------------------------------------------------------
-- Force Falloff
--------------------------------------------------------------------------------

/-- Falloff types for force points -/
inductive ForceFalloff where
  | linear
  | quadratic
  | none
  deriving Repr, DecidableEq, Inhabited

def forceFalloffFromString : String → Option ForceFalloff
  | "linear" => some .linear
  | "quadratic" => some .quadratic
  | "none" => some .none
  | _ => Option.none

def forceFalloffToString : ForceFalloff → String
  | .linear => "linear"
  | .quadratic => "quadratic"
  | .none => "none"

--------------------------------------------------------------------------------
-- Initial Distribution
--------------------------------------------------------------------------------

/-- Initial distribution types for force fields -/
inductive InitialDistribution where
  | random
  | grid
  | edge
  | center
  deriving Repr, DecidableEq, Inhabited

def initialDistributionFromString : String → Option InitialDistribution
  | "random" => some .random
  | "grid" => some .grid
  | "edge" => some .edge
  | "center" => some .center
  | _ => Option.none

def initialDistributionToString : InitialDistribution → String
  | .random => "random"
  | .grid => "grid"
  | .edge => "edge"
  | .center => "center"

--------------------------------------------------------------------------------
-- Shape Type
--------------------------------------------------------------------------------

/-- Shape types for shape morphing -/
inductive ShapeType where
  | circle
  | grid
  | text
  | heart
  | star
  | spiral
  | random
  | custom
  deriving Repr, DecidableEq, Inhabited

def shapeTypeFromString : String → Option ShapeType
  | "circle" => some .circle
  | "grid" => some .grid
  | "text" => some .text
  | "heart" => some .heart
  | "star" => some .star
  | "spiral" => some .spiral
  | "random" => some .random
  | "custom" => some .custom
  | _ => Option.none

def shapeTypeToString : ShapeType → String
  | .circle => "circle"
  | .grid => "grid"
  | .text => "text"
  | .heart => "heart"
  | .star => "star"
  | .spiral => "spiral"
  | .random => "random"
  | .custom => "custom"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def WANMOVE_MAX_DIMENSION : Nat := 8192
def WANMOVE_MAX_POINTS : Nat := 10000
def WANMOVE_MAX_FRAMES : Nat := 10000
def MAX_FPS : Float := 120.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- 2D point -/
structure Point2D where
  x : Float
  y : Float
  deriving Repr, Inhabited

/-- Track point tuple -/
abbrev TrackPointTuple := Float × Float

/-- RGB color tuple (0-255) -/
structure RGBColor where
  r : Nat
  g : Nat
  b : Nat
  deriving Repr, Inhabited

/-- WanMove trajectory metadata -/
structure WanMoveMetadata where
  numPoints : Nat
  numFrames : Nat
  width : Nat
  height : Nat
  fps : Float
  deriving Repr, Inhabited

/-- WanMove trajectory structure -/
structure WanMoveTrajectory where
  tracks : Array (Array TrackPointTuple)
  visibility : Array (Array Bool)
  metadata : WanMoveMetadata
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Check if metadata is valid -/
def WanMoveMetadata.isValid (m : WanMoveMetadata) : Bool :=
  m.numPoints > 0 && m.numPoints <= WANMOVE_MAX_POINTS &&
  m.numFrames > 0 && m.numFrames <= WANMOVE_MAX_FRAMES &&
  m.width > 0 && m.width <= WANMOVE_MAX_DIMENSION &&
  m.height > 0 && m.height <= WANMOVE_MAX_DIMENSION &&
  m.fps > 0 && m.fps <= MAX_FPS

/-- Check if RGB color is valid -/
def RGBColor.isValid (c : RGBColor) : Bool :=
  c.r <= 255 && c.g <= 255 && c.b <= 255

/-- Check if trajectory is valid -/
def WanMoveTrajectory.isValid (t : WanMoveTrajectory) : Bool :=
  t.metadata.isValid &&
  t.tracks.size == t.metadata.numPoints &&
  t.tracks.size == t.visibility.size

end Lattice.Schemas.Exports.WanMoveSchema
