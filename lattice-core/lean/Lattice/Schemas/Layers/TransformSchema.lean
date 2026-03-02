/-
  Lattice.Schemas.Layers.TransformSchema - Layer transform enums and types

  Layer transform enums: motion blur, auto-orient, material options.

  Source: ui/src/schemas/layers/transform-schema.ts
-/

namespace Lattice.Schemas.Layers.TransformSchema

--------------------------------------------------------------------------------
-- Motion Blur Type
--------------------------------------------------------------------------------

/-- Motion blur types -/
inductive MotionBlurType where
  | standard
  | pixel
  | directional
  | radial
  | vector
  | adaptive
  deriving Repr, DecidableEq, Inhabited

def MotionBlurType.fromString : String → Option MotionBlurType
  | "standard" => some MotionBlurType.standard
  | "pixel" => some MotionBlurType.pixel
  | "directional" => some MotionBlurType.directional
  | "radial" => some MotionBlurType.radial
  | "vector" => some MotionBlurType.vector
  | "adaptive" => some MotionBlurType.adaptive
  | _ => none

def MotionBlurType.toString : MotionBlurType → String
  | MotionBlurType.standard => "standard"
  | MotionBlurType.pixel => "pixel"
  | MotionBlurType.directional => "directional"
  | MotionBlurType.radial => "radial"
  | MotionBlurType.vector => "vector"
  | MotionBlurType.adaptive => "adaptive"

--------------------------------------------------------------------------------
-- Radial Mode
--------------------------------------------------------------------------------

/-- Radial motion blur modes -/
inductive RadialMode where
  | spin
  | zoom
  deriving Repr, DecidableEq, Inhabited

def RadialMode.fromString : String → Option RadialMode
  | "spin" => some RadialMode.spin
  | "zoom" => some RadialMode.zoom
  | _ => none

def RadialMode.toString : RadialMode → String
  | RadialMode.spin => "spin"
  | RadialMode.zoom => "zoom"

--------------------------------------------------------------------------------
-- Auto Orient Mode
--------------------------------------------------------------------------------

/-- Auto-orient mode for layers -/
inductive AutoOrientMode where
  | off
  | toCamera
  | alongPath
  | toPointOfInterest
  deriving Repr, DecidableEq, Inhabited

def AutoOrientMode.fromString : String → Option AutoOrientMode
  | "off" => some AutoOrientMode.off
  | "toCamera" => some AutoOrientMode.toCamera
  | "alongPath" => some AutoOrientMode.alongPath
  | "toPointOfInterest" => some AutoOrientMode.toPointOfInterest
  | _ => none

def AutoOrientMode.toString : AutoOrientMode → String
  | AutoOrientMode.off => "off"
  | AutoOrientMode.toCamera => "toCamera"
  | AutoOrientMode.alongPath => "alongPath"
  | AutoOrientMode.toPointOfInterest => "toPointOfInterest"

--------------------------------------------------------------------------------
-- Casts Shadows
--------------------------------------------------------------------------------

/-- Shadow casting modes -/
inductive CastsShadows where
  | off
  | on
  | only_
  deriving Repr, DecidableEq, Inhabited

def CastsShadows.fromString : String → Option CastsShadows
  | "off" => some CastsShadows.off
  | "on" => some CastsShadows.on
  | "only" => some CastsShadows.only_
  | _ => none

def CastsShadows.toString : CastsShadows → String
  | CastsShadows.off => "off"
  | CastsShadows.on => "on"
  | CastsShadows.only_ => "only"

--------------------------------------------------------------------------------
-- Stretch Anchor
--------------------------------------------------------------------------------

/-- Time stretch anchor points -/
inductive StretchAnchor where
  | startFrame
  | endFrame
  | currentFrame
  deriving Repr, DecidableEq, Inhabited

def StretchAnchor.fromString : String → Option StretchAnchor
  | "startFrame" => some StretchAnchor.startFrame
  | "endFrame" => some StretchAnchor.endFrame
  | "currentFrame" => some StretchAnchor.currentFrame
  | _ => none

def StretchAnchor.toString : StretchAnchor → String
  | StretchAnchor.startFrame => "startFrame"
  | StretchAnchor.endFrame => "endFrame"
  | StretchAnchor.currentFrame => "currentFrame"

--------------------------------------------------------------------------------
-- Audio Feature
--------------------------------------------------------------------------------

/-- Audio features for audio-driven animation -/
inductive AudioFeature where
  | amplitude
  | bass
  | mid
  | treble
  | spectral
  deriving Repr, DecidableEq, Inhabited

def AudioFeature.fromString : String → Option AudioFeature
  | "amplitude" => some AudioFeature.amplitude
  | "bass" => some AudioFeature.bass
  | "mid" => some AudioFeature.mid
  | "treble" => some AudioFeature.treble
  | "spectral" => some AudioFeature.spectral
  | _ => none

def AudioFeature.toString : AudioFeature → String
  | AudioFeature.amplitude => "amplitude"
  | AudioFeature.bass => "bass"
  | AudioFeature.mid => "mid"
  | AudioFeature.treble => "treble"
  | AudioFeature.spectral => "spectral"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def maxShutterAngle : Float := 720.0
def maxShutterPhase : Float := 180.0
def minShutterPhase : Float := -180.0
def minSamplesPerFrame : Nat := 2
def maxSamplesPerFrame : Nat := 64
def maxBlurLength : Float := 1000.0
def maxRadialAmount : Float := 100.0
def maxMaterialValue : Float := 100.0
def maxTimeStretch : Float := 100.0
def minTimeStretch : Float := 0.01

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Separate dimensions flags -/
structure SeparateDimensions where
  position : Bool
  scale : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Motion blur settings -/
structure MotionBlurSettings where
  type_ : MotionBlurType
  shutterAngle : Float
  shutterPhase : Float
  samplesPerFrame : Nat
  direction : Option Float
  blurLength : Option Float
  radialMode : Option RadialMode
  radialCenterX : Option Float
  radialCenterY : Option Float
  radialAmount : Option Float
  deriving Repr, DecidableEq, Inhabited

/-- Material options for 3D layers -/
structure MaterialOptions where
  castsShadows : CastsShadows
  lightTransmission : Float
  acceptsShadows : Bool
  acceptsLights : Bool
  ambient : Float
  diffuse : Float
  specularIntensity : Float
  specularShininess : Float
  metal : Float
  deriving Repr, DecidableEq, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

def isValidMotionBlurSettings (s : MotionBlurSettings) : Bool :=
  s.shutterAngle >= 0 && s.shutterAngle <= maxShutterAngle &&
  s.shutterPhase >= minShutterPhase && s.shutterPhase <= maxShutterPhase &&
  s.samplesPerFrame >= minSamplesPerFrame && s.samplesPerFrame <= maxSamplesPerFrame

def isValidMaterialOptions (m : MaterialOptions) : Bool :=
  m.lightTransmission >= 0 && m.lightTransmission <= maxMaterialValue &&
  m.ambient >= 0 && m.ambient <= maxMaterialValue &&
  m.diffuse >= 0 && m.diffuse <= maxMaterialValue &&
  m.specularIntensity >= 0 && m.specularIntensity <= maxMaterialValue &&
  m.specularShininess >= 0 && m.specularShininess <= maxMaterialValue &&
  m.metal >= 0 && m.metal <= maxMaterialValue

end Lattice.Schemas.Layers.TransformSchema
