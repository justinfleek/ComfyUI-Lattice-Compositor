/-
  Lattice.Schemas.AI.MotionSuggestionSchema

  AI motion suggestion validation for camera/layer/particle/spline intents.

  Source: ui/src/schemas/ai/motion-suggestion-schema.ts
-/

import Lattice.Schemas.SharedValidation

namespace Lattice.Schemas.AI.MotionSuggestionSchema

open SharedValidation

--------------------------------------------------------------------------------
-- Camera Motion Type
--------------------------------------------------------------------------------

/-- Camera motion type options -/
inductive CameraMotionType where
  | dolly
  | truck
  | pedestal
  | pan
  | tilt
  | roll
  | orbit
  | drift
  | handheld
  | crane
  | zoom
  | follow_path
  deriving Repr, DecidableEq, Inhabited

def cameraMotionTypeFromString : String → Option CameraMotionType
  | "dolly" => some .dolly
  | "truck" => some .truck
  | "pedestal" => some .pedestal
  | "pan" => some .pan
  | "tilt" => some .tilt
  | "roll" => some .roll
  | "orbit" => some .orbit
  | "drift" => some .drift
  | "handheld" => some .handheld
  | "crane" => some .crane
  | "zoom" => some .zoom
  | "follow_path" => some .follow_path
  | _ => none

def cameraMotionTypeToString : CameraMotionType → String
  | .dolly => "dolly"
  | .truck => "truck"
  | .pedestal => "pedestal"
  | .pan => "pan"
  | .tilt => "tilt"
  | .roll => "roll"
  | .orbit => "orbit"
  | .drift => "drift"
  | .handheld => "handheld"
  | .crane => "crane"
  | .zoom => "zoom"
  | .follow_path => "follow_path"

--------------------------------------------------------------------------------
-- Motion Intensity
--------------------------------------------------------------------------------

/-- Motion intensity levels -/
inductive MotionIntensity where
  | very_subtle
  | subtle
  | medium
  | strong
  | dramatic
  deriving Repr, DecidableEq, Inhabited

def motionIntensityFromString : String → Option MotionIntensity
  | "very_subtle" => some .very_subtle
  | "subtle" => some .subtle
  | "medium" => some .medium
  | "strong" => some .strong
  | "dramatic" => some .dramatic
  | _ => none

def motionIntensityToString : MotionIntensity → String
  | .very_subtle => "very_subtle"
  | .subtle => "subtle"
  | .medium => "medium"
  | .strong => "strong"
  | .dramatic => "dramatic"

--------------------------------------------------------------------------------
-- Easing Type
--------------------------------------------------------------------------------

/-- Easing type options -/
inductive EasingType where
  | linear
  | easeIn
  | easeOut
  | easeInOut
  | bounce
  | elastic
  deriving Repr, DecidableEq, Inhabited

def easingTypeFromString : String → Option EasingType
  | "linear" => some .linear
  | "easeIn" => some .easeIn
  | "easeOut" => some .easeOut
  | "easeInOut" => some .easeInOut
  | "bounce" => some .bounce
  | "elastic" => some .elastic
  | _ => none

def easingTypeToString : EasingType → String
  | .linear => "linear"
  | .easeIn => "easeIn"
  | .easeOut => "easeOut"
  | .easeInOut => "easeInOut"
  | .bounce => "bounce"
  | .elastic => "elastic"

--------------------------------------------------------------------------------
-- Spline Usage
--------------------------------------------------------------------------------

/-- Spline usage options -/
inductive SplineUsage where
  | camera_path
  | emitter_path
  | text_path
  | layer_path
  deriving Repr, DecidableEq, Inhabited

def splineUsageFromString : String → Option SplineUsage
  | "camera_path" => some .camera_path
  | "emitter_path" => some .emitter_path
  | "text_path" => some .text_path
  | "layer_path" => some .layer_path
  | _ => none

def splineUsageToString : SplineUsage → String
  | .camera_path => "camera_path"
  | .emitter_path => "emitter_path"
  | .text_path => "text_path"
  | .layer_path => "layer_path"

--------------------------------------------------------------------------------
-- Particle Behavior
--------------------------------------------------------------------------------

/-- Particle behavior options -/
inductive ParticleBehavior where
  | flow
  | drift
  | spray
  | turbulence
  | explosion
  | vortex
  | rain
  | snow
  | fireflies
  | dust
  | along_path
  deriving Repr, DecidableEq, Inhabited

def particleBehaviorFromString : String → Option ParticleBehavior
  | "flow" => some .flow
  | "drift" => some .drift
  | "spray" => some .spray
  | "turbulence" => some .turbulence
  | "explosion" => some .explosion
  | "vortex" => some .vortex
  | "rain" => some .rain
  | "snow" => some .snow
  | "fireflies" => some .fireflies
  | "dust" => some .dust
  | "along_path" => some .along_path
  | _ => none

def particleBehaviorToString : ParticleBehavior → String
  | .flow => "flow"
  | .drift => "drift"
  | .spray => "spray"
  | .turbulence => "turbulence"
  | .explosion => "explosion"
  | .vortex => "vortex"
  | .rain => "rain"
  | .snow => "snow"
  | .fireflies => "fireflies"
  | .dust => "dust"
  | .along_path => "along_path"

--------------------------------------------------------------------------------
-- Layer Motion Type
--------------------------------------------------------------------------------

/-- Layer motion type options -/
inductive LayerMotionType where
  | parallax
  | float
  | sway
  | breathe
  | drift
  | noise
  | pulse
  | rotate
  | follow_path
  deriving Repr, DecidableEq, Inhabited

def layerMotionTypeFromString : String → Option LayerMotionType
  | "parallax" => some .parallax
  | "float" => some .float
  | "sway" => some .sway
  | "breathe" => some .breathe
  | "drift" => some .drift
  | "noise" => some .noise
  | "pulse" => some .pulse
  | "rotate" => some .rotate
  | "follow_path" => some .follow_path
  | _ => none

def layerMotionTypeToString : LayerMotionType → String
  | .parallax => "parallax"
  | .float => "float"
  | .sway => "sway"
  | .breathe => "breathe"
  | .drift => "drift"
  | .noise => "noise"
  | .pulse => "pulse"
  | .rotate => "rotate"
  | .follow_path => "follow_path"

--------------------------------------------------------------------------------
-- Color Scheme
--------------------------------------------------------------------------------

/-- Color scheme options -/
inductive ColorScheme where
  | warm
  | cool
  | neutral
  | custom
  deriving Repr, DecidableEq, Inhabited

def colorSchemeFromString : String → Option ColorScheme
  | "warm" => some .warm
  | "cool" => some .cool
  | "neutral" => some .neutral
  | "custom" => some .custom
  | _ => none

def colorSchemeToString : ColorScheme → String
  | .warm => "warm"
  | .cool => "cool"
  | .neutral => "neutral"
  | .custom => "custom"

--------------------------------------------------------------------------------
-- Control Point Type
--------------------------------------------------------------------------------

/-- Control point type options -/
inductive ControlPointType where
  | corner
  | smooth
  | symmetric
  deriving Repr, DecidableEq, Inhabited

def controlPointTypeFromString : String → Option ControlPointType
  | "corner" => some .corner
  | "smooth" => some .smooth
  | "symmetric" => some .symmetric
  | _ => none

def controlPointTypeToString : ControlPointType → String
  | .corner => "corner"
  | .smooth => "smooth"
  | .symmetric => "symmetric"

--------------------------------------------------------------------------------
-- Axis
--------------------------------------------------------------------------------

/-- Axis options -/
inductive Axis where
  | x
  | y
  | z
  | all
  deriving Repr, DecidableEq, Inhabited

def axisFromString : String → Option Axis
  | "x" => some .x
  | "y" => some .y
  | "z" => some .z
  | "all" => some .all
  | _ => none

def axisToString : Axis → String
  | .x => "x"
  | .y => "y"
  | .z => "z"
  | .all => "all"

--------------------------------------------------------------------------------
-- Motion Axis
--------------------------------------------------------------------------------

/-- Motion axis options -/
inductive MotionAxis where
  | x
  | y
  | z
  | scale
  | rotation
  deriving Repr, DecidableEq, Inhabited

def motionAxisFromString : String → Option MotionAxis
  | "x" => some .x
  | "y" => some .y
  | "z" => some .z
  | "scale" => some .scale
  | "rotation" => some .rotation
  | _ => none

def motionAxisToString : MotionAxis → String
  | .x => "x"
  | .y => "y"
  | .z => "z"
  | .scale => "scale"
  | .rotation => "rotation"

end Lattice.Schemas.AI.MotionSuggestionSchema
