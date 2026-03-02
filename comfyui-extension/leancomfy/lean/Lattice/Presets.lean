/-
  Lattice.Presets - Preset System Types

  Max 500 lines.

  Source: ui/src/types/presets.ts (830 lines - mostly built-in data)

  Defines types for saving and loading presets for particles, effects,
  animations, and other configurable elements.
-/

import Lattice.Primitives

namespace Lattice.Presets

open Lattice.Primitives

/-! ## Preset Category -/

/-- Categories of presets -/
inductive PresetCategory where
  | particle
  | effect
  | animation
  | cameraShake
  | cameraTrajectory
  | pathEffect
  | textStyle
  | colorPalette
  deriving Repr, BEq, DecidableEq

/-! ## Preset Metadata -/

/-- Base metadata for all presets -/
structure PresetMetadata where
  id : NonEmptyString
  name : NonEmptyString
  category : PresetCategory
  description : Option String
  tags : Array String
  author : Option String
  createdAt : Nat        -- Unix timestamp
  updatedAt : Nat        -- Unix timestamp
  thumbnail : Option String  -- Base64 data URL
  isBuiltIn : Bool
  version : Option Nat
  deriving Repr

/-! ## Particle Preset -/

/-- Particle system configuration for presets -/
structure ParticlePresetConfig where
  maxParticles : Option Nat
  gravity : Option Float
  turbulenceStrength : Option Float
  emissionRate : Option Float
  lifespan : Option Float
  startSize : Option Float
  endSize : Option Float
  startColor : Option HexColor
  endColor : Option HexColor
  velocitySpread : Option Float
  deriving Repr

/-- Particle preset -/
structure ParticlePreset extends PresetMetadata where
  config : ParticlePresetConfig
  category_is_particle : category = PresetCategory.particle
  deriving Repr

/-! ## Effect Preset -/

/-- Effect parameter value -/
inductive EffectParamValue where
  | number : Float → EffectParamValue
  | string : String → EffectParamValue
  | bool : Bool → EffectParamValue
  | color : HexColor → EffectParamValue
  | array : Array EffectParamValue → EffectParamValue
  deriving Repr

/-- Single effect in preset -/
structure PresetEffect where
  effectType : NonEmptyString
  params : Array (String × EffectParamValue)
  deriving Repr

/-- Effect preset -/
structure EffectPreset extends PresetMetadata where
  effects : Array PresetEffect
  category_is_effect : category = PresetCategory.effect
  deriving Repr

/-! ## Path Effect Preset -/

/-- Path effect instance in preset -/
structure PathEffectInstance where
  id : NonEmptyString
  effectType : NonEmptyString
  enabled : Bool
  order : Nat
  params : Array (String × EffectParamValue)
  deriving Repr

/-- Path effect preset -/
structure PathEffectPreset extends PresetMetadata where
  effects : Array PathEffectInstance
  category_is_pathEffect : category = PresetCategory.pathEffect
  deriving Repr

/-! ## Camera Shake Preset -/

/-- Camera shake configuration (partial) -/
structure CameraShakeConfig where
  intensity : Option Float
  frequency : Option Float
  decay : Option Float
  octaves : Option Nat
  seed : Option Nat
  deriving Repr

/-- Camera shake preset -/
structure CameraShakePreset extends PresetMetadata where
  config : CameraShakeConfig
  category_is_cameraShake : category = PresetCategory.cameraShake
  deriving Repr

/-! ## Camera Trajectory Preset -/

/-- Trajectory configuration (partial) -/
structure TrajectoryConfig where
  duration : Option Float
  easing : Option NonEmptyString
  loopMode : Option NonEmptyString
  deriving Repr

/-- Camera trajectory preset -/
structure CameraTrajectoryPreset extends PresetMetadata where
  config : TrajectoryConfig
  category_is_cameraTrajectory : category = PresetCategory.cameraTrajectory
  deriving Repr

/-! ## Text Style Preset -/

/-- Text alignment -/
inductive TextAlign where
  | left | center | right
  deriving Repr, BEq, DecidableEq

/-- Text style configuration -/
structure TextStyleConfig where
  fontFamily : Option NonEmptyString
  fontSize : Option Float
  fontWeight : Option Nat
  fill : Option HexColor
  stroke : Option HexColor
  strokeWidth : Option Float
  letterSpacing : Option Float
  lineHeight : Option Float
  textAlign : Option TextAlign
  deriving Repr

/-- Text style preset -/
structure TextStylePreset extends PresetMetadata where
  style : TextStyleConfig
  category_is_textStyle : category = PresetCategory.textStyle
  deriving Repr

/-! ## Color Palette Preset -/

/-- Color palette preset -/
structure ColorPalettePreset extends PresetMetadata where
  colors : Array HexColor
  category_is_colorPalette : category = PresetCategory.colorPalette
  deriving Repr

/-! ## Animation Preset -/

/-- Keyframe in animation preset -/
structure PresetKeyframe where
  frame : FrameNumber
  value : EffectParamValue
  easing : Option NonEmptyString
  deriving Repr

/-- Property animation in preset -/
structure PresetPropertyAnimation where
  property : NonEmptyString
  keyframes : Array PresetKeyframe
  deriving Repr

/-- Animation preset -/
structure AnimationPreset extends PresetMetadata where
  keyframes : Array PresetPropertyAnimation
  duration : FrameNumber
  category_is_animation : category = PresetCategory.animation
  deriving Repr

/-! ## Preset Union -/

/-- All preset types -/
inductive Preset where
  | particle : ParticlePreset → Preset
  | effect : EffectPreset → Preset
  | pathEffect : PathEffectPreset → Preset
  | cameraShake : CameraShakePreset → Preset
  | cameraTrajectory : CameraTrajectoryPreset → Preset
  | textStyle : TextStylePreset → Preset
  | colorPalette : ColorPalettePreset → Preset
  | animation : AnimationPreset → Preset
  deriving Repr

/-- Get metadata from any preset -/
def Preset.metadata : Preset → PresetMetadata
  | .particle p => p.toPresetMetadata
  | .effect e => e.toPresetMetadata
  | .pathEffect pe => pe.toPresetMetadata
  | .cameraShake cs => cs.toPresetMetadata
  | .cameraTrajectory ct => ct.toPresetMetadata
  | .textStyle ts => ts.toPresetMetadata
  | .colorPalette cp => cp.toPresetMetadata
  | .animation a => a.toPresetMetadata

/-! ## Preset Collection -/

/-- Collection of presets for import/export -/
structure PresetCollection where
  version : Nat
  presets : Array Preset
  exportedAt : Nat  -- Unix timestamp
  deriving Repr

end Lattice.Presets
