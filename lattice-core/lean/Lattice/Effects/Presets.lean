/-
  Lattice.Effects.Presets - Animation presets and templates

  Part of Effects module. Max 500 lines.

  Source: ui/src/types/effects.ts (lines 3210-3338)
-/

import Lattice.Primitives
import Lattice.Enums
import Lattice.Effects.Parameters

namespace Lattice.Effects.Presets

open Lattice.Primitives
open Lattice.Enums
open Lattice.Effects.Parameters

/-! ## Preset Category -/

/-- Category of animation preset -/
inductive PresetCategory where
  | fade
  | scale
  | position
  | rotation
  | text
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Bezier Handle -/

/-- Bezier handle for preset keyframes -/
structure PresetBezierHandle where
  x : Float
  y : Float
  x_ge_0 : x ≥ 0
  x_le_1 : x ≤ 1
  y_finite : y.isFinite
  x_finite : x.isFinite
  deriving Repr

/-! ## Preset Keyframe -/

/-- Keyframe in animation preset -/
structure PresetKeyframe where
  time : Float              -- 0-1 normalized time
  value : EffectParameterValue
  inHandle : Option PresetBezierHandle
  outHandle : Option PresetBezierHandle
  time_ge_0 : time ≥ 0
  time_le_1 : time ≤ 1
  time_finite : time.isFinite
  deriving Repr

/-! ## Preset Property Animation -/

/-- Property animation within a preset -/
structure PresetPropertyAnimation where
  property : NonEmptyString  -- Property name (e.g., "opacity", "scale", "position")
  keyframes : Array PresetKeyframe
  h_min_keyframes : keyframes.size ≥ 2
  deriving Repr

/-! ## Animation Preset -/

/-- Animation preset definition -/
structure AnimationPreset where
  id : NonEmptyString
  name : NonEmptyString
  category : PresetCategory
  description : String
  keyframes : Array PresetPropertyAnimation
  deriving Repr

/-! ## Smart Constructors -/

/-- Create preset keyframe with linear handles (no easing) -/
def mkLinearKeyframe (time : Float) (value : EffectParameterValue)
    (h0 : time ≥ 0) (h1 : time ≤ 1) (hf : time.isFinite) : PresetKeyframe :=
  { time, value, inHandle := none, outHandle := none,
    time_ge_0 := h0, time_le_1 := h1, time_finite := hf }

/-- Create preset keyframe with ease-in-out handles -/
def mkEaseInOutKeyframe (time : Float) (value : EffectParameterValue)
    (h0 : time ≥ 0) (h1 : time ≤ 1) (hf : time.isFinite) : PresetKeyframe :=
  let inH : PresetBezierHandle := ⟨0.6, 1, by decide, by decide, by decide, by decide⟩
  let outH : PresetBezierHandle := ⟨0.4, 0, by decide, by decide, by decide, by decide⟩
  { time, value, inHandle := some inH, outHandle := some outH,
    time_ge_0 := h0, time_le_1 := h1, time_finite := hf }

/-! ## Preset Helpers -/

/-- Get total duration of preset (always 1.0 for normalized) -/
def AnimationPreset.duration (_p : AnimationPreset) : Float := 1.0

/-- Get all property names animated by preset -/
def AnimationPreset.animatedProperties (p : AnimationPreset) : Array NonEmptyString :=
  p.keyframes.map (·.property)

/-- Check if preset animates a specific property -/
def AnimationPreset.animatesProperty (p : AnimationPreset) (prop : NonEmptyString) : Bool :=
  p.keyframes.any (·.property == prop)

/-! ## Preset Validation -/

/-- Validate that all keyframes are in order -/
def PresetPropertyAnimation.isOrdered (a : PresetPropertyAnimation) : Bool :=
  let times := a.keyframes.map (·.time)
  times.size < 2 || (times.zipWith times.tail! (· <= ·)).all id

/-! ## Preset Categories -/

/-- Get category from string -/
def PresetCategory.fromString : String → Option PresetCategory
  | "fade" => some PresetCategory.fade
  | "scale" => some PresetCategory.scale
  | "position" => some PresetCategory.position
  | "rotation" => some PresetCategory.rotation
  | "text" => some PresetCategory.text
  | "custom" => some PresetCategory.custom
  | _ => none

/-- Convert category to string -/
def PresetCategory.toString : PresetCategory → String
  | fade => "fade"
  | scale => "scale"
  | position => "position"
  | rotation => "rotation"
  | text => "text"
  | custom => "custom"

/-! ## Common Preset Values -/

/-- Zero opacity value -/
def zeroOpacity : EffectParameterValue := EffectParameterValue.number 0

/-- Full opacity value -/
def fullOpacity : EffectParameterValue := EffectParameterValue.number 100

/-- Zero scale value -/
def zeroScale : EffectParameterValue :=
  EffectParameterValue.point2D ⟨0, 0, by decide, by decide⟩

/-- Full scale value (100%) -/
def fullScale : EffectParameterValue :=
  EffectParameterValue.point2D ⟨100, 100, by decide, by decide⟩

/-- Overshoot scale value (110%) -/
def overshootScale : EffectParameterValue :=
  EffectParameterValue.point2D ⟨110, 110, by decide, by decide⟩

/-- Undershoot scale value (95%) -/
def undershootScale : EffectParameterValue :=
  EffectParameterValue.point2D ⟨95, 95, by decide, by decide⟩

/-- Center position -/
def centerPosition : EffectParameterValue :=
  EffectParameterValue.point2D ⟨0.5, 0.5, by decide, by decide⟩

/-- Off-screen right position -/
def offScreenRight : EffectParameterValue :=
  EffectParameterValue.point2D ⟨1.5, 0.5, by decide, by decide⟩

/-- Zero rotation -/
def zeroRotation : EffectParameterValue := EffectParameterValue.number 0

/-- Full rotation (360°) -/
def fullRotation : EffectParameterValue := EffectParameterValue.number 360

end Lattice.Effects.Presets
