/-
  Lattice.Animation - Animation types

  Additional animation types not covered by Entities.lean.
  Single file under 500 lines.

  Refactored from: ui/src/types/animation.ts (213 lines)
  Note: Most animation types (Keyframe, AnimatableProperty, BezierHandle)
  are already in Lattice.Entities. This module adds clipboard operations
  and helper types.
-/

import Lattice.Primitives
import Lattice.Enums
import Lattice.Entities

namespace Lattice.Animation

open Lattice.Primitives
open Lattice.Enums
open Lattice.Entities

/-! ## Extended Interpolation Type -/

/-- Full interpolation type (includes all easing functions) -/
inductive FullInterpolationType where
  -- Base types
  | linear
  | bezier
  | hold
  -- Sine
  | easeInSine
  | easeOutSine
  | easeInOutSine
  -- Quadratic
  | easeInQuad
  | easeOutQuad
  | easeInOutQuad
  -- Cubic
  | easeInCubic
  | easeOutCubic
  | easeInOutCubic
  -- Quartic
  | easeInQuart
  | easeOutQuart
  | easeInOutQuart
  -- Quintic
  | easeInQuint
  | easeOutQuint
  | easeInOutQuint
  -- Exponential
  | easeInExpo
  | easeOutExpo
  | easeInOutExpo
  -- Circular
  | easeInCirc
  | easeOutCirc
  | easeInOutCirc
  -- Back
  | easeInBack
  | easeOutBack
  | easeInOutBack
  -- Elastic
  | easeInElastic
  | easeOutElastic
  | easeInOutElastic
  -- Bounce
  | easeInBounce
  | easeOutBounce
  | easeInOutBounce
  deriving Repr, BEq, DecidableEq

/-! ## Spatial Tangent -/

/-- Spatial tangent for motion path (3D) -/
structure SpatialTangent where
  x : Float
  y : Float
  z : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  z_finite : z.isFinite
  deriving Repr

/-! ## Extended Keyframe -/

/-- Extended keyframe with spatial tangents for motion paths -/
structure ExtendedKeyframe where
  id : NonEmptyString
  frame : FrameNumber
  value : String  -- JSON-encoded value
  interpolation : FullInterpolationType
  inHandle : BezierHandle
  outHandle : BezierHandle
  controlMode : ControlMode
  spatialInTangent : Option SpatialTangent
  spatialOutTangent : Option SpatialTangent
  deriving Repr

/-! ## Property Value Types -/

/-- Property value sum type for type-safe clipboard operations -/
inductive PropertyValue where
  | number : Float → PropertyValue
  | hexColor : NonEmptyString → PropertyValue  -- Hex color string
  | boolean : Bool → PropertyValue
  | vec2 : Float × Float → PropertyValue
  | vec3 : Float × Float × Float → PropertyValue
  | rgba : Nat × Nat × Nat × Float → PropertyValue
  deriving Repr

/-! ## Clipboard Operations -/

/-- Keyframe entry for clipboard -/
structure ClipboardKeyframeEntry where
  layerId : NonEmptyString
  propertyPath : NonEmptyString  -- Dot-separated path like "transform.position"
  keyframeIds : Array NonEmptyString
  deriving Repr

/-- Clipboard data for keyframe copy/paste -/
structure KeyframeClipboard where
  entries : Array ClipboardKeyframeEntry
  sourceFrame : FrameNumber
  deriving Repr

/-! ## Keyframe Selection -/

/-- Selected keyframe reference -/
structure KeyframeSelection where
  layerId : NonEmptyString
  propertyPath : NonEmptyString
  keyframeId : NonEmptyString
  deriving Repr

/-- Multi-keyframe selection -/
structure KeyframeSelectionSet where
  selections : Array KeyframeSelection
  deriving Repr

/-! ## Conversion Helpers -/

/-- Check if interpolation is a base type -/
def FullInterpolationType.isBase : FullInterpolationType → Bool
  | linear => true
  | bezier => true
  | hold => true
  | _ => false

/-- Check if interpolation is an easing function -/
def FullInterpolationType.isEasing : FullInterpolationType → Bool
  | t => !t.isBase

/-- Convert to base InterpolationType (for storage) -/
def FullInterpolationType.toBase : FullInterpolationType → InterpolationType
  | linear => InterpolationType.linear
  | bezier => InterpolationType.bezier
  | hold => InterpolationType.hold
  | _ => InterpolationType.custom

/-! ## Default Values -/

/-- Default bezier handle (±5 frame offset, flat slope) -/
def defaultInHandle : BezierHandle :=
  { frame := -5, value := 0, enabled := true }

def defaultOutHandle : BezierHandle :=
  { frame := 5, value := 0, enabled := true }

/-- Default spatial tangent (zero) -/
def defaultSpatialTangent : SpatialTangent :=
  ⟨0, 0, 0, by decide, by decide, by decide⟩

/-! ## Clipboard Helpers -/

/-- Check if clipboard is empty -/
def KeyframeClipboard.isEmpty (c : KeyframeClipboard) : Bool :=
  c.entries.isEmpty

/-- Get all layer IDs in clipboard -/
def KeyframeClipboard.layerIds (c : KeyframeClipboard) : Array NonEmptyString :=
  c.entries.map (·.layerId) |>.toList |>.eraseDups |>.toArray

/-- Get all property paths in clipboard -/
def KeyframeClipboard.propertyPaths (c : KeyframeClipboard) : Array NonEmptyString :=
  c.entries.map (·.propertyPath) |>.toList |>.eraseDups |>.toArray

/-! ## Selection Helpers -/

/-- Check if selection set is empty -/
def KeyframeSelectionSet.isEmpty (s : KeyframeSelectionSet) : Bool :=
  s.selections.isEmpty

/-- Get selection count -/
def KeyframeSelectionSet.count (s : KeyframeSelectionSet) : Nat :=
  s.selections.size

/-- Check if keyframe is selected -/
def KeyframeSelectionSet.isSelected (s : KeyframeSelectionSet) (layerId propertyPath keyframeId : NonEmptyString) : Bool :=
  s.selections.any fun sel =>
    sel.layerId == layerId && sel.propertyPath == propertyPath && sel.keyframeId == keyframeId

end Lattice.Animation
