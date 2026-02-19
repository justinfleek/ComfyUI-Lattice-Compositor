/-
  Lattice.Effects.Parameters - Effect parameter types

  Part of Effects module. Max 500 lines.

  Source: ui/src/types/effects.ts (lines 28-62, 148-154)
-/

import Lattice.Primitives
import Lattice.Enums
import Lattice.Effects.Enums

namespace Lattice.Effects.Parameters

open Lattice.Primitives
open Lattice.Enums
open Lattice.Effects.Enums

/-! ## 2D Point -/

/-- 2D point for effect parameters -/
structure EffectPoint2D where
  x : Float
  y : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-! ## 3D Point -/

/-- 3D point for effect parameters -/
structure EffectPoint3D where
  x : Float
  y : Float
  z : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  z_finite : z.isFinite
  deriving Repr

/-! ## RGBA Color -/

/-- RGBA color for effect parameters (0-255 for RGB, 0-1 for alpha) -/
structure EffectRGBA where
  r : Nat
  g : Nat
  b : Nat
  a : Float
  r_le_255 : r ≤ 255
  g_le_255 : g ≤ 255
  b_le_255 : b ≤ 255
  a_ge_0 : a ≥ 0
  a_le_1 : a ≤ 1
  a_finite : a.isFinite
  deriving Repr

/-! ## Curve Point -/

/-- Point on a bezier curve -/
structure CurvePoint where
  x : Float
  y : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-! ## Effect Parameter Value -/

/-- Effect parameter value (sum type for all possible value types) -/
inductive EffectParameterValue where
  | number : Float → EffectParameterValue
  | string : String → EffectParameterValue
  | boolean : Bool → EffectParameterValue
  | point2D : EffectPoint2D → EffectParameterValue
  | point3D : EffectPoint3D → EffectParameterValue
  | color : EffectRGBA → EffectParameterValue
  | curve : Array CurvePoint → EffectParameterValue
  | data : String → EffectParameterValue  -- JSON-encoded data
  | null : EffectParameterValue
  deriving Repr

/-! ## Dropdown Option -/

/-- Option for dropdown parameter -/
structure DropdownOption where
  label : NonEmptyString
  value : EffectParameterValue
  deriving Repr

/-! ## Effect Parameter Definition -/

/-- Parameter definition in effect template (without id/value) -/
structure EffectParameterDef where
  name : NonEmptyString
  parameterType : EffectParameterType
  defaultValue : EffectParameterValue
  min : Option Float
  max : Option Float
  step : Option Float
  options : Option (Array DropdownOption)
  animatable : Bool
  group : Option NonEmptyString
  -- Proofs for numeric bounds
  min_finite : ∀ m, min = some m → m.isFinite
  max_finite : ∀ m, max = some m → m.isFinite
  step_positive : ∀ s, step = some s → s > 0
  step_finite : ∀ s, step = some s → s.isFinite
  deriving Repr

/-! ## Effect Parameter -/

/-- Full effect parameter (with id and current value) -/
structure EffectParameter where
  id : NonEmptyString
  name : NonEmptyString
  parameterType : EffectParameterType
  value : EffectParameterValue
  defaultValue : EffectParameterValue
  min : Option Float
  max : Option Float
  step : Option Float
  options : Option (Array DropdownOption)
  animatable : Bool
  group : Option NonEmptyString
  -- Proofs for numeric bounds
  min_finite : ∀ m, min = some m → m.isFinite
  max_finite : ∀ m, max = some m → m.isFinite
  step_positive : ∀ s, step = some s → s > 0
  step_finite : ∀ s, step = some s → s.isFinite
  deriving Repr

/-! ## Smart Constructors -/

/-- Create a number parameter value -/
def mkNumberValue (n : Float) (h : n.isFinite) : EffectParameterValue :=
  EffectParameterValue.number n

/-- Create a point2D parameter value -/
def mkPoint2DValue (x y : Float) (hx : x.isFinite) (hy : y.isFinite) : EffectParameterValue :=
  EffectParameterValue.point2D ⟨x, y, hx, hy⟩

/-- Create a point3D parameter value -/
def mkPoint3DValue (x y z : Float) (hx : x.isFinite) (hy : y.isFinite) (hz : z.isFinite) : EffectParameterValue :=
  EffectParameterValue.point3D ⟨x, y, z, hx, hy, hz⟩

/-- Create a color parameter value -/
def mkColorValue (r g b : Nat) (a : Float)
    (hr : r ≤ 255) (hg : g ≤ 255) (hb : b ≤ 255)
    (ha0 : a ≥ 0) (ha1 : a ≤ 1) (haf : a.isFinite) : EffectParameterValue :=
  EffectParameterValue.color ⟨r, g, b, a, hr, hg, hb, ha0, ha1, haf⟩

/-! ## Parameter Validation -/

/-- Check if value is within parameter bounds -/
def EffectParameter.isValueInBounds (p : EffectParameter) : Bool :=
  match p.value with
  | EffectParameterValue.number n =>
    let minOk := match p.min with
      | some m => n >= m
      | none => true
    let maxOk := match p.max with
      | some m => n <= m
      | none => true
    minOk && maxOk
  | _ => true

/-! ## Default Values -/

/-- Default number parameter value -/
def defaultNumberValue : EffectParameterValue := EffectParameterValue.number 0

/-- Default point2D parameter value -/
def defaultPoint2DValue : EffectParameterValue :=
  EffectParameterValue.point2D ⟨0.5, 0.5, by decide, by decide⟩

/-- Default point3D parameter value -/
def defaultPoint3DValue : EffectParameterValue :=
  EffectParameterValue.point3D ⟨0, 0, 0, by decide, by decide, by decide⟩

/-- Default color parameter value (white) -/
def defaultColorValue : EffectParameterValue :=
  EffectParameterValue.color ⟨255, 255, 255, 1.0,
    by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- Default color parameter value (black) -/
def defaultBlackValue : EffectParameterValue :=
  EffectParameterValue.color ⟨0, 0, 0, 1.0,
    by decide, by decide, by decide,
    by decide, by decide, by decide⟩

end Lattice.Effects.Parameters
