/-
  Lattice.Utils.TypeGuards - Runtime type checks and safe defaults

  These are ACTUAL runtime checks with explicit proofs.
  They narrow types by checking values at runtime.

  Source: ui/src/utils/typeGuards.ts
-/

import Lattice.Primitives
import Lattice.Utils.Validation

namespace Lattice.Utils.TypeGuards

open Lattice.Primitives
open Lattice.Utils.Validation

/-! ## Primitive Type Guards -/

/-- Check if float value is finite (not NaN, not Infinity) -/
def isFiniteFloat (value : Float) : Bool :=
  value.isFinite

/-- Check if string is non-empty -/
def isNonEmptyString (value : String) : Bool :=
  value.length > 0

/-- Check if list is non-empty -/
def isNonEmptyList {α : Type} (value : List α) : Bool :=
  !value.isEmpty

/-! ## Numeric Type Guards -/

/-- Check if value is positive -/
def isPositive (value : Float) : Bool :=
  value.isFinite && value > 0

/-- Check if value is non-negative -/
def isNonNegative (value : Float) : Bool :=
  value.isFinite && value >= 0

/-- Check if value is in unit range [0, 1] -/
def isUnitRange (value : Float) : Bool :=
  value.isFinite && value >= 0 && value <= 1

/-- Check if value is percentage [0, 100] -/
def isPercentageRange (value : Float) : Bool :=
  value.isFinite && value >= 0 && value <= 100

/-- Check if value is color channel [0, 255] -/
def isColorChannel (value : Float) : Bool :=
  value.isFinite && value >= 0 && value <= 255

/-! ## Vector Type Guards -/

/-- Check if Vec2 has valid coordinates -/
def isValidVec2 (v : Vec2) : Bool :=
  v.x.val.isFinite && v.y.val.isFinite

/-- Check if Vec3 has valid coordinates -/
def isValidVec3 (v : Vec3) : Bool :=
  v.x.val.isFinite && v.y.val.isFinite && v.z.val.isFinite

/-- Check if Vec4 has valid coordinates -/
def isValidVec4 (v : Vec4) : Bool :=
  v.x.val.isFinite && v.y.val.isFinite && v.z.val.isFinite && v.w.val.isFinite

/-! ## Bounding Box Guard -/

/-- Check if bounding box has valid dimensions (positive width/height) -/
structure BoundingBox where
  x : FiniteFloat
  y : FiniteFloat
  width : PositiveFloat
  height : PositiveFloat
  deriving Repr

/-- Try to create bounding box from raw values -/
def mkBoundingBox? (x y width height : Float) : Option BoundingBox :=
  if hx : x.isFinite then
    if hy : y.isFinite then
      if hw : width.isFinite ∧ width > 0 then
        if hh : height.isFinite ∧ height > 0 then
          some ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨width, hw.1, hw.2⟩, ⟨height, hh.1, hh.2⟩⟩
        else none
      else none
    else none
  else none

/-! ## Color Type Guards -/

/-- Check if RGB has valid channel values -/
def isValidRGB (c : RGB) : Bool :=
  isColorChannel c.r.val && isColorChannel c.g.val && isColorChannel c.b.val

/-- Check if RGBA has valid values -/
def isValidRGBA (c : RGBA) : Bool :=
  isValidRGB ⟨c.r, c.g, c.b⟩ && isUnitRange c.a.val

/-! ## Safe Default Functions -/

/-- Safe coordinate default - allows negative, zero, positive -/
def safeCoordinateDefault (value : Option Float) (default : FiniteFloat) : FiniteFloat :=
  match value with
  | none => default
  | some v =>
    if hv : v.isFinite then ⟨v, hv⟩
    else default

/-- Safe non-negative default - requires >= 0 -/
def safeNonNegativeDefault (value : Option Float) (default : NonNegativeFloat) : NonNegativeFloat :=
  match value with
  | none => default
  | some v =>
    if hv : v.isFinite ∧ v >= 0 then ⟨v, hv.1, hv.2⟩
    else default

/-- Safe positive default - requires > 0 -/
def safePositiveDefault (value : Option Float) (default : PositiveFloat) : PositiveFloat :=
  match value with
  | none => default
  | some v =>
    if hv : v.isFinite ∧ v > 0 then ⟨v, hv.1, hv.2⟩
    else default

/-- Safe unit default - requires [0, 1] -/
def safeUnitDefault (value : Option Float) (default : UnitFloat) : UnitFloat :=
  match value with
  | none => default
  | some v =>
    if hv : v.isFinite ∧ v >= 0 ∧ v <= 1 then ⟨v, hv.1, hv.2.1, hv.2.2⟩
    else default

/-- Safe percentage default - requires [0, 100] -/
def safePercentageDefault (value : Option Float) (default : Percentage) : Percentage :=
  match value with
  | none => default
  | some v =>
    if hv : v.isFinite ∧ v >= 0 ∧ v <= 100 then ⟨v, hv.1, hv.2.1, hv.2.2⟩
    else default

/-- Safe array default - returns empty if none -/
def safeArrayDefault {α : Type} (value : Option (List α)) (default : List α) : List α :=
  match value with
  | none => default
  | some v => v

/-- Safe non-empty string default -/
def safeStringDefault (value : Option String) (default : NonEmptyString) : NonEmptyString :=
  match value with
  | none => default
  | some v =>
    if hv : v.length > 0 then ⟨v, hv⟩
    else default

/-! ## Type Coercion with Validation -/

/-- Convert Float to FiniteFloat with validation -/
def toFiniteFloat (value : Float) (name : String) : ValidationResult FiniteFloat :=
  validateFiniteNumber value name {}

/-- Convert Float to PositiveFloat with validation -/
def toPositiveFloat (value : Float) (name : String) : ValidationResult PositiveFloat :=
  validatePositive value name

/-- Convert Float to NonNegativeFloat with validation -/
def toNonNegativeFloat (value : Float) (name : String) : ValidationResult NonNegativeFloat :=
  validateNonNegative value name

/-- Convert Float to UnitFloat with validation -/
def toUnitFloat (value : Float) (name : String) : ValidationResult UnitFloat :=
  validateUnit value name

/-- Convert Float to Percentage with validation -/
def toPercentage (value : Float) (name : String) : ValidationResult Percentage :=
  validatePercentage value name

/-! ## Assertion Helpers -/

/-- Assert and extract finite float, throwing on invalid -/
def assertFinite (value : Float) (name : String) : Except String FiniteFloat :=
  if hv : value.isFinite then
    .ok ⟨value, hv⟩
  else
    .error s!"{name} must be finite, got {value}"

/-- Assert and extract positive float -/
def assertPositive (value : Float) (name : String) : Except String PositiveFloat :=
  if hv : value.isFinite ∧ value > 0 then
    .ok ⟨value, hv.1, hv.2⟩
  else
    .error s!"{name} must be positive, got {value}"

/-- Assert and extract non-negative float -/
def assertNonNegative (value : Float) (name : String) : Except String NonNegativeFloat :=
  if hv : value.isFinite ∧ value >= 0 then
    .ok ⟨value, hv.1, hv.2⟩
  else
    .error s!"{name} must be non-negative, got {value}"

/-- Assert non-empty string -/
def assertNonEmpty (value : String) (name : String) : Except String NonEmptyString :=
  if hv : value.length > 0 then
    .ok ⟨value, hv⟩
  else
    .error s!"{name} cannot be empty"

/-- Assert list is non-empty -/
def assertNonEmptyList {α : Type} (value : List α) (name : String) : Except String (List α) :=
  if value.isEmpty then
    .error s!"{name} cannot be empty"
  else
    .ok value

/-! ## Checked Constructors -/

/-- Create Vec2 with validation -/
def mkVec2Checked (x y : Float) (name : String) : ValidationResult Vec2 :=
  validateVec2 x y name

/-- Create Vec3 with validation -/
def mkVec3Checked (x y z : Float) (name : String) : ValidationResult Vec3 :=
  validateVec3 x y z name

/-- Create RGB with validation -/
def mkRGBChecked (r g b : Float) (name : String) : ValidationResult RGB :=
  validateRGB r g b name

/-- Create RGBA with validation -/
def mkRGBAChecked (r g b a : Float) (name : String) : ValidationResult RGBA :=
  validateRGBA r g b a name

/-! ## Predicate Proofs -/

/-- Proof that finite float check is decidable -/
instance : Decidable (Float.isFinite x = true) :=
  inferInstanceAs (Decidable _)

/-- Proof that non-negative check on finite float is decidable -/
def decNonNegative (x : Float) : Decidable (x >= 0) :=
  if h : x >= 0 then .isTrue h else .isFalse h

/-- Proof that positive check is decidable -/
def decPositive (x : Float) : Decidable (x > 0) :=
  if h : x > 0 then .isTrue h else .isFalse h

end Lattice.Utils.TypeGuards
