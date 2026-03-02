/-
  Lattice.Utils.Validation - Runtime input validation with Result types

  Validates input at runtime boundaries (AI commands, file imports, user input).
  All validators return explicit success/failure results.

  Source: ui/src/utils/validation.ts
-/

import Lattice.Primitives

namespace Lattice.Utils.Validation

open Lattice.Primitives

/-! ## Result Type -/

/-- Validation result - either success with typed value, or failure with error -/
inductive ValidationResult (α : Type)
  | ok : α → ValidationResult α
  | fail : String → ValidationResult α
  deriving Repr

namespace ValidationResult

/-- Check if result is success -/
def isOk {α : Type} : ValidationResult α → Bool
  | ok _ => true
  | fail _ => false

/-- Get value if success, with default fallback -/
def getOr {α : Type} (result : ValidationResult α) (default : α) : α :=
  match result with
  | ok v => v
  | fail _ => default

/-- Map over success value -/
def map {α β : Type} (f : α → β) : ValidationResult α → ValidationResult β
  | ok v => ok (f v)
  | fail e => fail e

/-- Bind/flatMap for chaining validations -/
def bind {α β : Type} (result : ValidationResult α) (f : α → ValidationResult β) : ValidationResult β :=
  match result with
  | ok v => f v
  | fail e => fail e

instance : Monad ValidationResult where
  pure := ok
  bind := bind

end ValidationResult

/-! ## Primitive Validators -/

/-- Options for string validation -/
structure StringOptions where
  minLength : Option Nat := none
  maxLength : Option Nat := none
  allowEmpty : Bool := false

/-- Helper: wrap string in NonEmptyString, handling empty case -/
private def toNonEmptyString (value : String) : NonEmptyString :=
  if h : value.isEmpty then ⟨" ", by decide⟩  -- Fallback (should never happen after validation)
  else ⟨value, h⟩

/-- Validate that value is a non-empty string -/
def validateString (value : String) (name : String) (opts : StringOptions := {}) : ValidationResult NonEmptyString :=
  if !opts.allowEmpty && value.isEmpty then
    .fail s!"{name} cannot be empty"
  else if let some min := opts.minLength then
    if value.length < min then
      .fail s!"{name} must be at least {min} characters"
    else if let some max := opts.maxLength then
      if value.length > max then
        .fail s!"{name} must be at most {max} characters"
      else
        .ok (toNonEmptyString value)
    else
      .ok (toNonEmptyString value)
  else if let some max := opts.maxLength then
    if value.length > max then
      .fail s!"{name} must be at most {max} characters"
    else
      .ok (toNonEmptyString value)
  else
    .ok (toNonEmptyString value)

/-- Options for numeric validation -/
structure NumberOptions where
  min : Option Float := none
  max : Option Float := none

/-- Validate that value is finite -/
def validateFiniteNumber (value : Float) (name : String) (opts : NumberOptions := {}) : ValidationResult FiniteFloat :=
  if hf : value.isFinite then
    if let some min := opts.min then
      if value < min then
        .fail s!"{name} must be >= {min}, got {value}"
      else if let some max := opts.max then
        if value > max then
          .fail s!"{name} must be <= {max}, got {value}"
        else
          .ok ⟨value, hf⟩
      else
        .ok ⟨value, hf⟩
    else if let some max := opts.max then
      if value > max then
        .fail s!"{name} must be <= {max}, got {value}"
      else
        .ok ⟨value, hf⟩
    else
      .ok ⟨value, hf⟩
  else
    .fail s!"{name} must be a finite number"

/-- Validate integer (finite and whole) -/
def validateInteger (value : Float) (name : String) (opts : NumberOptions := {}) : ValidationResult Int :=
  let finiteResult := validateFiniteNumber value name opts
  match finiteResult with
  | .fail e => .fail e
  | .ok v =>
    let intValue := v.val.toUInt64.toNat
    let floored := Float.floor v.val
    if v.val == floored then
      .ok intValue.toInt
    else
      .fail s!"{name} must be an integer, got {value}"

/-- Validate boolean -/
def validateBoolean (value : Bool) (name : String) : ValidationResult Bool :=
  .ok value

/-- Validate value is in allowed list -/
def validateEnum {α : Type} [BEq α] [ToString α] (value : α) (name : String) (allowed : List α) : ValidationResult α :=
  if allowed.any (· == value) then
    .ok value
  else
    .fail s!"{name} must be one of allowed values"

/-! ## Numeric Type Validators -/

/-- Validate positive number (> 0) -/
def validatePositive (value : Float) (name : String) : ValidationResult PositiveFloat :=
  if hf : value.isFinite then
    if hp : value > 0 then
      .ok ⟨value, hf, hp⟩
    else
      .fail s!"{name} must be positive, got {value}"
  else
    .fail s!"{name} must be a finite number"

/-- Validate non-negative number (>= 0) -/
def validateNonNegative (value : Float) (name : String) : ValidationResult NonNegativeFloat :=
  if hf : value.isFinite then
    if hn : value >= 0 then
      .ok ⟨value, hf, hn⟩
    else
      .fail s!"{name} must be non-negative, got {value}"
  else
    .fail s!"{name} must be a finite number"

/-- Validate unit float (0 to 1) -/
def validateUnit (value : Float) (name : String) : ValidationResult UnitFloat :=
  if hf : value.isFinite then
    if hge : value >= 0 then
      if hle : value <= 1 then
        .ok ⟨value, hf, hge, hle⟩
      else
        .fail s!"{name} must be <= 1, got {value}"
    else
      .fail s!"{name} must be >= 0, got {value}"
  else
    .fail s!"{name} must be a finite number"

/-- Validate percentage (0 to 100) -/
def validatePercentage (value : Float) (name : String) : ValidationResult Percentage :=
  if hf : value.isFinite then
    if hge : value >= 0 then
      if hle : value <= 100 then
        .ok ⟨value, hf, hge, hle⟩
      else
        .fail s!"{name} must be <= 100, got {value}"
    else
      .fail s!"{name} must be >= 0, got {value}"
  else
    .fail s!"{name} must be a finite number"

/-- Validate frame number (non-negative integer) -/
def validateFrameNumber (value : Float) (name : String) : ValidationResult FrameNumber :=
  if !value.isFinite then
    .fail s!"{name} must be a finite number"
  else if value < 0 then
    .fail s!"{name} must be non-negative, got {value}"
  else
    let intVal := value.toUInt64.toNat
    if value == intVal.toFloat then
      .ok ⟨intVal⟩  -- FrameNumber only has `value : Nat`, no proofs needed
    else
      .fail s!"{name} must be an integer, got {value}"

/-! ## Array Validators -/

/-- Validate array with item validator -/
def validateArray {α : Type} (values : List Float) (name : String)
    (itemValidator : Float → String → ValidationResult α) : ValidationResult (List α) :=
  let rec go (items : List Float) (idx : Nat) (acc : List α) : ValidationResult (List α) :=
    match items with
    | [] => .ok acc.reverse
    | x :: xs =>
      match itemValidator x s!"{name}[{idx}]" with
      | .ok v => go xs (idx + 1) (v :: acc)
      | .fail e => .fail e
  go values 0 []

/-- Validate array of finite numbers -/
def validateNumberArray (values : List Float) (name : String) (opts : NumberOptions := {}) : ValidationResult (List FiniteFloat) :=
  validateArray values name (fun v n => validateFiniteNumber v n opts)

/-! ## Vector Validators -/

/-- Validate Vec2 -/
def validateVec2 (x y : Float) (name : String) : ValidationResult Vec2 :=
  match validateFiniteNumber x s!"{name}.x", validateFiniteNumber y s!"{name}.y" with
  | .ok vx, .ok vy => .ok ⟨vx, vy⟩
  | .fail e, _ => .fail e
  | _, .fail e => .fail e

/-- Validate Vec3 -/
def validateVec3 (x y z : Float) (name : String) : ValidationResult Vec3 :=
  match validateFiniteNumber x s!"{name}.x",
        validateFiniteNumber y s!"{name}.y",
        validateFiniteNumber z s!"{name}.z" with
  | .ok vx, .ok vy, .ok vz => .ok ⟨vx, vy, vz⟩
  | .fail e, _, _ => .fail e
  | _, .fail e, _ => .fail e
  | _, _, .fail e => .fail e

/-- Validate Vec4 -/
def validateVec4 (x y z w : Float) (name : String) : ValidationResult Vec4 :=
  match validateFiniteNumber x s!"{name}.x",
        validateFiniteNumber y s!"{name}.y",
        validateFiniteNumber z s!"{name}.z",
        validateFiniteNumber w s!"{name}.w" with
  | .ok vx, .ok vy, .ok vz, .ok vw => .ok ⟨vx, vy, vz, vw⟩
  | .fail e, _, _, _ => .fail e
  | _, .fail e, _, _ => .fail e
  | _, _, .fail e, _ => .fail e
  | _, _, _, .fail e => .fail e

/-! ## Color Validators -/

/-- Validate RGB color (0-255 each) -/
def validateRGB (r g b : Float) (name : String) : ValidationResult RGB :=
  let opts : NumberOptions := { min := some 0, max := some 255 }
  match validateFiniteNumber r s!"{name}.r" opts,
        validateFiniteNumber g s!"{name}.g" opts,
        validateFiniteNumber b s!"{name}.b" opts with
  | .ok vr, .ok vg, .ok vb => .ok ⟨vr, vg, vb⟩
  | .fail e, _, _ => .fail e
  | _, .fail e, _ => .fail e
  | _, _, .fail e => .fail e

/-- Validate RGBA color -/
def validateRGBA (r g b a : Float) (name : String) : ValidationResult RGBA :=
  let colorOpts : NumberOptions := { min := some 0, max := some 255 }
  let alphaOpts : NumberOptions := { min := some 0, max := some 1 }
  match validateFiniteNumber r s!"{name}.r" colorOpts,
        validateFiniteNumber g s!"{name}.g" colorOpts,
        validateFiniteNumber b s!"{name}.b" colorOpts,
        validateUnit a s!"{name}.a" with
  | .ok vr, .ok vg, .ok vb, .ok va => .ok ⟨vr, vg, vb, va⟩
  | .fail e, _, _, _ => .fail e
  | _, .fail e, _, _ => .fail e
  | _, _, .fail e, _ => .fail e
  | _, _, _, .fail e => .fail e

/-! ## Optional/Default Helpers -/

/-- Make validation optional - returns none if input is none -/
def optional {α : Type} (validator : Float → String → ValidationResult α)
    : Option Float → String → ValidationResult (Option α)
  | none, _ => .ok none
  | some v, name => (validator v name).map some

/-- Provide default if validation fails -/
def withDefault {α : Type} (validator : Float → String → ValidationResult α) (default : α)
    : Float → String → ValidationResult α :=
  fun v name =>
    match validator v name with
    | .ok x => .ok x
    | .fail _ => .ok default

/-! ## Composition Helpers -/

/-- Collect all errors from multiple validations -/
def validateAll (validations : List (Unit → ValidationResult Unit)) : ValidationResult Unit :=
  let errors := validations.filterMap fun f =>
    match f () with
    | .fail e => some e
    | .ok _ => none
  if errors.isEmpty then
    .ok ()
  else
    .fail (String.intercalate "; " errors)

/-- Chain two validations -/
def andThen {α β : Type} (first : ValidationResult α) (second : α → ValidationResult β) : ValidationResult β :=
  match first with
  | .ok v => second v
  | .fail e => .fail e

/-- Combine two validations into a pair -/
def both {α β : Type} (first : ValidationResult α) (second : ValidationResult β) : ValidationResult (α × β) :=
  match first, second with
  | .ok a, .ok b => .ok (a, b)
  | .fail e, _ => .fail e
  | _, .fail e => .fail e

end Lattice.Utils.Validation
