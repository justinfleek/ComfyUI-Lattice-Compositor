/-
  Lattice.Utils.ErrorHelpers - Error helper utilities

  Standardized error message formatting across the codebase.
  Provides consistent error context and helpful debugging information.

  Source: ui/src/utils/errorHelpers.ts
-/

namespace Lattice.Utils.ErrorHelpers

/-! ## Error Types -/

/-- Structured error with context -/
structure ContextualError where
  context : String    -- Module/component context
  action : String     -- What action was being performed
  reason : String     -- Why it failed
  fix : Option String -- Optional suggestion

  deriving Repr

/-- Validation error with field details -/
structure ValidationError where
  field : String      -- Field name that failed
  actualType : String -- Actual type received
  actualValue : String -- Actual value (stringified)
  expected : String   -- What was expected

  deriving Repr

/-! ## Error Construction -/

/-- Create a contextual error message -/
def mkContextualError (context action reason : String) (fix : Option String := none) : ContextualError :=
  { context, action, reason, fix }

/-- Format contextual error as string -/
def ContextualError.toString (e : ContextualError) : String :=
  let base := s!"[{e.context}] {e.action} failed: {e.reason}."
  match e.fix with
  | none => base
  | some f => s!"{base} {f}"

instance : ToString ContextualError where
  toString := ContextualError.toString

/-- Create a validation error -/
def mkValidationError (field actualType actualValue expected : String) : ValidationError :=
  { field, actualType, actualValue, expected }

/-- Format validation error as string -/
def ValidationError.toString (e : ValidationError) : String :=
  let contextual := mkContextualError
    "Validation"
    s!"Field \"{e.field}\" validation"
    s!"got {e.actualType} ({e.actualValue}), expected {e.expected}"
    (some s!"Provide a valid {e.expected} value for {e.field}")
  contextual.toString

instance : ToString ValidationError where
  toString := ValidationError.toString

/-- Convert validation error to contextual error -/
def ValidationError.toContextual (e : ValidationError) : ContextualError :=
  mkContextualError
    "Validation"
    s!"Field \"{e.field}\" validation"
    s!"got {e.actualType} ({e.actualValue}), expected {e.expected}"
    (some s!"Provide a valid {e.expected} value for {e.field}")

/-! ## Common Error Patterns -/

/-- Create error for missing required field -/
def missingFieldError (field : String) : ContextualError :=
  mkContextualError
    "Validation"
    s!"Field \"{field}\" check"
    "value is missing or undefined"
    (some s!"Provide a value for required field {field}")

/-- Create error for invalid type -/
def invalidTypeError (field expected actual : String) : ContextualError :=
  mkContextualError
    "Validation"
    s!"Field \"{field}\" type check"
    s!"expected {expected}, got {actual}"
    (some s!"Provide a {expected} value for {field}")

/-- Create error for out of range value -/
def outOfRangeError (field : String) (value min max : Float) : ContextualError :=
  mkContextualError
    "Validation"
    s!"Field \"{field}\" range check"
    s!"value {value} is outside allowed range [{min}, {max}]"
    (some s!"Provide a value between {min} and {max} for {field}")

/-- Create error for empty collection -/
def emptyCollectionError (field : String) : ContextualError :=
  mkContextualError
    "Validation"
    s!"Field \"{field}\" check"
    "collection is empty but at least one item is required"
    (some s!"Provide at least one item for {field}")

/-! ## Result Helpers -/

/-- Wrap error in Except -/
def contextualErrorToExcept {α : Type} (e : ContextualError) : Except String α :=
  .error e.toString

/-- Wrap validation error in Except -/
def validationErrorToExcept {α : Type} (e : ValidationError) : Except String α :=
  .error e.toString

end Lattice.Utils.ErrorHelpers
