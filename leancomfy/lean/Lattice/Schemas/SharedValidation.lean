/-
  Lattice.Schemas.SharedValidation - Shared validation constants and helpers

  Common validation constraints used across all schemas.
  Ensures consistency and prevents security issues.

  Source: ui/src/schemas/shared-validation.ts
-/

namespace Lattice.Schemas.SharedValidation

/-! ## Fixed Constants (Security Critical) -/

def MAX_NAME_LENGTH : Nat := 200
def MAX_DESCRIPTION_LENGTH : Nat := 2000
def MAX_COMMENT_LENGTH : Nat := 5000
def MAX_TAG_LENGTH : Nat := 50
def MAX_TAGS_COUNT : Nat := 50
def MAX_PATH_LENGTH : Nat := 500
def MAX_ID_LENGTH : Nat := 200
def MAX_MIME_TYPE_LENGTH : Nat := 100
def MAX_FONT_FAMILY_LENGTH : Nat := 200
def MAX_FONT_STYLE_LENGTH : Nat := 100
def MAX_URL_LENGTH : Nat := 2048
def MAX_BASE64_LENGTH : Nat := 50 * 1024 * 1024  -- 50MB
def MAX_SHADER_LENGTH : Nat := 100000
def MAX_FILENAME_LENGTH : Nat := 255
def MAX_ANIMATION_NAME_LENGTH : Nat := 100
def MAX_WARNING_LENGTH : Nat := 500

/-! ## Configurable Limits (Defaults) -/

structure ValidationLimitsConfig where
  maxDimension : Nat := 8192
  maxFrameCount : Nat := 10000
  maxArrayLength : Nat := 100000
  maxParticles : Nat := 1000000
  maxLayers : Nat := 1000
  maxKeyframesPerProperty : Nat := 10000
  maxStringLength : Nat := 100000
  maxFPS : Nat := 120
  deriving Repr, BEq

def defaultLimits : ValidationLimitsConfig := {}

/-! ## Validation Error -/

structure ValidationError where
  field : String
  message : String
  deriving Repr, BEq

def mkError (field message : String) : ValidationError :=
  { field, message }

/-! ## String Validation -/

/-- Validate string is non-empty with max length -/
def validateNonEmptyString (field : String) (maxLen : Nat) (value : String) : Except ValidationError String :=
  if value.isEmpty then
    throw (mkError field "must not be empty")
  else if value.length > maxLen then
    throw (mkError field s!"must be at most {maxLen} characters")
  else
    pure value.trim

/-- Validate string with max length (can be empty) -/
def validateString (field : String) (maxLen : Nat) (value : String) : Except ValidationError String :=
  if value.length > maxLen then
    throw (mkError field s!"must be at most {maxLen} characters")
  else
    pure value.trim

/-- Validate hex color format (#RRGGBB or #RRGGBBAA) -/
def validateHexColor (field : String) (value : String) : Except ValidationError String :=
  let isHexChar (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
  if value.length == 7 && value.get! 0 == '#' && value.drop 1 |>.all isHexChar then
    pure value
  else if value.length == 9 && value.get! 0 == '#' && value.drop 1 |>.all isHexChar then
    pure value
  else
    throw (mkError field "must be valid hex color (#RRGGBB or #RRGGBBAA)")

/-- Validate entity ID format -/
def validateEntityId (field : String) (value : String) : Except ValidationError String :=
  let isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-'
  if value.isEmpty then
    throw (mkError field "must not be empty")
  else if value.length > MAX_ID_LENGTH then
    throw (mkError field s!"must be at most {MAX_ID_LENGTH} characters")
  else if !value.all isIdChar then
    throw (mkError field "must contain only alphanumeric, underscores, and hyphens")
  else
    pure value

/-- Validate filename -/
def validateFilename (field : String) (value : String) : Except ValidationError String :=
  let invalidChars := ['<', '>', ':', '"', '|', '?', '*']
  if value.length > MAX_FILENAME_LENGTH then
    throw (mkError field s!"must be at most {MAX_FILENAME_LENGTH} characters")
  else if value.any (· ∈ invalidChars) then
    throw (mkError field "contains invalid characters")
  else if value.endsWith "." || value.endsWith " " then
    throw (mkError field "must not end with dot or space")
  else
    pure value

/-! ## Number Validation -/

/-- Validate positive integer with max -/
def validatePositiveInt (field : String) (maxVal : Nat) (value : Int) : Except ValidationError Nat :=
  if value ≤ 0 then
    throw (mkError field "must be positive")
  else if value.toNat > maxVal then
    throw (mkError field s!"must be at most {maxVal}")
  else
    pure value.toNat

/-- Validate non-negative integer with max -/
def validateNonNegativeInt (field : String) (maxVal : Nat) (value : Int) : Except ValidationError Nat :=
  if value < 0 then
    throw (mkError field "must be non-negative")
  else if value.toNat > maxVal then
    throw (mkError field s!"must be at most {maxVal}")
  else
    pure value.toNat

/-- Validate positive float with max -/
def validatePositiveFloat (field : String) (maxVal : Float) (value : Float) : Except ValidationError Float :=
  if value ≤ 0.0 then
    throw (mkError field "must be positive")
  else if !value.isFinite then
    throw (mkError field "must be finite")
  else if value > maxVal then
    throw (mkError field s!"must be at most {maxVal}")
  else
    pure value

/-- Validate non-negative float with max -/
def validateNonNegativeFloat (field : String) (maxVal : Float) (value : Float) : Except ValidationError Float :=
  if value < 0.0 then
    throw (mkError field "must be non-negative")
  else if !value.isFinite then
    throw (mkError field "must be finite")
  else if value > maxVal then
    throw (mkError field s!"must be at most {maxVal}")
  else
    pure value

/-! ## Array Validation -/

/-- Validate array length -/
def validateArrayLength {α : Type} (field : String) (maxLen : Nat) (arr : List α) : Except ValidationError (List α) :=
  if arr.length > maxLen then
    throw (mkError field s!"must have at most {maxLen} elements")
  else
    pure arr

/-- Validate non-empty array -/
def validateNonEmptyArray {α : Type} (field : String) (arr : List α) : Except ValidationError (List α) :=
  if arr.isEmpty then
    throw (mkError field "must not be empty")
  else
    pure arr

/-! ## Date/Time Validation -/

/-- Validate ISO 8601 datetime format (simplified check) -/
def validateDateTime (field : String) (value : String) : Except ValidationError String :=
  -- Simple check: YYYY-MM-DDTHH:MM:SS or with timezone
  if value.length < 19 then
    throw (mkError field "must be valid ISO 8601 datetime")
  else
    let dateTimePart := value.take 19
    -- Basic structure check
    let hasValidStructure :=
      dateTimePart.get! 4 == '-' &&
      dateTimePart.get! 7 == '-' &&
      dateTimePart.get! 10 == 'T' &&
      dateTimePart.get! 13 == ':' &&
      dateTimePart.get! 16 == ':'
    if hasValidStructure then
      pure value
    else
      throw (mkError field "must be valid ISO 8601 datetime")

/-- Validate date format YYYY-MM-DD -/
def validateDate (field : String) (value : String) : Except ValidationError String :=
  if value.length != 10 then
    throw (mkError field "must be YYYY-MM-DD format")
  else if value.get! 4 == '-' && value.get! 7 == '-' then
    pure value
  else
    throw (mkError field "must be YYYY-MM-DD format")

end Lattice.Schemas.SharedValidation
