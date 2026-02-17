/-
  Lattice.Schemas.Settings.SessionStorageSchema - Session storage validation

  Validates data stored in sessionStorage.

  Source: ui/src/schemas/settings/session-storage-schema.ts
-/

import Lattice.Schemas.SharedValidation

namespace Lattice.Schemas.Settings.SessionStorageSchema

open Lattice.Schemas.SharedValidation

/-! ## Constants -/

def MAX_SESSION_COUNT_KEYS : Nat := 1000
def MAX_CALLS_PER_SESSION : Nat := 100000

/-! ## Session Counts -/

/-- Session counts stored in sessionStorage for rate limiting -/
structure SessionCounts where
  counts : List (String × Nat)
  deriving Repr, BEq

/-- Validate SessionCounts -/
def validateSessionCounts (sc : SessionCounts) : Except ValidationError SessionCounts := do
  if sc.counts.length > MAX_SESSION_COUNT_KEYS then
    throw (mkError "counts" s!"must have at most {MAX_SESSION_COUNT_KEYS} keys")
  for (key, count) in sc.counts do
    let _ ← validateString "counts.key" MAX_NAME_LENGTH key
    let _ ← validateNonNegativeInt "counts.value" MAX_CALLS_PER_SESSION count
  pure sc

/-! ## Audit Session ID -/

/-- Validate UUID format (simplified) -/
def validateUUID (field : String) (value : String) : Except ValidationError String :=
  -- UUID format: xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx (36 chars)
  if value.length != 36 then
    throw (mkError field "must be valid UUID format")
  else if value.get! 8 != '-' || value.get! 13 != '-' ||
          value.get! 18 != '-' || value.get! 23 != '-' then
    throw (mkError field "must be valid UUID format")
  else
    let isHexChar (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
    let hexParts := value.replace "-" ""
    if hexParts.all isHexChar then
      pure value
    else
      throw (mkError field "must be valid UUID format")

/-- Validate audit session ID -/
def validateAuditSessionId (value : String) : Except ValidationError String :=
  validateUUID "auditSessionId" value

/-! ## Safe Validation -/

def safeValidateSessionCounts (sc : SessionCounts) : Option SessionCounts :=
  match validateSessionCounts sc with
  | .ok c => some c
  | .error _ => none

def safeValidateAuditSessionId (value : String) : Option String :=
  match validateAuditSessionId value with
  | .ok v => some v
  | .error _ => none

end Lattice.Schemas.Settings.SessionStorageSchema
