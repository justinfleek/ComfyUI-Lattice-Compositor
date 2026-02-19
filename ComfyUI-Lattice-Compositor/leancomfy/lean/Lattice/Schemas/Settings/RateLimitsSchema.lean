/-
  Lattice.Schemas.Settings.RateLimitsSchema - Rate limits schema

  Validates rate limit data stored in localStorage/sessionStorage.

  Source: ui/src/schemas/settings/rate-limits-schema.ts
-/

import Lattice.Schemas.SharedValidation

namespace Lattice.Schemas.Settings.RateLimitsSchema

open Lattice.Schemas.SharedValidation

/-! ## Constants -/

def MAX_CALLS_PER_DAY : Nat := 100000
def MAX_CALLS_PER_SESSION : Nat := 10000
def MAX_VRAM_COST_MB : Nat := 1000000  -- 1TB
def MAX_RATE_LIMIT_KEYS : Nat := 1000

/-! ## Rate Limit Config -/

/-- Rate limit configuration for a tool -/
structure RateLimitConfig where
  toolName : String
  maxPerDay : Nat
  maxPerSession : Option Nat
  vramCostMB : Option Float
  deriving Repr, BEq

/-- Validate RateLimitConfig -/
def validateRateLimitConfig (config : RateLimitConfig) : Except ValidationError RateLimitConfig := do
  let _ ← validateNonEmptyString "toolName" MAX_NAME_LENGTH config.toolName
  let _ ← validatePositiveInt "maxPerDay" MAX_CALLS_PER_DAY config.maxPerDay
  match config.maxPerSession with
  | some max => let _ ← validatePositiveInt "maxPerSession" MAX_CALLS_PER_SESSION max; pure ()
  | none => pure ()
  match config.vramCostMB with
  | some cost => let _ ← validatePositiveFloat "vramCostMB" MAX_VRAM_COST_MB.toFloat cost; pure ()
  | none => pure ()
  pure config

/-! ## Rate Limit Status -/

/-- Rate limit status for a tool -/
structure RateLimitStatus where
  toolName : String
  callsToday : Nat
  maxPerDay : Nat
  callsThisSession : Nat
  maxPerSession : Option Nat
  canCall : Bool
  blockedReason : Option String
  resetsAt : String  -- ISO timestamp
  resetsIn : String  -- Human readable
  deriving Repr, BEq

/-- Validate RateLimitStatus constraints -/
def validateStatusConstraints (status : RateLimitStatus) : Except ValidationError Unit :=
  if status.callsToday > status.maxPerDay then
    throw (mkError "callsToday" "must be <= maxPerDay")
  else match status.maxPerSession with
    | some max =>
      if status.callsThisSession > max then
        throw (mkError "callsThisSession" "must be <= maxPerSession")
      else pure ()
    | none => pure ()

/-- Validate RateLimitStatus -/
def validateRateLimitStatus (status : RateLimitStatus) : Except ValidationError RateLimitStatus := do
  let _ ← validateNonEmptyString "toolName" MAX_NAME_LENGTH status.toolName
  let _ ← validateNonNegativeInt "callsToday" MAX_CALLS_PER_DAY status.callsToday
  let _ ← validatePositiveInt "maxPerDay" MAX_CALLS_PER_DAY status.maxPerDay
  let _ ← validateNonNegativeInt "callsThisSession" MAX_CALLS_PER_SESSION status.callsThisSession
  match status.maxPerSession with
  | some max => let _ ← validatePositiveInt "maxPerSession" MAX_CALLS_PER_SESSION max; pure ()
  | none => pure ()
  match status.blockedReason with
  | some reason => let _ ← validateString "blockedReason" 500 reason; pure ()
  | none => pure ()
  let _ ← validateDateTime "resetsAt" status.resetsAt
  let _ ← validateString "resetsIn" 100 status.resetsIn
  validateStatusConstraints status
  pure status

/-! ## Stored Rate Limits -/

/-- Rate limits stored in localStorage -/
structure StoredRateLimits where
  date : String  -- YYYY-MM-DD
  counts : List (String × Nat)
  lastReset : String  -- ISO timestamp
  deriving Repr, BEq

/-- Validate StoredRateLimits -/
def validateStoredRateLimits (limits : StoredRateLimits) : Except ValidationError StoredRateLimits := do
  let _ ← validateDate "date" limits.date
  let _ ← validateDateTime "lastReset" limits.lastReset
  if limits.counts.length > MAX_RATE_LIMIT_KEYS then
    throw (mkError "counts" s!"must have at most {MAX_RATE_LIMIT_KEYS} keys")
  else
    for (key, count) in limits.counts do
      let _ ← validateString "counts.key" MAX_NAME_LENGTH key
      let _ ← validateNonNegativeInt "counts.value" MAX_CALLS_PER_DAY count
    pure limits

/-- Safe validation (returns Option) -/
def safeValidateStoredRateLimits (limits : StoredRateLimits) : Option StoredRateLimits :=
  match validateStoredRateLimits limits with
  | .ok l => some l
  | .error _ => none

end Lattice.Schemas.Settings.RateLimitsSchema
