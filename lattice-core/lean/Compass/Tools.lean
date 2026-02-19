/-
  Compass.Tools - Tool infrastructure types with roundtrip proofs

  Maps to toolbox/core/types.py RateLimit, ToolResult, CallContext.
-/

import Compass.Core

namespace Compass.Tools

open Compass.Core

/-! ## RateLimit -/

structure RateLimit where
  requests : Int
  period_seconds : Int
  burst : Int
  deriving Repr, DecidableEq

def RateLimit.toJson (r : RateLimit) : Json := .obj [
  ("requests", .int r.requests),
  ("period_seconds", .int r.period_seconds),
  ("burst", .int r.burst)
]

def RateLimit.fromJson (j : Json) : Option RateLimit := do
  let requests ← (Json.fieldN 0 j) >>= Json.asInt
  let period_seconds ← (Json.fieldN 1 j) >>= Json.asInt
  let burst ← (Json.fieldN 2 j) >>= Json.asInt
  pure ⟨requests, period_seconds, burst⟩

theorem RateLimit.roundtrip (r : RateLimit) :
    RateLimit.fromJson (RateLimit.toJson r) = some r := by
  cases r; rfl

instance : Extractable RateLimit where
  encode := RateLimit.toJson
  decode := RateLimit.fromJson
  roundtrip := RateLimit.roundtrip

end Compass.Tools
