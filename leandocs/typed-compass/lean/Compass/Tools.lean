/-
  Compass.Tools - Tool infrastructure types with roundtrip proofs

  Maps to toolbox/core/types.py RateLimit, ToolResult, CallContext.
-/

import Compass.Core
import Compass.Auth

namespace Compass.Tools

open Compass.Core

/-! ## Option encoding helpers -/

def Json.encodeOptString : Option String → Json
  | none => .null
  | some s => .str s

def Json.decodeOptString : Json → Option (Option String)
  | .null => some none
  | .str s => some (some s)
  | _ => none

@[simp]
theorem Json.decodeOptString_encodeOptString (o : Option String) :
    Json.decodeOptString (Json.encodeOptString o) = some o := by
  cases o <;> rfl

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

/-! ## ToolResult -/

structure ToolResult where
  success : Bool
  data : Option String  -- JSON string
  error : Option String
  cost_usd : Float
  tokens_used : Int
  duration_ms : Int
  model_used : Option String
  deriving Repr

def ToolResult.toJson (r : ToolResult) : Json := .obj [
  ("success", .bool r.success),
  ("data", Json.encodeOptString r.data),
  ("error", Json.encodeOptString r.error),
  ("cost_usd", .num r.cost_usd),
  ("tokens_used", .int r.tokens_used),
  ("duration_ms", .int r.duration_ms),
  ("model_used", Json.encodeOptString r.model_used)
]

def ToolResult.fromJson (j : Json) : Option ToolResult := do
  let success ← (Json.fieldN 0 j) >>= Json.asBool
  let data ← (Json.fieldN 1 j) >>= Json.decodeOptString
  let error ← (Json.fieldN 2 j) >>= Json.decodeOptString
  let cost_usd ← (Json.fieldN 3 j) >>= Json.asFloat
  let tokens_used ← (Json.fieldN 4 j) >>= Json.asInt
  let duration_ms ← (Json.fieldN 5 j) >>= Json.asInt
  let model_used ← (Json.fieldN 6 j) >>= Json.decodeOptString
  pure ⟨success, data, error, cost_usd, tokens_used, duration_ms, model_used⟩

theorem ToolResult.roundtrip (r : ToolResult) :
    ToolResult.fromJson (ToolResult.toJson r) = some r := by
  cases r with
  | mk success data error cost_usd tokens_used duration_ms model_used =>
    cases data <;> cases error <;> cases model_used <;> rfl

instance : Extractable ToolResult where
  encode := ToolResult.toJson
  decode := ToolResult.fromJson
  roundtrip := ToolResult.roundtrip

/-! ## CallContext -/

structure CallContext where
  user_id : String
  request_id : String
  trace_id : Option String
  parent_span_id : Option String
  job_id : Option String
  workflow_name : Option String
  created_at : DateTime
  deriving Repr

def CallContext.toJson (c : CallContext) : Json := .obj [
  ("user_id", .str c.user_id),
  ("request_id", .str c.request_id),
  ("trace_id", Json.encodeOptString c.trace_id),
  ("parent_span_id", Json.encodeOptString c.parent_span_id),
  ("job_id", Json.encodeOptString c.job_id),
  ("workflow_name", Json.encodeOptString c.workflow_name),
  ("created_at", .str c.created_at)
]

def CallContext.fromJson (j : Json) : Option CallContext := do
  let user_id ← (Json.fieldN 0 j) >>= Json.asString
  let request_id ← (Json.fieldN 1 j) >>= Json.asString
  let trace_id ← (Json.fieldN 2 j) >>= Json.decodeOptString
  let parent_span_id ← (Json.fieldN 3 j) >>= Json.decodeOptString
  let job_id ← (Json.fieldN 4 j) >>= Json.decodeOptString
  let workflow_name ← (Json.fieldN 5 j) >>= Json.decodeOptString
  let created_at ← (Json.fieldN 6 j) >>= Json.asString
  pure ⟨user_id, request_id, trace_id, parent_span_id, job_id, workflow_name, created_at⟩

theorem CallContext.roundtrip (c : CallContext) :
    CallContext.fromJson (CallContext.toJson c) = some c := by
  cases c with
  | mk user_id request_id trace_id parent_span_id job_id workflow_name created_at =>
    cases trace_id <;> cases parent_span_id <;> cases job_id <;> cases workflow_name <;> rfl

instance : Extractable CallContext where
  encode := CallContext.toJson
  decode := CallContext.fromJson
  roundtrip := CallContext.roundtrip

end Compass.Tools
