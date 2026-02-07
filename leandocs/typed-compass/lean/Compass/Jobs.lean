/-
  Compass.Jobs - Job execution types with roundtrip proofs

  Maps to toolbox/core/types.py Job, JobStatus.
-/

import Compass.Core

namespace Compass.Jobs

open Compass.Core

/-! ## JobStatus Enum -/

inductive JobStatus where
  | PENDING : JobStatus
  | RUNNING : JobStatus
  | WAITING_APPROVAL : JobStatus
  | APPROVED : JobStatus
  | COMPLETED : JobStatus
  | FAILED : JobStatus
  | CANCELLED : JobStatus
  deriving Repr, DecidableEq, Inhabited

def JobStatus.toString : JobStatus → String
  | .PENDING => "pending"
  | .RUNNING => "running"
  | .WAITING_APPROVAL => "waiting_approval"
  | .APPROVED => "approved"
  | .COMPLETED => "completed"
  | .FAILED => "failed"
  | .CANCELLED => "cancelled"

def JobStatus.fromString : String → Option JobStatus
  | "pending" => some .PENDING
  | "running" => some .RUNNING
  | "waiting_approval" => some .WAITING_APPROVAL
  | "approved" => some .APPROVED
  | "completed" => some .COMPLETED
  | "failed" => some .FAILED
  | "cancelled" => some .CANCELLED
  | _ => none

theorem job_status_roundtrip (s : JobStatus) :
    JobStatus.fromString (JobStatus.toString s) = some s := by
  cases s <;> rfl

instance : Extractable JobStatus where
  encode s := .str (JobStatus.toString s)
  decode j := do
    let s ← j.asString
    JobStatus.fromString s
  roundtrip s := by simp [Json.asString, job_status_roundtrip]

/-! ## Job (simplified with positional access) -/

structure Job where
  id : String
  job_type : String
  status : JobStatus
  created_by : String
  input_data : String  -- JSON string
  requires_approval : Bool
  created_at : DateTime
  retry_count : Int
  max_retries : Int
  cost_usd : Float
  deriving Repr

-- Encode using ordered fields
def Job.toJson (j : Job) : Json := .obj [
  ("id", .str j.id),
  ("job_type", .str j.job_type),
  ("status", .str (JobStatus.toString j.status)),
  ("created_by", .str j.created_by),
  ("input_data", .str j.input_data),
  ("requires_approval", .bool j.requires_approval),
  ("created_at", .str j.created_at),
  ("retry_count", .int j.retry_count),
  ("max_retries", .int j.max_retries),
  ("cost_usd", .num j.cost_usd)
]

-- Decode using positional access
def Job.fromJson (json : Json) : Option Job := do
  let id ← (Json.fieldN 0 json) >>= Json.asString
  let job_type ← (Json.fieldN 1 json) >>= Json.asString
  let status_str ← (Json.fieldN 2 json) >>= Json.asString
  let status ← JobStatus.fromString status_str
  let created_by ← (Json.fieldN 3 json) >>= Json.asString
  let input_data ← (Json.fieldN 4 json) >>= Json.asString
  let requires_approval ← (Json.fieldN 5 json) >>= Json.asBool
  let created_at ← (Json.fieldN 6 json) >>= Json.asString
  let retry_count ← (Json.fieldN 7 json) >>= Json.asInt
  let max_retries ← (Json.fieldN 8 json) >>= Json.asInt
  let cost_usd ← (Json.fieldN 9 json) >>= Json.asFloat
  pure ⟨id, job_type, status, created_by, input_data, requires_approval,
        created_at, retry_count, max_retries, cost_usd⟩

theorem Job.roundtrip (j : Job) : Job.fromJson (Job.toJson j) = some j := by
  cases j with
  | mk id job_type status created_by input_data requires_approval created_at retry_count max_retries cost_usd =>
    cases status <;> rfl

instance : Extractable Job where
  encode := Job.toJson
  decode := Job.fromJson
  roundtrip := Job.roundtrip

/-! ## Job Invariants -/

/-- Retry count cannot exceed max -/
def Job.retryValid (j : Job) : Prop :=
  j.retry_count ≤ j.max_retries

end Compass.Jobs
