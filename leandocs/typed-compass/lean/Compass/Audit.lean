/-
  Compass.Audit - Audit and provenance types with roundtrip proofs

  Maps to toolbox/core/types.py AuditRecord, ProvenanceNode, TransformationType.
-/

import Compass.Core

namespace Compass.Audit

open Compass.Core

/-! ## TransformationType Enum -/

inductive TransformationType where
  | SOURCE : TransformationType
  | SEARCH : TransformationType
  | SUMMARIZE : TransformationType
  | GENERATE : TransformationType
  | EDIT : TransformationType
  | MERGE : TransformationType
  | FORMAT : TransformationType
  deriving Repr, DecidableEq, Inhabited

def TransformationType.toString : TransformationType → String
  | .SOURCE => "SOURCE"
  | .SEARCH => "SEARCH"
  | .SUMMARIZE => "SUMMARIZE"
  | .GENERATE => "GENERATE"
  | .EDIT => "EDIT"
  | .MERGE => "MERGE"
  | .FORMAT => "FORMAT"

def TransformationType.fromString : String → Option TransformationType
  | "SOURCE" => some .SOURCE
  | "SEARCH" => some .SEARCH
  | "SUMMARIZE" => some .SUMMARIZE
  | "GENERATE" => some .GENERATE
  | "EDIT" => some .EDIT
  | "MERGE" => some .MERGE
  | "FORMAT" => some .FORMAT
  | _ => none

theorem transformation_type_roundtrip (t : TransformationType) :
    TransformationType.fromString (TransformationType.toString t) = some t := by
  cases t <;> rfl

instance : Extractable TransformationType where
  encode t := .str (TransformationType.toString t)
  decode j := do
    let s ← j.asString
    TransformationType.fromString s
  roundtrip t := by simp [Json.asString, transformation_type_roundtrip]

/-! ## AuditRecord -/

structure AuditRecord where
  id : String
  timestamp : DateTime
  event_type : String
  user_id : String
  user_role : String
  request_id : String
  input_hash : String
  success : Bool
  duration_ms : Int
  cost_usd : Float
  previous_hash : String
  record_hash : String
  deriving Repr

def AuditRecord.toJson (r : AuditRecord) : Json := .obj [
  ("id", .str r.id),
  ("timestamp", .str r.timestamp),
  ("event_type", .str r.event_type),
  ("user_id", .str r.user_id),
  ("user_role", .str r.user_role),
  ("request_id", .str r.request_id),
  ("input_hash", .str r.input_hash),
  ("success", .bool r.success),
  ("duration_ms", .int r.duration_ms),
  ("cost_usd", .num r.cost_usd),
  ("previous_hash", .str r.previous_hash),
  ("record_hash", .str r.record_hash)
]

def AuditRecord.fromJson (j : Json) : Option AuditRecord := do
  let id ← (Json.fieldN 0 j) >>= Json.asString
  let timestamp ← (Json.fieldN 1 j) >>= Json.asString
  let event_type ← (Json.fieldN 2 j) >>= Json.asString
  let user_id ← (Json.fieldN 3 j) >>= Json.asString
  let user_role ← (Json.fieldN 4 j) >>= Json.asString
  let request_id ← (Json.fieldN 5 j) >>= Json.asString
  let input_hash ← (Json.fieldN 6 j) >>= Json.asString
  let success ← (Json.fieldN 7 j) >>= Json.asBool
  let duration_ms ← (Json.fieldN 8 j) >>= Json.asInt
  let cost_usd ← (Json.fieldN 9 j) >>= Json.asFloat
  let previous_hash ← (Json.fieldN 10 j) >>= Json.asString
  let record_hash ← (Json.fieldN 11 j) >>= Json.asString
  pure ⟨id, timestamp, event_type, user_id, user_role, request_id,
        input_hash, success, duration_ms, cost_usd, previous_hash, record_hash⟩

theorem AuditRecord.roundtrip (r : AuditRecord) :
    AuditRecord.fromJson (AuditRecord.toJson r) = some r := by
  cases r; rfl

instance : Extractable AuditRecord where
  encode := AuditRecord.toJson
  decode := AuditRecord.fromJson
  roundtrip := AuditRecord.roundtrip

/-! ## ProvenanceNode -/

structure ProvenanceNode where
  id : String
  content_hash : String
  source_type : String
  captured_at : DateTime
  transformation : TransformationType
  deriving Repr

def ProvenanceNode.toJson (p : ProvenanceNode) : Json := .obj [
  ("id", .str p.id),
  ("content_hash", .str p.content_hash),
  ("source_type", .str p.source_type),
  ("captured_at", .str p.captured_at),
  ("transformation", .str (TransformationType.toString p.transformation))
]

def ProvenanceNode.fromJson (j : Json) : Option ProvenanceNode := do
  let id ← (Json.fieldN 0 j) >>= Json.asString
  let content_hash ← (Json.fieldN 1 j) >>= Json.asString
  let source_type ← (Json.fieldN 2 j) >>= Json.asString
  let captured_at ← (Json.fieldN 3 j) >>= Json.asString
  let trans_str ← (Json.fieldN 4 j) >>= Json.asString
  let transformation ← TransformationType.fromString trans_str
  pure ⟨id, content_hash, source_type, captured_at, transformation⟩

theorem ProvenanceNode.roundtrip (p : ProvenanceNode) :
    ProvenanceNode.fromJson (ProvenanceNode.toJson p) = some p := by
  cases p with
  | mk id content_hash source_type captured_at transformation =>
    cases transformation <;> rfl

instance : Extractable ProvenanceNode where
  encode := ProvenanceNode.toJson
  decode := ProvenanceNode.fromJson
  roundtrip := ProvenanceNode.roundtrip

/-! ## Audit Chain Invariants -/

/-- Each record's hash must chain to the previous -/
def AuditRecord.chainValid (prev next : AuditRecord) : Prop :=
  next.previous_hash = prev.record_hash

/-- Timestamp must be monotonically increasing in chain -/
def AuditRecord.timestampValid (prev next : AuditRecord) : Prop :=
  prev.timestamp ≤ next.timestamp

end Compass.Audit
