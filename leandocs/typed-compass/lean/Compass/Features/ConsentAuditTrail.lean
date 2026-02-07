import Compass.Core

/-!
  Consent audit trail
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure ConsentAuditTrail where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def ConsentAuditTrail.toJson (f : ConsentAuditTrail) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def ConsentAuditTrail.fromJson (j : Json) : Option ConsentAuditTrail := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem ConsentAuditTrail.roundtrip (f : ConsentAuditTrail) :
    ConsentAuditTrail.fromJson (ConsentAuditTrail.toJson f) = some f := by
  cases f; rfl

instance : Extractable ConsentAuditTrail where
  encode := ConsentAuditTrail.toJson
  decode := ConsentAuditTrail.fromJson
  roundtrip := ConsentAuditTrail.roundtrip

end Compass.Features
