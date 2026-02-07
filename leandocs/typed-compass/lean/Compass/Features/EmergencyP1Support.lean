import Compass.Core

/-!
  Emergency/P1 support
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure EmergencyP1Support where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def EmergencyP1Support.toJson (f : EmergencyP1Support) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def EmergencyP1Support.fromJson (j : Json) : Option EmergencyP1Support := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem EmergencyP1Support.roundtrip (f : EmergencyP1Support) :
    EmergencyP1Support.fromJson (EmergencyP1Support.toJson f) = some f := by
  cases f; rfl

instance : Extractable EmergencyP1Support where
  encode := EmergencyP1Support.toJson
  decode := EmergencyP1Support.fromJson
  roundtrip := EmergencyP1Support.roundtrip

end Compass.Features
