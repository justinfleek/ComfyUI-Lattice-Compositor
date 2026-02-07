import Compass.Core

/-!
  SLA management
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure SlaManagement where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def SlaManagement.toJson (f : SlaManagement) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def SlaManagement.fromJson (j : Json) : Option SlaManagement := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem SlaManagement.roundtrip (f : SlaManagement) :
    SlaManagement.fromJson (SlaManagement.toJson f) = some f := by
  cases f; rfl

instance : Extractable SlaManagement where
  encode := SlaManagement.toJson
  decode := SlaManagement.fromJson
  roundtrip := SlaManagement.roundtrip

end Compass.Features
