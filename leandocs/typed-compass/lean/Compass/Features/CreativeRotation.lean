import Compass.Core

/-!
  Creative rotation
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure CreativeRotation where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def CreativeRotation.toJson (f : CreativeRotation) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def CreativeRotation.fromJson (j : Json) : Option CreativeRotation := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem CreativeRotation.roundtrip (f : CreativeRotation) :
    CreativeRotation.fromJson (CreativeRotation.toJson f) = some f := by
  cases f; rfl

instance : Extractable CreativeRotation where
  encode := CreativeRotation.toJson
  decode := CreativeRotation.fromJson
  roundtrip := CreativeRotation.roundtrip

end Compass.Features
