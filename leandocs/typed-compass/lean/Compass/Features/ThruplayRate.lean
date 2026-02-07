import Compass.Core

/-!
  ThruPlay rate
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure ThruplayRate where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def ThruplayRate.toJson (f : ThruplayRate) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def ThruplayRate.fromJson (j : Json) : Option ThruplayRate := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem ThruplayRate.roundtrip (f : ThruplayRate) :
    ThruplayRate.fromJson (ThruplayRate.toJson f) = some f := by
  cases f; rfl

instance : Extractable ThruplayRate where
  encode := ThruplayRate.toJson
  decode := ThruplayRate.fromJson
  roundtrip := ThruplayRate.roundtrip

end Compass.Features
