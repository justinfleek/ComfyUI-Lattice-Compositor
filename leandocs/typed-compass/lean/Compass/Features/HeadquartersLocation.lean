import Compass.Core

/-!
  Headquarters location
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure HeadquartersLocation where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def HeadquartersLocation.toJson (f : HeadquartersLocation) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def HeadquartersLocation.fromJson (j : Json) : Option HeadquartersLocation := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem HeadquartersLocation.roundtrip (f : HeadquartersLocation) :
    HeadquartersLocation.fromJson (HeadquartersLocation.toJson f) = some f := by
  cases f; rfl

instance : Extractable HeadquartersLocation where
  encode := HeadquartersLocation.toJson
  decode := HeadquartersLocation.fromJson
  roundtrip := HeadquartersLocation.roundtrip

end Compass.Features
