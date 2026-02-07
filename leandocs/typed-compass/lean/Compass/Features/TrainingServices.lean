import Compass.Core

/-!
  Training services
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure TrainingServices where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def TrainingServices.toJson (f : TrainingServices) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def TrainingServices.fromJson (j : Json) : Option TrainingServices := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem TrainingServices.roundtrip (f : TrainingServices) :
    TrainingServices.fromJson (TrainingServices.toJson f) = some f := by
  cases f; rfl

instance : Extractable TrainingServices where
  encode := TrainingServices.toJson
  decode := TrainingServices.fromJson
  roundtrip := TrainingServices.roundtrip

end Compass.Features
