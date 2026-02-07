import Compass.Core

/-!
  Presenter video generation
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure PresenterVideoGeneration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def PresenterVideoGeneration.toJson (f : PresenterVideoGeneration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def PresenterVideoGeneration.fromJson (j : Json) : Option PresenterVideoGeneration := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem PresenterVideoGeneration.roundtrip (f : PresenterVideoGeneration) :
    PresenterVideoGeneration.fromJson (PresenterVideoGeneration.toJson f) = some f := by
  cases f; rfl

instance : Extractable PresenterVideoGeneration where
  encode := PresenterVideoGeneration.toJson
  decode := PresenterVideoGeneration.fromJson
  roundtrip := PresenterVideoGeneration.roundtrip

end Compass.Features
