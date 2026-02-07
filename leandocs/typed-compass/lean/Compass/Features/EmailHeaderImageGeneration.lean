import Compass.Core

/-!
  Email header image generation
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure EmailHeaderImageGeneration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def EmailHeaderImageGeneration.toJson (f : EmailHeaderImageGeneration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def EmailHeaderImageGeneration.fromJson (j : Json) : Option EmailHeaderImageGeneration := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem EmailHeaderImageGeneration.roundtrip (f : EmailHeaderImageGeneration) :
    EmailHeaderImageGeneration.fromJson (EmailHeaderImageGeneration.toJson f) = some f := by
  cases f; rfl

instance : Extractable EmailHeaderImageGeneration where
  encode := EmailHeaderImageGeneration.toJson
  decode := EmailHeaderImageGeneration.fromJson
  roundtrip := EmailHeaderImageGeneration.roundtrip

end Compass.Features
