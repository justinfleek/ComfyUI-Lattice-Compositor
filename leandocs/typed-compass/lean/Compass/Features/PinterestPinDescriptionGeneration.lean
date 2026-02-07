import Compass.Core

/-!
  Pinterest pin description generation
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure PinterestPinDescriptionGeneration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def PinterestPinDescriptionGeneration.toJson (f : PinterestPinDescriptionGeneration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def PinterestPinDescriptionGeneration.fromJson (j : Json) : Option PinterestPinDescriptionGeneration := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem PinterestPinDescriptionGeneration.roundtrip (f : PinterestPinDescriptionGeneration) :
    PinterestPinDescriptionGeneration.fromJson (PinterestPinDescriptionGeneration.toJson f) = some f := by
  cases f; rfl

instance : Extractable PinterestPinDescriptionGeneration where
  encode := PinterestPinDescriptionGeneration.toJson
  decode := PinterestPinDescriptionGeneration.fromJson
  roundtrip := PinterestPinDescriptionGeneration.roundtrip

end Compass.Features
