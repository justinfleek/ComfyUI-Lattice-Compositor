import Compass.Core

/-!
  B2B order handling
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure B2bOrderHandling where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def B2bOrderHandling.toJson (f : B2bOrderHandling) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def B2bOrderHandling.fromJson (j : Json) : Option B2bOrderHandling := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem B2bOrderHandling.roundtrip (f : B2bOrderHandling) :
    B2bOrderHandling.fromJson (B2bOrderHandling.toJson f) = some f := by
  cases f; rfl

instance : Extractable B2bOrderHandling where
  encode := B2bOrderHandling.toJson
  decode := B2bOrderHandling.fromJson
  roundtrip := B2bOrderHandling.roundtrip

end Compass.Features
