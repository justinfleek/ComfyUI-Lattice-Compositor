import Compass.Core

/-!
  Impressions by creative
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure ImpressionsByCreative where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def ImpressionsByCreative.toJson (f : ImpressionsByCreative) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def ImpressionsByCreative.fromJson (j : Json) : Option ImpressionsByCreative := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem ImpressionsByCreative.roundtrip (f : ImpressionsByCreative) :
    ImpressionsByCreative.fromJson (ImpressionsByCreative.toJson f) = some f := by
  cases f; rfl

instance : Extractable ImpressionsByCreative where
  encode := ImpressionsByCreative.toJson
  decode := ImpressionsByCreative.fromJson
  roundtrip := ImpressionsByCreative.roundtrip

end Compass.Features
