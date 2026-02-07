import Compass.Core

/-!
  Graph-based recommendations
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure GraphBasedRecommendations where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def GraphBasedRecommendations.toJson (f : GraphBasedRecommendations) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def GraphBasedRecommendations.fromJson (j : Json) : Option GraphBasedRecommendations := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem GraphBasedRecommendations.roundtrip (f : GraphBasedRecommendations) :
    GraphBasedRecommendations.fromJson (GraphBasedRecommendations.toJson f) = some f := by
  cases f; rfl

instance : Extractable GraphBasedRecommendations where
  encode := GraphBasedRecommendations.toJson
  decode := GraphBasedRecommendations.fromJson
  roundtrip := GraphBasedRecommendations.roundtrip

end Compass.Features
