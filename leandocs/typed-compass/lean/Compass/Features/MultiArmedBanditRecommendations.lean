import Compass.Core

/-!
  Multi-armed bandit recommendations
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure MultiArmedBanditRecommendations where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def MultiArmedBanditRecommendations.toJson (f : MultiArmedBanditRecommendations) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def MultiArmedBanditRecommendations.fromJson (j : Json) : Option MultiArmedBanditRecommendations := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem MultiArmedBanditRecommendations.roundtrip (f : MultiArmedBanditRecommendations) :
    MultiArmedBanditRecommendations.fromJson (MultiArmedBanditRecommendations.toJson f) = some f := by
  cases f; rfl

instance : Extractable MultiArmedBanditRecommendations where
  encode := MultiArmedBanditRecommendations.toJson
  decode := MultiArmedBanditRecommendations.fromJson
  roundtrip := MultiArmedBanditRecommendations.roundtrip

end Compass.Features
