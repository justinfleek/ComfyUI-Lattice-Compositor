import Compass.Core

/-!
  Personalized offers
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure PersonalizedOffers where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def PersonalizedOffers.toJson (f : PersonalizedOffers) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def PersonalizedOffers.fromJson (j : Json) : Option PersonalizedOffers := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem PersonalizedOffers.roundtrip (f : PersonalizedOffers) :
    PersonalizedOffers.fromJson (PersonalizedOffers.toJson f) = some f := by
  cases f; rfl

instance : Extractable PersonalizedOffers where
  encode := PersonalizedOffers.toJson
  decode := PersonalizedOffers.fromJson
  roundtrip := PersonalizedOffers.roundtrip

end Compass.Features
