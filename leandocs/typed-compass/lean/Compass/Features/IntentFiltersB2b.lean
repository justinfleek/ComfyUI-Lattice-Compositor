import Compass.Core

/-!
  Intent filters (B2B)
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure IntentFiltersB2b where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def IntentFiltersB2b.toJson (f : IntentFiltersB2b) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def IntentFiltersB2b.fromJson (j : Json) : Option IntentFiltersB2b := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem IntentFiltersB2b.roundtrip (f : IntentFiltersB2b) :
    IntentFiltersB2b.fromJson (IntentFiltersB2b.toJson f) = some f := by
  cases f; rfl

instance : Extractable IntentFiltersB2b where
  encode := IntentFiltersB2b.toJson
  decode := IntentFiltersB2b.fromJson
  roundtrip := IntentFiltersB2b.roundtrip

end Compass.Features
