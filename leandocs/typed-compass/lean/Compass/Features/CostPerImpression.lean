import Compass.Core

/-!
  Cost per impression
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure CostPerImpression where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def CostPerImpression.toJson (f : CostPerImpression) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def CostPerImpression.fromJson (j : Json) : Option CostPerImpression := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem CostPerImpression.roundtrip (f : CostPerImpression) :
    CostPerImpression.fromJson (CostPerImpression.toJson f) = some f := by
  cases f; rfl

instance : Extractable CostPerImpression where
  encode := CostPerImpression.toJson
  decode := CostPerImpression.fromJson
  roundtrip := CostPerImpression.roundtrip

end Compass.Features
