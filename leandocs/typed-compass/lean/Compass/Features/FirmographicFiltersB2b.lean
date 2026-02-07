import Compass.Core

/-!
  Firmographic filters (B2B)
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure FirmographicFiltersB2b where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def FirmographicFiltersB2b.toJson (f : FirmographicFiltersB2b) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def FirmographicFiltersB2b.fromJson (j : Json) : Option FirmographicFiltersB2b := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem FirmographicFiltersB2b.roundtrip (f : FirmographicFiltersB2b) :
    FirmographicFiltersB2b.fromJson (FirmographicFiltersB2b.toJson f) = some f := by
  cases f; rfl

instance : Extractable FirmographicFiltersB2b where
  encode := FirmographicFiltersB2b.toJson
  decode := FirmographicFiltersB2b.fromJson
  roundtrip := FirmographicFiltersB2b.roundtrip

end Compass.Features
