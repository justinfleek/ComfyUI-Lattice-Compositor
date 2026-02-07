import Compass.Core

/-!
  Data quality trends
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure DataQualityTrends where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def DataQualityTrends.toJson (f : DataQualityTrends) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def DataQualityTrends.fromJson (j : Json) : Option DataQualityTrends := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem DataQualityTrends.roundtrip (f : DataQualityTrends) :
    DataQualityTrends.fromJson (DataQualityTrends.toJson f) = some f := by
  cases f; rfl

instance : Extractable DataQualityTrends where
  encode := DataQualityTrends.toJson
  decode := DataQualityTrends.fromJson
  roundtrip := DataQualityTrends.roundtrip

end Compass.Features
