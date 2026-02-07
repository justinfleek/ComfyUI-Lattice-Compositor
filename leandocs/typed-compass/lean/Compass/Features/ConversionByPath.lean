import Compass.Core

/-!
  Conversion by path
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure ConversionByPath where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def ConversionByPath.toJson (f : ConversionByPath) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def ConversionByPath.fromJson (j : Json) : Option ConversionByPath := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem ConversionByPath.roundtrip (f : ConversionByPath) :
    ConversionByPath.fromJson (ConversionByPath.toJson f) = some f := by
  cases f; rfl

instance : Extractable ConversionByPath where
  encode := ConversionByPath.toJson
  decode := ConversionByPath.fromJson
  roundtrip := ConversionByPath.roundtrip

end Compass.Features
