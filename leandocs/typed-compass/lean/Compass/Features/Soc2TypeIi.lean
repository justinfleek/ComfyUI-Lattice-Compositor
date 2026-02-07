import Compass.Core

/-!
  SOC 2 Type II
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure Soc2TypeIi where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def Soc2TypeIi.toJson (f : Soc2TypeIi) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def Soc2TypeIi.fromJson (j : Json) : Option Soc2TypeIi := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem Soc2TypeIi.roundtrip (f : Soc2TypeIi) :
    Soc2TypeIi.fromJson (Soc2TypeIi.toJson f) = some f := by
  cases f; rfl

instance : Extractable Soc2TypeIi where
  encode := Soc2TypeIi.toJson
  decode := Soc2TypeIi.fromJson
  roundtrip := Soc2TypeIi.roundtrip

end Compass.Features
