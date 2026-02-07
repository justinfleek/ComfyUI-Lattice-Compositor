import Compass.Core

/-!
  Account firmographics
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure AccountFirmographics where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def AccountFirmographics.toJson (f : AccountFirmographics) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def AccountFirmographics.fromJson (j : Json) : Option AccountFirmographics := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem AccountFirmographics.roundtrip (f : AccountFirmographics) :
    AccountFirmographics.fromJson (AccountFirmographics.toJson f) = some f := by
  cases f; rfl

instance : Extractable AccountFirmographics where
  encode := AccountFirmographics.toJson
  decode := AccountFirmographics.fromJson
  roundtrip := AccountFirmographics.roundtrip

end Compass.Features
