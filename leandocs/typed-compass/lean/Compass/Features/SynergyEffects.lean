import Compass.Core

/-!
  Synergy effects
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure SynergyEffects where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def SynergyEffects.toJson (f : SynergyEffects) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def SynergyEffects.fromJson (j : Json) : Option SynergyEffects := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem SynergyEffects.roundtrip (f : SynergyEffects) :
    SynergyEffects.fromJson (SynergyEffects.toJson f) = some f := by
  cases f; rfl

instance : Extractable SynergyEffects where
  encode := SynergyEffects.toJson
  decode := SynergyEffects.fromJson
  roundtrip := SynergyEffects.roundtrip

end Compass.Features
