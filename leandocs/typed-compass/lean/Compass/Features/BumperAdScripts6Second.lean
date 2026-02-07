import Compass.Core

/-!
  Bumper ad scripts (6-second)
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure BumperAdScripts6Second where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def BumperAdScripts6Second.toJson (f : BumperAdScripts6Second) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def BumperAdScripts6Second.fromJson (j : Json) : Option BumperAdScripts6Second := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem BumperAdScripts6Second.roundtrip (f : BumperAdScripts6Second) :
    BumperAdScripts6Second.fromJson (BumperAdScripts6Second.toJson f) = some f := by
  cases f; rfl

instance : Extractable BumperAdScripts6Second where
  encode := BumperAdScripts6Second.toJson
  decode := BumperAdScripts6Second.fromJson
  roundtrip := BumperAdScripts6Second.roundtrip

end Compass.Features
