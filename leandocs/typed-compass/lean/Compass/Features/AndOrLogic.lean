import Compass.Core

/-!
  AND/OR logic
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure AndOrLogic where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def AndOrLogic.toJson (f : AndOrLogic) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def AndOrLogic.fromJson (j : Json) : Option AndOrLogic := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem AndOrLogic.roundtrip (f : AndOrLogic) :
    AndOrLogic.fromJson (AndOrLogic.toJson f) = some f := by
  cases f; rfl

instance : Extractable AndOrLogic where
  encode := AndOrLogic.toJson
  decode := AndOrLogic.fromJson
  roundtrip := AndOrLogic.roundtrip

end Compass.Features
