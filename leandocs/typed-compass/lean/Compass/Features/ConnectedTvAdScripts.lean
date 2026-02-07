import Compass.Core

/-!
  Connected TV ad scripts
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure ConnectedTvAdScripts where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def ConnectedTvAdScripts.toJson (f : ConnectedTvAdScripts) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def ConnectedTvAdScripts.fromJson (j : Json) : Option ConnectedTvAdScripts := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem ConnectedTvAdScripts.roundtrip (f : ConnectedTvAdScripts) :
    ConnectedTvAdScripts.fromJson (ConnectedTvAdScripts.toJson f) = some f := by
  cases f; rfl

instance : Extractable ConnectedTvAdScripts where
  encode := ConnectedTvAdScripts.toJson
  decode := ConnectedTvAdScripts.fromJson
  roundtrip := ConnectedTvAdScripts.roundtrip

end Compass.Features
