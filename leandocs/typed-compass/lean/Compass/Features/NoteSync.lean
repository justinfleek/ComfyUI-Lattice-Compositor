import Compass.Core

/-!
  Note sync
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure NoteSync where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def NoteSync.toJson (f : NoteSync) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def NoteSync.fromJson (j : Json) : Option NoteSync := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem NoteSync.roundtrip (f : NoteSync) :
    NoteSync.fromJson (NoteSync.toJson f) = some f := by
  cases f; rfl

instance : Extractable NoteSync where
  encode := NoteSync.toJson
  decode := NoteSync.fromJson
  roundtrip := NoteSync.roundtrip

end Compass.Features
