import Compass.Core

/-!
  ISO 27001
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure Iso27001 where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def Iso27001.toJson (f : Iso27001) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def Iso27001.fromJson (j : Json) : Option Iso27001 := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem Iso27001.roundtrip (f : Iso27001) :
    Iso27001.fromJson (Iso27001.toJson f) = some f := by
  cases f; rfl

instance : Extractable Iso27001 where
  encode := Iso27001.toJson
  decode := Iso27001.fromJson
  roundtrip := Iso27001.roundtrip

end Compass.Features
