import Compass.Core

/-!
  DV360 integration
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure Dv360Integration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def Dv360Integration.toJson (f : Dv360Integration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def Dv360Integration.fromJson (j : Json) : Option Dv360Integration := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem Dv360Integration.roundtrip (f : Dv360Integration) :
    Dv360Integration.fromJson (Dv360Integration.toJson f) = some f := by
  cases f; rfl

instance : Extractable Dv360Integration where
  encode := Dv360Integration.toJson
  decode := Dv360Integration.fromJson
  roundtrip := Dv360Integration.roundtrip

end Compass.Features
