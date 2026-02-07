import Compass.Core

/-!
  Template library
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure TemplateLibrary where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def TemplateLibrary.toJson (f : TemplateLibrary) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def TemplateLibrary.fromJson (j : Json) : Option TemplateLibrary := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem TemplateLibrary.roundtrip (f : TemplateLibrary) :
    TemplateLibrary.fromJson (TemplateLibrary.toJson f) = some f := by
  cases f; rfl

instance : Extractable TemplateLibrary where
  encode := TemplateLibrary.toJson
  decode := TemplateLibrary.fromJson
  roundtrip := TemplateLibrary.roundtrip

end Compass.Features
