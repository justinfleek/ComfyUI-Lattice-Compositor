import Compass.Core

/-!
  UTM templates
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure UtmTemplates where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def UtmTemplates.toJson (f : UtmTemplates) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def UtmTemplates.fromJson (j : Json) : Option UtmTemplates := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem UtmTemplates.roundtrip (f : UtmTemplates) :
    UtmTemplates.fromJson (UtmTemplates.toJson f) = some f := by
  cases f; rfl

instance : Extractable UtmTemplates where
  encode := UtmTemplates.toJson
  decode := UtmTemplates.fromJson
  roundtrip := UtmTemplates.roundtrip

end Compass.Features
