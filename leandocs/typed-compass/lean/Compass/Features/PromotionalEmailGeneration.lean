import Compass.Core

/-!
  Promotional email generation
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure PromotionalEmailGeneration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def PromotionalEmailGeneration.toJson (f : PromotionalEmailGeneration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def PromotionalEmailGeneration.fromJson (j : Json) : Option PromotionalEmailGeneration := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem PromotionalEmailGeneration.roundtrip (f : PromotionalEmailGeneration) :
    PromotionalEmailGeneration.fromJson (PromotionalEmailGeneration.toJson f) = some f := by
  cases f; rfl

instance : Extractable PromotionalEmailGeneration where
  encode := PromotionalEmailGeneration.toJson
  decode := PromotionalEmailGeneration.fromJson
  roundtrip := PromotionalEmailGeneration.roundtrip

end Compass.Features
