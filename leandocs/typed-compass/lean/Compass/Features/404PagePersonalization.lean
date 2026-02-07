import Compass.Core

/-!
  404 page personalization
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure 404PagePersonalization where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def 404PagePersonalization.toJson (f : 404PagePersonalization) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def 404PagePersonalization.fromJson (j : Json) : Option 404PagePersonalization := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem 404PagePersonalization.roundtrip (f : 404PagePersonalization) :
    404PagePersonalization.fromJson (404PagePersonalization.toJson f) = some f := by
  cases f; rfl

instance : Extractable 404PagePersonalization where
  encode := 404PagePersonalization.toJson
  decode := 404PagePersonalization.fromJson
  roundtrip := 404PagePersonalization.roundtrip

end Compass.Features
