import Compass.Core

/-!
  10DLC registration
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure 10dlcRegistration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def 10dlcRegistration.toJson (f : 10dlcRegistration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def 10dlcRegistration.fromJson (j : Json) : Option 10dlcRegistration := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem 10dlcRegistration.roundtrip (f : 10dlcRegistration) :
    10dlcRegistration.fromJson (10dlcRegistration.toJson f) = some f := by
  cases f; rfl

instance : Extractable 10dlcRegistration where
  encode := 10dlcRegistration.toJson
  decode := 10dlcRegistration.fromJson
  roundtrip := 10dlcRegistration.roundtrip

end Compass.Features
