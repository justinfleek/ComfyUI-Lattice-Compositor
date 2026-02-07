import Compass.Core

/-!
  Hashed email matching
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure HashedEmailMatching where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def HashedEmailMatching.toJson (f : HashedEmailMatching) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def HashedEmailMatching.fromJson (j : Json) : Option HashedEmailMatching := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem HashedEmailMatching.roundtrip (f : HashedEmailMatching) :
    HashedEmailMatching.fromJson (HashedEmailMatching.toJson f) = some f := by
  cases f; rfl

instance : Extractable HashedEmailMatching where
  encode := HashedEmailMatching.toJson
  decode := HashedEmailMatching.fromJson
  roundtrip := HashedEmailMatching.roundtrip

end Compass.Features
