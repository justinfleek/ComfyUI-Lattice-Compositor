import Compass.Core

/-!
  1:1 microsites
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure 11Microsites where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def 11Microsites.toJson (f : 11Microsites) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def 11Microsites.fromJson (j : Json) : Option 11Microsites := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem 11Microsites.roundtrip (f : 11Microsites) :
    11Microsites.fromJson (11Microsites.toJson f) = some f := by
  cases f; rfl

instance : Extractable 11Microsites where
  encode := 11Microsites.toJson
  decode := 11Microsites.fromJson
  roundtrip := 11Microsites.roundtrip

end Compass.Features
