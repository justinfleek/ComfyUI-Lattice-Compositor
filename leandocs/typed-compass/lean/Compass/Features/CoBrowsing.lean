import Compass.Core

/-!
  Co-browsing
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure CoBrowsing where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def CoBrowsing.toJson (f : CoBrowsing) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def CoBrowsing.fromJson (j : Json) : Option CoBrowsing := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem CoBrowsing.roundtrip (f : CoBrowsing) :
    CoBrowsing.fromJson (CoBrowsing.toJson f) = some f := by
  cases f; rfl

instance : Extractable CoBrowsing where
  encode := CoBrowsing.toJson
  decode := CoBrowsing.fromJson
  roundtrip := CoBrowsing.roundtrip

end Compass.Features
