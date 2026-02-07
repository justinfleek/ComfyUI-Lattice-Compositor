import Compass.Core

/-!
  99.9%+ uptime SLA
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure 999UptimeSla where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def 999UptimeSla.toJson (f : 999UptimeSla) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def 999UptimeSla.fromJson (j : Json) : Option 999UptimeSla := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem 999UptimeSla.roundtrip (f : 999UptimeSla) :
    999UptimeSla.fromJson (999UptimeSla.toJson f) = some f := by
  cases f; rfl

instance : Extractable 999UptimeSla where
  encode := 999UptimeSla.toJson
  decode := 999UptimeSla.fromJson
  roundtrip := 999UptimeSla.roundtrip

end Compass.Features
