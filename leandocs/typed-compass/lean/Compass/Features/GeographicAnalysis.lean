import Compass.Core

/-!
  Geographic analysis
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure GeographicAnalysis where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def GeographicAnalysis.toJson (f : GeographicAnalysis) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def GeographicAnalysis.fromJson (j : Json) : Option GeographicAnalysis := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem GeographicAnalysis.roundtrip (f : GeographicAnalysis) :
    GeographicAnalysis.fromJson (GeographicAnalysis.toJson f) = some f := by
  cases f; rfl

instance : Extractable GeographicAnalysis where
  encode := GeographicAnalysis.toJson
  decode := GeographicAnalysis.fromJson
  roundtrip := GeographicAnalysis.roundtrip

end Compass.Features
