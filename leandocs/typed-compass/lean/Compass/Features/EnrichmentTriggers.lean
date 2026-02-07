import Compass.Core

/-!
  Enrichment triggers
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure EnrichmentTriggers where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def EnrichmentTriggers.toJson (f : EnrichmentTriggers) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def EnrichmentTriggers.fromJson (j : Json) : Option EnrichmentTriggers := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem EnrichmentTriggers.roundtrip (f : EnrichmentTriggers) :
    EnrichmentTriggers.fromJson (EnrichmentTriggers.toJson f) = some f := by
  cases f; rfl

instance : Extractable EnrichmentTriggers where
  encode := EnrichmentTriggers.toJson
  decode := EnrichmentTriggers.fromJson
  roundtrip := EnrichmentTriggers.roundtrip

end Compass.Features
