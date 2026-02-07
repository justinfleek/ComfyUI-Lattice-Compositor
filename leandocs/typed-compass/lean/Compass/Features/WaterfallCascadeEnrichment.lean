import Compass.Core

/-!
  Waterfall/cascade enrichment
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure WaterfallCascadeEnrichment where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def WaterfallCascadeEnrichment.toJson (f : WaterfallCascadeEnrichment) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def WaterfallCascadeEnrichment.fromJson (j : Json) : Option WaterfallCascadeEnrichment := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem WaterfallCascadeEnrichment.roundtrip (f : WaterfallCascadeEnrichment) :
    WaterfallCascadeEnrichment.fromJson (WaterfallCascadeEnrichment.toJson f) = some f := by
  cases f; rfl

instance : Extractable WaterfallCascadeEnrichment where
  encode := WaterfallCascadeEnrichment.toJson
  decode := WaterfallCascadeEnrichment.fromJson
  roundtrip := WaterfallCascadeEnrichment.roundtrip

end Compass.Features
