import Compass.Core

/-!
  Cross-journey orchestration
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure CrossJourneyOrchestration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def CrossJourneyOrchestration.toJson (f : CrossJourneyOrchestration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def CrossJourneyOrchestration.fromJson (j : Json) : Option CrossJourneyOrchestration := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem CrossJourneyOrchestration.roundtrip (f : CrossJourneyOrchestration) :
    CrossJourneyOrchestration.fromJson (CrossJourneyOrchestration.toJson f) = some f := by
  cases f; rfl

instance : Extractable CrossJourneyOrchestration where
  encode := CrossJourneyOrchestration.toJson
  decode := CrossJourneyOrchestration.fromJson
  roundtrip := CrossJourneyOrchestration.roundtrip

end Compass.Features
