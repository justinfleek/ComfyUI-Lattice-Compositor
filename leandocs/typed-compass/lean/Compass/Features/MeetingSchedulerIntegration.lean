import Compass.Core

/-!
  Meeting scheduler integration
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure MeetingSchedulerIntegration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def MeetingSchedulerIntegration.toJson (f : MeetingSchedulerIntegration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def MeetingSchedulerIntegration.fromJson (j : Json) : Option MeetingSchedulerIntegration := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem MeetingSchedulerIntegration.roundtrip (f : MeetingSchedulerIntegration) :
    MeetingSchedulerIntegration.fromJson (MeetingSchedulerIntegration.toJson f) = some f := by
  cases f; rfl

instance : Extractable MeetingSchedulerIntegration where
  encode := MeetingSchedulerIntegration.toJson
  decode := MeetingSchedulerIntegration.fromJson
  roundtrip := MeetingSchedulerIntegration.roundtrip

end Compass.Features
