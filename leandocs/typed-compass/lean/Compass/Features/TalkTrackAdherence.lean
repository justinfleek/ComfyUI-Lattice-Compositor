import Compass.Core

/-!
  Talk track adherence
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure TalkTrackAdherence where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def TalkTrackAdherence.toJson (f : TalkTrackAdherence) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def TalkTrackAdherence.fromJson (j : Json) : Option TalkTrackAdherence := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem TalkTrackAdherence.roundtrip (f : TalkTrackAdherence) :
    TalkTrackAdherence.fromJson (TalkTrackAdherence.toJson f) = some f := by
  cases f; rfl

instance : Extractable TalkTrackAdherence where
  encode := TalkTrackAdherence.toJson
  decode := TalkTrackAdherence.fromJson
  roundtrip := TalkTrackAdherence.roundtrip

end Compass.Features
