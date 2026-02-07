import Compass.Core

/-!
  White-labeled reports
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure WhiteLabeledReports where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def WhiteLabeledReports.toJson (f : WhiteLabeledReports) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def WhiteLabeledReports.fromJson (j : Json) : Option WhiteLabeledReports := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem WhiteLabeledReports.roundtrip (f : WhiteLabeledReports) :
    WhiteLabeledReports.fromJson (WhiteLabeledReports.toJson f) = some f := by
  cases f; rfl

instance : Extractable WhiteLabeledReports where
  encode := WhiteLabeledReports.toJson
  decode := WhiteLabeledReports.fromJson
  roundtrip := WhiteLabeledReports.roundtrip

end Compass.Features
