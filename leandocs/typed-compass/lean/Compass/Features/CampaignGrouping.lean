import Compass.Core

/-!
  Campaign grouping
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure CampaignGrouping where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def CampaignGrouping.toJson (f : CampaignGrouping) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def CampaignGrouping.fromJson (j : Json) : Option CampaignGrouping := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem CampaignGrouping.roundtrip (f : CampaignGrouping) :
    CampaignGrouping.fromJson (CampaignGrouping.toJson f) = some f := by
  cases f; rfl

instance : Extractable CampaignGrouping where
  encode := CampaignGrouping.toJson
  decode := CampaignGrouping.fromJson
  roundtrip := CampaignGrouping.roundtrip

end Compass.Features
