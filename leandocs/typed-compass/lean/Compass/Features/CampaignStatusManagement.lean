import Compass.Core

/-!
  Campaign status management
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure CampaignStatusManagement where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def CampaignStatusManagement.toJson (f : CampaignStatusManagement) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def CampaignStatusManagement.fromJson (j : Json) : Option CampaignStatusManagement := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem CampaignStatusManagement.roundtrip (f : CampaignStatusManagement) :
    CampaignStatusManagement.fromJson (CampaignStatusManagement.toJson f) = some f := by
  cases f; rfl

instance : Extractable CampaignStatusManagement where
  encode := CampaignStatusManagement.toJson
  decode := CampaignStatusManagement.fromJson
  roundtrip := CampaignStatusManagement.roundtrip

end Compass.Features
