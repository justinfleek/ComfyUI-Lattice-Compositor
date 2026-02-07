import Compass.Core

/-!
  Webhooks (inbound)
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure WebhooksInbound where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def WebhooksInbound.toJson (f : WebhooksInbound) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def WebhooksInbound.fromJson (j : Json) : Option WebhooksInbound := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem WebhooksInbound.roundtrip (f : WebhooksInbound) :
    WebhooksInbound.fromJson (WebhooksInbound.toJson f) = some f := by
  cases f; rfl

instance : Extractable WebhooksInbound where
  encode := WebhooksInbound.toJson
  decode := WebhooksInbound.fromJson
  roundtrip := WebhooksInbound.roundtrip

end Compass.Features
