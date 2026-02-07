import Compass.Core

/-!
  Action nodes (send push)
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure ActionNodesSendPush where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def ActionNodesSendPush.toJson (f : ActionNodesSendPush) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def ActionNodesSendPush.fromJson (j : Json) : Option ActionNodesSendPush := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem ActionNodesSendPush.roundtrip (f : ActionNodesSendPush) :
    ActionNodesSendPush.fromJson (ActionNodesSendPush.toJson f) = some f := by
  cases f; rfl

instance : Extractable ActionNodesSendPush where
  encode := ActionNodesSendPush.toJson
  decode := ActionNodesSendPush.fromJson
  roundtrip := ActionNodesSendPush.roundtrip

end Compass.Features
