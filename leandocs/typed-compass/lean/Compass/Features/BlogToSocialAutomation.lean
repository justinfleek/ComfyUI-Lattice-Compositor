import Compass.Core

/-!
  Blog to social automation
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure BlogToSocialAutomation where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def BlogToSocialAutomation.toJson (f : BlogToSocialAutomation) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def BlogToSocialAutomation.fromJson (j : Json) : Option BlogToSocialAutomation := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem BlogToSocialAutomation.roundtrip (f : BlogToSocialAutomation) :
    BlogToSocialAutomation.fromJson (BlogToSocialAutomation.toJson f) = some f := by
  cases f; rfl

instance : Extractable BlogToSocialAutomation where
  encode := BlogToSocialAutomation.toJson
  decode := BlogToSocialAutomation.fromJson
  roundtrip := BlogToSocialAutomation.roundtrip

end Compass.Features
