import Compass.Core

/-!
  WhatsApp automation
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure WhatsappAutomation where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def WhatsappAutomation.toJson (f : WhatsappAutomation) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def WhatsappAutomation.fromJson (j : Json) : Option WhatsappAutomation := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem WhatsappAutomation.roundtrip (f : WhatsappAutomation) :
    WhatsappAutomation.fromJson (WhatsappAutomation.toJson f) = some f := by
  cases f; rfl

instance : Extractable WhatsappAutomation where
  encode := WhatsappAutomation.toJson
  decode := WhatsappAutomation.fromJson
  roundtrip := WhatsappAutomation.roundtrip

end Compass.Features
