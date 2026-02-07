import Compass.Core

/-!
  Channel selection
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure ChannelSelection where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def ChannelSelection.toJson (f : ChannelSelection) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def ChannelSelection.fromJson (j : Json) : Option ChannelSelection := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem ChannelSelection.roundtrip (f : ChannelSelection) :
    ChannelSelection.fromJson (ChannelSelection.toJson f) = some f := by
  cases f; rfl

instance : Extractable ChannelSelection where
  encode := ChannelSelection.toJson
  decode := ChannelSelection.fromJson
  roundtrip := ChannelSelection.roundtrip

end Compass.Features
