import Compass.Core

/-!
  Hook rate (3-second views)
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure HookRate3SecondViews where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def HookRate3SecondViews.toJson (f : HookRate3SecondViews) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def HookRate3SecondViews.fromJson (j : Json) : Option HookRate3SecondViews := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem HookRate3SecondViews.roundtrip (f : HookRate3SecondViews) :
    HookRate3SecondViews.fromJson (HookRate3SecondViews.toJson f) = some f := by
  cases f; rfl

instance : Extractable HookRate3SecondViews where
  encode := HookRate3SecondViews.toJson
  decode := HookRate3SecondViews.fromJson
  roundtrip := HookRate3SecondViews.roundtrip

end Compass.Features
