import Compass.Core

/-!
  Usage analytics
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure UsageAnalytics where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def UsageAnalytics.toJson (f : UsageAnalytics) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def UsageAnalytics.fromJson (j : Json) : Option UsageAnalytics := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem UsageAnalytics.roundtrip (f : UsageAnalytics) :
    UsageAnalytics.fromJson (UsageAnalytics.toJson f) = some f := by
  cases f; rfl

instance : Extractable UsageAnalytics where
  encode := UsageAnalytics.toJson
  decode := UsageAnalytics.fromJson
  roundtrip := UsageAnalytics.roundtrip

end Compass.Features
