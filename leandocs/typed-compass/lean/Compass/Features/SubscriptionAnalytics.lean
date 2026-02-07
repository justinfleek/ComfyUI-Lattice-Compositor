import Compass.Core

/-!
  Subscription analytics
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure SubscriptionAnalytics where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def SubscriptionAnalytics.toJson (f : SubscriptionAnalytics) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def SubscriptionAnalytics.fromJson (j : Json) : Option SubscriptionAnalytics := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem SubscriptionAnalytics.roundtrip (f : SubscriptionAnalytics) :
    SubscriptionAnalytics.fromJson (SubscriptionAnalytics.toJson f) = some f := by
  cases f; rfl

instance : Extractable SubscriptionAnalytics where
  encode := SubscriptionAnalytics.toJson
  decode := SubscriptionAnalytics.fromJson
  roundtrip := SubscriptionAnalytics.roundtrip

end Compass.Features
