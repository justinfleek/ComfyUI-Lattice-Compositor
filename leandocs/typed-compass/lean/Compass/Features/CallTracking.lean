import Compass.Core

/-!
  Call tracking
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure CallTracking where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def CallTracking.toJson (f : CallTracking) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def CallTracking.fromJson (j : Json) : Option CallTracking := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem CallTracking.roundtrip (f : CallTracking) :
    CallTracking.fromJson (CallTracking.toJson f) = some f := by
  cases f; rfl

instance : Extractable CallTracking where
  encode := CallTracking.toJson
  decode := CallTracking.fromJson
  roundtrip := CallTracking.roundtrip

end Compass.Features
