import Compass.Core

/-!
  High availability (HA)
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure HighAvailabilityHa where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def HighAvailabilityHa.toJson (f : HighAvailabilityHa) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def HighAvailabilityHa.fromJson (j : Json) : Option HighAvailabilityHa := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem HighAvailabilityHa.roundtrip (f : HighAvailabilityHa) :
    HighAvailabilityHa.fromJson (HighAvailabilityHa.toJson f) = some f := by
  cases f; rfl

instance : Extractable HighAvailabilityHa where
  encode := HighAvailabilityHa.toJson
  decode := HighAvailabilityHa.fromJson
  roundtrip := HighAvailabilityHa.roundtrip

end Compass.Features
