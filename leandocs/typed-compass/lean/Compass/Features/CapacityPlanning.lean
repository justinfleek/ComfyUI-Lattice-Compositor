import Compass.Core

/-!
  Capacity planning
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure CapacityPlanning where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def CapacityPlanning.toJson (f : CapacityPlanning) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def CapacityPlanning.fromJson (j : Json) : Option CapacityPlanning := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem CapacityPlanning.roundtrip (f : CapacityPlanning) :
    CapacityPlanning.fromJson (CapacityPlanning.toJson f) = some f := by
  cases f; rfl

instance : Extractable CapacityPlanning where
  encode := CapacityPlanning.toJson
  decode := CapacityPlanning.fromJson
  roundtrip := CapacityPlanning.roundtrip

end Compass.Features
