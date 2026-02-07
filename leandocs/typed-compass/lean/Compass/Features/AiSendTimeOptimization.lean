import Compass.Core

/-!
  AI send time optimization
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure AiSendTimeOptimization where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def AiSendTimeOptimization.toJson (f : AiSendTimeOptimization) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def AiSendTimeOptimization.fromJson (j : Json) : Option AiSendTimeOptimization := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem AiSendTimeOptimization.roundtrip (f : AiSendTimeOptimization) :
    AiSendTimeOptimization.fromJson (AiSendTimeOptimization.toJson f) = some f := by
  cases f; rfl

instance : Extractable AiSendTimeOptimization where
  encode := AiSendTimeOptimization.toJson
  decode := AiSendTimeOptimization.fromJson
  roundtrip := AiSendTimeOptimization.roundtrip

end Compass.Features
