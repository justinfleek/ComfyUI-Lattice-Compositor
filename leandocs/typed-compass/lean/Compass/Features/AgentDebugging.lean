import Compass.Core

/-!
  Agent debugging
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure AgentDebugging where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def AgentDebugging.toJson (f : AgentDebugging) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def AgentDebugging.fromJson (j : Json) : Option AgentDebugging := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem AgentDebugging.roundtrip (f : AgentDebugging) :
    AgentDebugging.fromJson (AgentDebugging.toJson f) = some f := by
  cases f; rfl

instance : Extractable AgentDebugging where
  encode := AgentDebugging.toJson
  decode := AgentDebugging.fromJson
  roundtrip := AgentDebugging.roundtrip

end Compass.Features
