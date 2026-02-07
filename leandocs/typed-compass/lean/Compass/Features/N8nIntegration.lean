import Compass.Core

/-!
  n8n integration
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure N8nIntegration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def N8nIntegration.toJson (f : N8nIntegration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def N8nIntegration.fromJson (j : Json) : Option N8nIntegration := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem N8nIntegration.roundtrip (f : N8nIntegration) :
    N8nIntegration.fromJson (N8nIntegration.toJson f) = some f := by
  cases f; rfl

instance : Extractable N8nIntegration where
  encode := N8nIntegration.toJson
  decode := N8nIntegration.fromJson
  roundtrip := N8nIntegration.roundtrip

end Compass.Features
