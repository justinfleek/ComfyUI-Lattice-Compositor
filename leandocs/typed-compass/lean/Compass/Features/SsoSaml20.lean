import Compass.Core

/-!
  SSO (SAML 2.0)
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure SsoSaml20 where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def SsoSaml20.toJson (f : SsoSaml20) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def SsoSaml20.fromJson (j : Json) : Option SsoSaml20 := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem SsoSaml20.roundtrip (f : SsoSaml20) :
    SsoSaml20.fromJson (SsoSaml20.toJson f) = some f := by
  cases f; rfl

instance : Extractable SsoSaml20 where
  encode := SsoSaml20.toJson
  decode := SsoSaml20.fromJson
  roundtrip := SsoSaml20.roundtrip

end Compass.Features
