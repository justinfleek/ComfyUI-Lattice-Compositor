import Compass.Core

/-!
  TLS 1.2/1.3
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure Tls1213 where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def Tls1213.toJson (f : Tls1213) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def Tls1213.fromJson (j : Json) : Option Tls1213 := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem Tls1213.roundtrip (f : Tls1213) :
    Tls1213.fromJson (Tls1213.toJson f) = some f := by
  cases f; rfl

instance : Extractable Tls1213 where
  encode := Tls1213.toJson
  decode := Tls1213.fromJson
  roundtrip := Tls1213.roundtrip

end Compass.Features
