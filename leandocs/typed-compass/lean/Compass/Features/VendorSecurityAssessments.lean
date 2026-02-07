import Compass.Core

/-!
  Vendor security assessments
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure VendorSecurityAssessments where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def VendorSecurityAssessments.toJson (f : VendorSecurityAssessments) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def VendorSecurityAssessments.fromJson (j : Json) : Option VendorSecurityAssessments := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem VendorSecurityAssessments.roundtrip (f : VendorSecurityAssessments) :
    VendorSecurityAssessments.fromJson (VendorSecurityAssessments.toJson f) = some f := by
  cases f; rfl

instance : Extractable VendorSecurityAssessments where
  encode := VendorSecurityAssessments.toJson
  decode := VendorSecurityAssessments.fromJson
  roundtrip := VendorSecurityAssessments.roundtrip

end Compass.Features
