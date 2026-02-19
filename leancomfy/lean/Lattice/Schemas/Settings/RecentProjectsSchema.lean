/-
  Lattice.Schemas.Settings.RecentProjectsSchema - Recent projects validation

  Validates recent projects list stored in localStorage.

  Source: ui/src/schemas/settings/recent-projects-schema.ts
-/

import Lattice.Schemas.SharedValidation

namespace Lattice.Schemas.Settings.RecentProjectsSchema

open Lattice.Schemas.SharedValidation

/-! ## Constants -/

def MAX_RECENT_PROJECTS : Nat := 100
def MAX_THUMBNAIL_SIZE : Nat := 10 * 1024 * 1024  -- 10MB
def MAX_TIMESTAMP : Nat := 2147483647000  -- Year 2038

/-! ## Recent Project -/

/-- A recent project entry -/
structure RecentProject where
  id : String
  name : String
  thumbnail : Option String
  modifiedAt : Nat
  deriving Repr, BEq

/-- Validate RecentProject -/
def validateRecentProject (rp : RecentProject) : Except ValidationError RecentProject := do
  let _ ← validateEntityId "id" rp.id
  let _ ← validateNonEmptyString "name" MAX_NAME_LENGTH rp.name
  match rp.thumbnail with
  | some thumb =>
    if thumb.length > MAX_THUMBNAIL_SIZE then
      throw (mkError "thumbnail" s!"must be at most {MAX_THUMBNAIL_SIZE} characters")
    else pure ()
  | none => pure ()
  let _ ← validateNonNegativeInt "modifiedAt" MAX_TIMESTAMP rp.modifiedAt
  pure rp

/-! ## Recent Projects Array -/

/-- Validate array of recent projects -/
def validateRecentProjects (projects : List RecentProject) : Except ValidationError (List RecentProject) := do
  if projects.length > MAX_RECENT_PROJECTS then
    throw (mkError "recentProjects" s!"must have at most {MAX_RECENT_PROJECTS} projects")
  for p in projects do
    let _ ← validateRecentProject p
  pure projects

/-! ## Safe Validation -/

def safeValidateRecentProject (rp : RecentProject) : Option RecentProject :=
  match validateRecentProject rp with
  | .ok p => some p
  | .error _ => none

def safeValidateRecentProjects (projects : List RecentProject) : Option (List RecentProject) :=
  match validateRecentProjects projects with
  | .ok ps => some ps
  | .error _ => none

end Lattice.Schemas.Settings.RecentProjectsSchema
