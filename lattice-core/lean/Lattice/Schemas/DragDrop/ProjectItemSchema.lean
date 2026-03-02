/-
  Lattice.Schemas.DragDrop.ProjectItemSchema

  Project item validation for drag-drop operations.

  Source: ui/src/schemas/dragdrop/project-item-schema.ts
-/

import Lattice.Schemas.SharedValidation

namespace Lattice.Schemas.DragDrop.ProjectItemSchema

open SharedValidation

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_DIMENSION : Nat := 16384

--------------------------------------------------------------------------------
-- Project Item Type
--------------------------------------------------------------------------------

/-- Project item type options -/
inductive ProjectItemType where
  | composition
  | footage
  | solid
  | audio
  | folder
  deriving Repr, DecidableEq, Inhabited

def projectItemTypeFromString : String → Option ProjectItemType
  | "composition" => some .composition
  | "footage" => some .footage
  | "solid" => some .solid
  | "audio" => some .audio
  | "folder" => some .folder
  | _ => none

def projectItemTypeToString : ProjectItemType → String
  | .composition => "composition"
  | .footage => "footage"
  | .solid => "solid"
  | .audio => "audio"
  | .folder => "folder"

--------------------------------------------------------------------------------
-- Project Item
--------------------------------------------------------------------------------

/-- Project item structure -/
structure ProjectItem where
  id : String
  name : String
  itemType : ProjectItemType
  width : Option Nat
  height : Option Nat
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Validate ProjectItem -/
def validateProjectItem (item : ProjectItem) : Except ValidationError ProjectItem := do
  _ ← validateEntityId "id" item.id
  _ ← validateNonEmptyString "name" MAX_NAME_LENGTH item.name

  -- Validate width
  match item.width with
  | some w => if w > MAX_DIMENSION then
      throw (mkError "width" s!"must be at most {MAX_DIMENSION}")
    else pure ()
  | none => pure ()

  -- Validate height
  match item.height with
  | some h => if h > MAX_DIMENSION then
      throw (mkError "height" s!"must be at most {MAX_DIMENSION}")
    else pure ()
  | none => pure ()

  pure item

/-- Safe validation -/
def safeValidateProjectItem (item : ProjectItem) : Option ProjectItem :=
  match validateProjectItem item with
  | .ok i => some i
  | .error _ => none

end Lattice.Schemas.DragDrop.ProjectItemSchema
