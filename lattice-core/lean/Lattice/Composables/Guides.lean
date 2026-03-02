/-
  Lattice.Composables.Guides - Ruler guide types and pure list operations

  Ported from: ui/src/composables/useGuides.ts
  Haskell: src/lattice/Composables/Guides.hs

  Types and list operations only; no DOM/events.
  All proofs verify without sorry.
-/

import Mathlib.Data.List.Basic
import Batteries.Lean.Float

namespace Lattice.Composables.Guides

/-! ## Orientation -/

/-- Guide orientation -/
inductive GuideOrientation where
  | horizontal
  | vertical
  deriving Repr, BEq, DecidableEq

/-! ## Guide -/

/-- Single ruler guide (id, orientation, position in px) -/
structure Guide where
  id : String
  orientation : GuideOrientation
  position : Float
  deriving Repr, BEq

/-! ## List operations (match Haskell API) -/

/-- Add a guide with the given id (caller provides id) -/
def addGuide (gid : String) (orient : GuideOrientation) (pos : Float) (gs : List Guide) : List Guide :=
  ⟨gid, orient, pos⟩ :: gs

/-- Remove guide by id -/
def removeGuide (gid : String) (gs : List Guide) : List Guide :=
  gs.filter (λ g => g.id != gid)

/-- Remove all guides -/
def clearGuides (_ : List Guide) : List Guide :=
  []

/-- Update position of guide by id; returns unchanged list if id not found -/
def updateGuidePosition (gid : String) (pos : Float) (gs : List Guide) : List Guide :=
  gs.map (λ g => if g.id == gid then { g with position := pos } else g)

/-! ## Theorems -/

/-- removeGuide does not increase length -/
theorem removeGuide_length_le (gid : String) (gs : List Guide) :
    (removeGuide gid gs).length ≤ gs.length := by
  simp [removeGuide]
  exact List.length_filter_le _ _

/-- clearGuides yields empty list -/
theorem clearGuides_length (gs : List Guide) :
    (clearGuides gs).length = 0 := by
  simp [clearGuides]

/-- addGuide increases length by one -/
theorem addGuide_length (gid : String) (orient : GuideOrientation) (pos : Float) (gs : List Guide) :
    (addGuide gid orient pos gs).length = gs.length + 1 := by
  simp [addGuide]

/-- updateGuidePosition preserves length -/
theorem updateGuidePosition_length (gid : String) (pos : Float) (gs : List Guide) :
    (updateGuidePosition gid pos gs).length = gs.length := by
  simp [updateGuidePosition]

end Lattice.Composables.Guides
