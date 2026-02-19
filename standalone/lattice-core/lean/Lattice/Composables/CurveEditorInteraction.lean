/-
  Lattice.Composables.CurveEditorInteraction - Selection box and hit-test (pure)

  Ported from: ui/src/composables/useCurveEditorInteraction.ts
  Haskell: src/lattice/Composables/CurveEditorInteraction.hs

  Pure: selection box containment, hit radius constant.
  All proofs verify without sorry.
-/

import Batteries.Lean.Float

namespace Lattice.Composables.CurveEditorInteraction

/-! ## Selection box -/

/-- Selection box (x, y, width, height) -/
structure SelectionBox where
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr, BEq

/-- Build box from two corners (x1,y1) and (x2,y2) -/
def selectionBoxFromPoints (x1 y1 x2 y2 : Float) : SelectionBox :=
  ⟨min x1 x2, min y1 y2, Float.abs (x2 - x1), Float.abs (y2 - y1)⟩

/-- True if point (px, py) is inside the box (inclusive edges) -/
def pointInSelectionBox (px py : Float) (box : SelectionBox) : Bool :=
  px >= box.x && px <= box.x + box.width &&
  py >= box.y && py <= box.y + box.height

/-! ## Hit radius (match TS constant 10) -/

def defaultHitRadius : Float := 10.0

end Lattice.Composables.CurveEditorInteraction
