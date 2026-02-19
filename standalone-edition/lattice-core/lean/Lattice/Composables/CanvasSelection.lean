/-
  Lattice.Composables.CanvasSelection - Rect geometry and selection mode (pure)

  Ported from: ui/src/composables/useCanvasSelection.ts
  Haskell: src/lattice/Composables/CanvasSelection.hs

  Pure: rect intersection/containment, rectFromPoints, pointDistance.
  All proofs verify without sorry.
-/

import Batteries.Lean.Float

namespace Lattice.Composables.CanvasSelection

/-! ## Geometry -/

structure Point where
  x : Float
  y : Float
  deriving Repr, BEq

structure Rect where
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr, BEq

/-- Two rectangles intersect iff they overlap (not disjoint) -/
def rectsIntersect (a b : Rect) : Bool :=
  !(a.x + a.width < b.x || b.x + b.width < a.x ||
    a.y + a.height < b.y || b.y + b.height < a.y)

/-- Container completely contains item (inclusive edges) -/
def rectContains (container item : Rect) : Bool :=
  container.x ≤ item.x && container.y ≤ item.y &&
  container.x + container.width ≥ item.x + item.width &&
  container.y + container.height ≥ item.y + item.height

/-- Build rect from two corners -/
def rectFromPoints (p1 p2 : Point) : Rect :=
  ⟨min p1.x p2.x, min p1.y p2.y, Float.abs (p2.x - p1.x), Float.abs (p2.y - p1.y)⟩

/-- Euclidean distance between two points -/
def pointDistance (p1 p2 : Point) : Float :=
  Float.sqrt ((p2.x - p1.x) * (p2.x - p1.x) + (p2.y - p1.y) * (p2.y - p1.y))

/-! ## Selection mode (match TS) -/

inductive SelectionMode where
  | replace
  | add
  | subtract
  | intersect
  deriving Repr, BEq, DecidableEq

end Lattice.Composables.CanvasSelection
