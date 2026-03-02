/-
  Lattice.Shapes.Enums - Shape-specific enumerations

  Part of Shapes module. Max 500 lines.

  Source: ui/src/types/shapes.ts (lines 151-277)
-/

namespace Lattice.Shapes.Enums

/-! ## Fill/Stroke Enums -/

/-- Fill rule for path operations -/
inductive FillRule where
  | nonzero
  | evenodd
  deriving Repr, BEq, DecidableEq

/-- Line cap style -/
inductive LineCap where
  | butt
  | round
  | square
  deriving Repr, BEq, DecidableEq

/-- Line join style -/
inductive LineJoin where
  | miter
  | round
  | bevel
  deriving Repr, BEq, DecidableEq

/-! ## Path Operator Enums -/

/-- Trim paths mode -/
inductive TrimMode where
  | simultaneously
  | individually
  deriving Repr, BEq, DecidableEq

/-- Merge paths mode -/
inductive MergeMode where
  | add        -- Union
  | subtract   -- Minus Front
  | intersect  -- Intersection
  | exclude    -- Exclude Intersection
  | minusFront -- Same as subtract
  | minusBack  -- Minus Back (Illustrator)
  deriving Repr, BEq, DecidableEq

/-- Offset paths join style -/
inductive OffsetJoin where
  | miter
  | round
  | bevel
  deriving Repr, BEq, DecidableEq

/-- Wiggle paths point type -/
inductive WigglePointType where
  | corner
  | smooth
  deriving Repr, BEq, DecidableEq

/-- ZigZag point type -/
inductive ZigZagPointType where
  | corner
  | smooth
  deriving Repr, BEq, DecidableEq

/-! ## Repeater/Group Enums -/

/-- Repeater composite order -/
inductive RepeaterComposite where
  | above
  | below
  deriving Repr, BEq, DecidableEq

/-! ## Shape Content Type -/

/-- All shape content types -/
inductive ShapeContentType where
  -- Generators
  | rectangle
  | ellipse
  | polygon
  | star
  | path
  -- Modifiers
  | fill
  | stroke
  | gradientFill
  | gradientStroke
  -- Operators
  | trimPaths
  | mergePaths
  | offsetPaths
  | puckerBloat
  | wigglePaths
  | zigZag
  | twist
  | roundedCorners
  | repeater
  | transform
  -- Group
  | group
  -- Illustrator
  | simplifyPath
  | smoothPath
  | extrude
  | trace
  deriving Repr, BEq, DecidableEq

/-! ## Gradient Type -/

/-- Gradient type -/
inductive GradientType where
  | linear
  | radial
  deriving Repr, BEq, DecidableEq

/-! ## Quality Mode -/

/-- Shape layer quality -/
inductive ShapeQuality where
  | draft
  | normal
  | high
  deriving Repr, BEq, DecidableEq

/-! ## Extrude Cap Type -/

/-- Extrude cap style -/
inductive ExtrudeCapType where
  | flat
  | round
  | bevel
  deriving Repr, BEq, DecidableEq

/-! ## Trace Mode -/

/-- Image trace mode -/
inductive TraceMode where
  | blackAndWhite
  | grayscale
  | color
  deriving Repr, BEq, DecidableEq

/-! ## Path Direction -/

/-- Path winding direction -/
inductive PathDirection where
  | clockwise      -- 1
  | counterClockwise  -- -1
  deriving Repr, BEq, DecidableEq

/-- Convert direction to integer -/
def PathDirection.toInt : PathDirection → Int
  | clockwise => 1
  | counterClockwise => -1

end Lattice.Shapes.Enums
