/-
  Lattice.Schemas.Shapes.ShapesSchema

  Shape layer enums for generators, modifiers, and path operators.

  Source: ui/src/schemas/layers/shapes-schema.ts
-/

namespace Lattice.Schemas.Shapes.ShapesSchema

--------------------------------------------------------------------------------
-- Fill Rule
--------------------------------------------------------------------------------

/-- Fill rule options -/
inductive FillRule where
  | nonzero
  | evenodd
  deriving Repr, DecidableEq, Inhabited

def fillRuleFromString : String → Option FillRule
  | "nonzero" => some .nonzero
  | "evenodd" => some .evenodd
  | _ => Option.none

def fillRuleToString : FillRule → String
  | .nonzero => "nonzero"
  | .evenodd => "evenodd"

--------------------------------------------------------------------------------
-- Line Cap
--------------------------------------------------------------------------------

/-- Line cap options -/
inductive LineCap where
  | butt
  | round
  | square
  deriving Repr, DecidableEq, Inhabited

def lineCapFromString : String → Option LineCap
  | "butt" => some .butt
  | "round" => some .round
  | "square" => some .square
  | _ => Option.none

def lineCapToString : LineCap → String
  | .butt => "butt"
  | .round => "round"
  | .square => "square"

--------------------------------------------------------------------------------
-- Line Join
--------------------------------------------------------------------------------

/-- Line join options -/
inductive LineJoin where
  | miter
  | round
  | bevel
  deriving Repr, DecidableEq, Inhabited

def lineJoinFromString : String → Option LineJoin
  | "miter" => some .miter
  | "round" => some .round
  | "bevel" => some .bevel
  | _ => Option.none

def lineJoinToString : LineJoin → String
  | .miter => "miter"
  | .round => "round"
  | .bevel => "bevel"

--------------------------------------------------------------------------------
-- Trim Mode
--------------------------------------------------------------------------------

/-- Trim mode options -/
inductive TrimMode where
  | simultaneously
  | individually
  deriving Repr, DecidableEq, Inhabited

def trimModeFromString : String → Option TrimMode
  | "simultaneously" => some .simultaneously
  | "individually" => some .individually
  | _ => Option.none

def trimModeToString : TrimMode → String
  | .simultaneously => "simultaneously"
  | .individually => "individually"

--------------------------------------------------------------------------------
-- Merge Mode
--------------------------------------------------------------------------------

/-- Merge mode options (path boolean operations) -/
inductive MergeMode where
  | add
  | subtract
  | intersect
  | exclude
  | minusFront
  | minusBack
  deriving Repr, DecidableEq, Inhabited

def mergeModeFromString : String → Option MergeMode
  | "add" => some .add
  | "subtract" => some .subtract
  | "intersect" => some .intersect
  | "exclude" => some .exclude
  | "minusFront" => some .minusFront
  | "minusBack" => some .minusBack
  | _ => Option.none

def mergeModeToString : MergeMode → String
  | .add => "add"
  | .subtract => "subtract"
  | .intersect => "intersect"
  | .exclude => "exclude"
  | .minusFront => "minusFront"
  | .minusBack => "minusBack"

--------------------------------------------------------------------------------
-- Wiggle Point Type
--------------------------------------------------------------------------------

/-- Wiggle point type options -/
inductive WigglePointType where
  | corner
  | smooth
  deriving Repr, DecidableEq, Inhabited

def wigglePointTypeFromString : String → Option WigglePointType
  | "corner" => some .corner
  | "smooth" => some .smooth
  | _ => Option.none

def wigglePointTypeToString : WigglePointType → String
  | .corner => "corner"
  | .smooth => "smooth"

--------------------------------------------------------------------------------
-- Repeater Composite
--------------------------------------------------------------------------------

/-- Repeater composite options -/
inductive RepeaterComposite where
  | above
  | below
  deriving Repr, DecidableEq, Inhabited

def repeaterCompositeFromString : String → Option RepeaterComposite
  | "above" => some .above
  | "below" => some .below
  | _ => Option.none

def repeaterCompositeToString : RepeaterComposite → String
  | .above => "above"
  | .below => "below"

--------------------------------------------------------------------------------
-- Cap Type (for extrude)
--------------------------------------------------------------------------------

/-- Cap type options for extrusion -/
inductive CapType where
  | flat
  | round
  | bevel
  deriving Repr, DecidableEq, Inhabited

def capTypeFromString : String → Option CapType
  | "flat" => some .flat
  | "round" => some .round
  | "bevel" => some .bevel
  | _ => Option.none

def capTypeToString : CapType → String
  | .flat => "flat"
  | .round => "round"
  | .bevel => "bevel"

--------------------------------------------------------------------------------
-- Trace Mode
--------------------------------------------------------------------------------

/-- Trace mode options -/
inductive TraceMode where
  | blackAndWhite
  | grayscale
  | color
  deriving Repr, DecidableEq, Inhabited

def traceModeFromString : String → Option TraceMode
  | "blackAndWhite" => some .blackAndWhite
  | "grayscale" => some .grayscale
  | "color" => some .color
  | _ => Option.none

def traceModeToString : TraceMode → String
  | .blackAndWhite => "blackAndWhite"
  | .grayscale => "grayscale"
  | .color => "color"

--------------------------------------------------------------------------------
-- Shape Quality
--------------------------------------------------------------------------------

/-- Shape quality options -/
inductive ShapeQuality where
  | draft
  | normal
  | high
  deriving Repr, DecidableEq, Inhabited

def shapeQualityFromString : String → Option ShapeQuality
  | "draft" => some .draft
  | "normal" => some .normal
  | "high" => some .high
  | _ => Option.none

def shapeQualityToString : ShapeQuality → String
  | .draft => "draft"
  | .normal => "normal"
  | .high => "high"

--------------------------------------------------------------------------------
-- Shape Direction
--------------------------------------------------------------------------------

/-- Shape direction (clockwise or counter-clockwise) -/
inductive ShapeDirection where
  | clockwise      -- 1
  | counterclockwise  -- -1
  deriving Repr, DecidableEq, Inhabited

def shapeDirectionFromInt : Int → Option ShapeDirection
  | 1 => some .clockwise
  | -1 => some .counterclockwise
  | _ => Option.none

def shapeDirectionToInt : ShapeDirection → Int
  | .clockwise => 1
  | .counterclockwise => -1

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_VERTICES_PER_PATH : Nat := 100000
def MIN_CLOSED_PATH_VERTICES : Nat := 3
def MAX_GRADIENT_STOPS : Nat := 100
def MIN_GRADIENT_STOPS : Nat := 2
def MAX_DASH_SEGMENTS : Nat := 1000
def MAX_CONTENTS_PER_GROUP : Nat := 1000
def MAX_BEVEL_SEGMENTS : Nat := 100
def MAX_TRACE_COLORS : Nat := 256
def MAX_MITER_LIMIT : Float := 100.0

end Lattice.Schemas.Shapes.ShapesSchema
