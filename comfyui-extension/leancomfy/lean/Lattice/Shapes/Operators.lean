/-
  Lattice.Shapes.Operators - Path operator types

  Part of Shapes module. Max 500 lines.

  Source: ui/src/types/shapes.ts (lines 222-409)
-/

import Lattice.Primitives
import Lattice.Shapes.Enums
import Lattice.Shapes.Primitives

namespace Lattice.Shapes.Operators

open Lattice.Primitives
open Lattice.Shapes.Enums
open Lattice.Shapes.Primitives

/-! ## Standard Path Operators -/

/-- Trim paths operator -/
structure TrimPathsOperator where
  name : NonEmptyString
  start : AnimatablePropertyRef   -- 0-100%
  end_ : AnimatablePropertyRef    -- 0-100%
  offset : AnimatablePropertyRef  -- Degrees (-360 to 360)
  mode : TrimMode
  deriving Repr

/-- Merge paths operator -/
structure MergePathsOperator where
  name : NonEmptyString
  mode : MergeMode
  deriving Repr

/-- Offset paths operator -/
structure OffsetPathsOperator where
  name : NonEmptyString
  amount : AnimatablePropertyRef     -- Positive = expand, negative = contract
  lineJoin : OffsetJoin
  miterLimit : AnimatablePropertyRef
  copies : AnimatablePropertyRef     -- Can create multiple offset copies
  copyOffset : AnimatablePropertyRef -- Distance between copies
  deriving Repr

/-- Pucker & Bloat operator -/
structure PuckerBloatOperator where
  name : NonEmptyString
  amount : AnimatablePropertyRef  -- -100 (pucker) to 100 (bloat)
  deriving Repr

/-- Wiggle paths operator -/
structure WigglePathsOperator where
  name : NonEmptyString
  size : AnimatablePropertyRef         -- Wiggle magnitude
  detail : AnimatablePropertyRef       -- Segments per curve (1-10)
  points : WigglePointType
  correlation : AnimatablePropertyRef  -- 0-100% how linked adjacent points are
  temporalPhase : AnimatablePropertyRef -- Animation offset
  spatialPhase : AnimatablePropertyRef  -- Spatial offset
  randomSeed : Nat
  deriving Repr

/-- ZigZag operator -/
structure ZigZagOperator where
  name : NonEmptyString
  size : AnimatablePropertyRef           -- Peak height
  ridgesPerSegment : AnimatablePropertyRef -- Zigzags per path segment
  points : ZigZagPointType
  deriving Repr

/-- Twist operator -/
structure TwistOperator where
  name : NonEmptyString
  angle : AnimatablePropertyRef   -- Total twist in degrees
  center : AnimatablePropertyRef  -- Center point
  deriving Repr

/-- Rounded corners operator -/
structure RoundedCornersOperator where
  name : NonEmptyString
  radius : AnimatablePropertyRef
  deriving Repr

/-! ## Illustrator-Specific Operators -/

/-- Simplify path operator -/
structure SimplifyPathOperator where
  name : NonEmptyString
  tolerance : AnimatablePropertyRef      -- Curve precision (0-100)
  angleTolerance : AnimatablePropertyRef -- Corner angle threshold
  straightLines : Bool                   -- Convert to straight segments
  deriving Repr

/-- Smooth path operator -/
structure SmoothPathOperator where
  name : NonEmptyString
  amount : AnimatablePropertyRef  -- 0-100%
  deriving Repr

/-- Extrude operator (3D) -/
structure ExtrudeOperator where
  name : NonEmptyString
  depth : AnimatablePropertyRef       -- Extrusion depth
  bevelDepth : AnimatablePropertyRef  -- Bevel size
  bevelSegments : Nat                 -- Smoothness of bevel
  capType : ExtrudeCapType
  -- Material colors
  frontColor : AnimatablePropertyRef
  sideColor : AnimatablePropertyRef
  bevelColor : AnimatablePropertyRef
  deriving Repr

/-- Image trace operator -/
structure TraceOperator where
  name : NonEmptyString
  mode : TraceMode
  threshold : AnimatablePropertyRef    -- B&W threshold (0-255)
  colors : Nat                         -- Max colors for color mode
  cornerAngle : Float                  -- Corner detection threshold
  pathFitting : AnimatablePropertyRef  -- Tolerance for path simplification
  noiseReduction : AnimatablePropertyRef -- Ignore small features
  sourceLayerId : Option NonEmptyString  -- Layer to trace
  sourceFrame : Option FrameNumber       -- Frame to trace (for video)
  cornerAngle_finite : cornerAngle.isFinite
  deriving Repr

/-! ## Path Operator Sum Type -/

/-- Path operator sum type -/
inductive PathOperator where
  | trimPaths : TrimPathsOperator → PathOperator
  | mergePaths : MergePathsOperator → PathOperator
  | offsetPaths : OffsetPathsOperator → PathOperator
  | puckerBloat : PuckerBloatOperator → PathOperator
  | wigglePaths : WigglePathsOperator → PathOperator
  | zigZag : ZigZagOperator → PathOperator
  | twist : TwistOperator → PathOperator
  | roundedCorners : RoundedCornersOperator → PathOperator
  deriving Repr

/-- Illustrator operator sum type -/
inductive IllustratorOperator where
  | simplifyPath : SimplifyPathOperator → IllustratorOperator
  | smoothPath : SmoothPathOperator → IllustratorOperator
  | extrude : ExtrudeOperator → IllustratorOperator
  | trace : TraceOperator → IllustratorOperator
  deriving Repr

/-! ## Operator Accessors -/

/-- Get name from any path operator -/
def PathOperator.name : PathOperator → NonEmptyString
  | trimPaths t => t.name
  | mergePaths m => m.name
  | offsetPaths o => o.name
  | puckerBloat p => p.name
  | wigglePaths w => w.name
  | zigZag z => z.name
  | twist t => t.name
  | roundedCorners r => r.name

/-- Get content type from path operator -/
def PathOperator.contentType : PathOperator → ShapeContentType
  | trimPaths _ => ShapeContentType.trimPaths
  | mergePaths _ => ShapeContentType.mergePaths
  | offsetPaths _ => ShapeContentType.offsetPaths
  | puckerBloat _ => ShapeContentType.puckerBloat
  | wigglePaths _ => ShapeContentType.wigglePaths
  | zigZag _ => ShapeContentType.zigZag
  | twist _ => ShapeContentType.twist
  | roundedCorners _ => ShapeContentType.roundedCorners

/-- Get name from any illustrator operator -/
def IllustratorOperator.name : IllustratorOperator → NonEmptyString
  | simplifyPath s => s.name
  | smoothPath s => s.name
  | extrude e => e.name
  | trace t => t.name

end Lattice.Shapes.Operators
