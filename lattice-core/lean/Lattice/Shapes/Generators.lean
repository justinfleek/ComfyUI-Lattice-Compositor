/-
  Lattice.Shapes.Generators - Shape generator types

  Part of Shapes module. Max 500 lines.

  Source: ui/src/types/shapes.ts (lines 92-145)
-/

import Lattice.Primitives
import Lattice.Shapes.Enums
import Lattice.Shapes.Primitives

namespace Lattice.Shapes.Generators

open Lattice.Primitives
open Lattice.Shapes.Enums
open Lattice.Shapes.Primitives

/-! ## Shape Generators -/

/-- Rectangle shape -/
structure RectangleShape where
  name : NonEmptyString
  position : AnimatablePropertyRef
  size : AnimatablePropertyRef
  roundness : AnimatablePropertyRef  -- Corner radius in pixels
  direction : PathDirection
  deriving Repr

/-- Ellipse shape -/
structure EllipseShape where
  name : NonEmptyString
  position : AnimatablePropertyRef
  size : AnimatablePropertyRef
  direction : PathDirection
  deriving Repr

/-- Polygon shape -/
structure PolygonShape where
  name : NonEmptyString
  position : AnimatablePropertyRef
  points : AnimatablePropertyRef     -- Number of sides (3+)
  outerRadius : AnimatablePropertyRef
  outerRoundness : AnimatablePropertyRef  -- 0-100%
  rotation : AnimatablePropertyRef   -- Degrees
  direction : PathDirection
  deriving Repr

/-- Star shape -/
structure StarShape where
  name : NonEmptyString
  position : AnimatablePropertyRef
  points : AnimatablePropertyRef     -- Number of points (3+)
  outerRadius : AnimatablePropertyRef
  innerRadius : AnimatablePropertyRef
  outerRoundness : AnimatablePropertyRef  -- 0-100%
  innerRoundness : AnimatablePropertyRef  -- 0-100%
  rotation : AnimatablePropertyRef
  direction : PathDirection
  deriving Repr

/-- Path shape -/
structure PathShape where
  name : NonEmptyString
  path : AnimatablePropertyRef
  direction : PathDirection
  deriving Repr

/-- Shape generator sum type -/
inductive ShapeGenerator where
  | rectangle : RectangleShape → ShapeGenerator
  | ellipse : EllipseShape → ShapeGenerator
  | polygon : PolygonShape → ShapeGenerator
  | star : StarShape → ShapeGenerator
  | path : PathShape → ShapeGenerator
  deriving Repr

/-! ## Generator Accessors -/

/-- Get name from any generator -/
def ShapeGenerator.name : ShapeGenerator → NonEmptyString
  | rectangle r => r.name
  | ellipse e => e.name
  | polygon p => p.name
  | star s => s.name
  | path p => p.name

/-- Get content type from generator -/
def ShapeGenerator.contentType : ShapeGenerator → ShapeContentType
  | rectangle _ => ShapeContentType.rectangle
  | ellipse _ => ShapeContentType.ellipse
  | polygon _ => ShapeContentType.polygon
  | star _ => ShapeContentType.star
  | path _ => ShapeContentType.path

/-- Get direction from any generator -/
def ShapeGenerator.direction : ShapeGenerator → PathDirection
  | rectangle r => r.direction
  | ellipse e => e.direction
  | polygon p => p.direction
  | star s => s.direction
  | path p => p.direction

end Lattice.Shapes.Generators
