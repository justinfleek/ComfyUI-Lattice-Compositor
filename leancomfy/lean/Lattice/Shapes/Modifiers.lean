/-
  Lattice.Shapes.Modifiers - Fill and Stroke shape types

  Part of Shapes module. Max 500 lines.

  Source: ui/src/types/shapes.ts (lines 155-214)
-/

import Lattice.Primitives
import Lattice.Enums
import Lattice.Shapes.Enums
import Lattice.Shapes.Primitives

namespace Lattice.Shapes.Modifiers

open Lattice.Primitives
open Lattice.Enums
open Lattice.Shapes.Enums
open Lattice.Shapes.Primitives

/-! ## Fill Shape -/

/-- Fill shape modifier -/
structure FillShape where
  name : NonEmptyString
  color : AnimatablePropertyRef
  opacity : AnimatablePropertyRef  -- 0-100
  fillRule : FillRule
  blendMode : BlendMode
  deriving Repr

/-! ## Stroke Shape -/

/-- Stroke shape modifier -/
structure StrokeShape where
  name : NonEmptyString
  color : AnimatablePropertyRef
  opacity : AnimatablePropertyRef  -- 0-100
  width : AnimatablePropertyRef
  lineCap : LineCap
  lineJoin : LineJoin
  miterLimit : Float
  -- Dashes
  dashPattern : AnimatablePropertyRef  -- Array of dash/gap values
  dashOffset : AnimatablePropertyRef
  blendMode : BlendMode
  -- Taper settings
  taperEnabled : Bool
  taperStartLength : AnimatablePropertyRef  -- 0-100%
  taperEndLength : AnimatablePropertyRef
  taperStartWidth : AnimatablePropertyRef   -- 0-100%
  taperEndWidth : AnimatablePropertyRef
  taperStartEase : AnimatablePropertyRef    -- 0-100%
  taperEndEase : AnimatablePropertyRef
  -- Proof that miterLimit is valid
  miterLimit_finite : miterLimit.isFinite
  miterLimit_positive : miterLimit > 0
  deriving Repr

/-! ## Gradient Fill Shape -/

/-- Gradient fill shape modifier -/
structure GradientFillShape where
  name : NonEmptyString
  gradient : AnimatablePropertyRef
  opacity : AnimatablePropertyRef
  fillRule : FillRule
  blendMode : BlendMode
  deriving Repr

/-! ## Gradient Stroke Shape -/

/-- Gradient stroke shape modifier -/
structure GradientStrokeShape where
  name : NonEmptyString
  gradient : AnimatablePropertyRef
  opacity : AnimatablePropertyRef
  width : AnimatablePropertyRef
  lineCap : LineCap
  lineJoin : LineJoin
  miterLimit : Float
  dashPattern : AnimatablePropertyRef
  dashOffset : AnimatablePropertyRef
  blendMode : BlendMode
  miterLimit_finite : miterLimit.isFinite
  miterLimit_positive : miterLimit > 0
  deriving Repr

/-! ## Shape Modifier Sum Type -/

/-- Shape modifier sum type -/
inductive ShapeModifier where
  | fill : FillShape → ShapeModifier
  | stroke : StrokeShape → ShapeModifier
  | gradientFill : GradientFillShape → ShapeModifier
  | gradientStroke : GradientStrokeShape → ShapeModifier
  deriving Repr

/-! ## Modifier Accessors -/

/-- Get name from any modifier -/
def ShapeModifier.name : ShapeModifier → NonEmptyString
  | fill f => f.name
  | stroke s => s.name
  | gradientFill g => g.name
  | gradientStroke g => g.name

/-- Get content type from modifier -/
def ShapeModifier.contentType : ShapeModifier → ShapeContentType
  | fill _ => ShapeContentType.fill
  | stroke _ => ShapeContentType.stroke
  | gradientFill _ => ShapeContentType.gradientFill
  | gradientStroke _ => ShapeContentType.gradientStroke

/-- Get blend mode from any modifier -/
def ShapeModifier.blendMode : ShapeModifier → BlendMode
  | fill f => f.blendMode
  | stroke s => s.blendMode
  | gradientFill g => g.blendMode
  | gradientStroke g => g.blendMode

end Lattice.Shapes.Modifiers
