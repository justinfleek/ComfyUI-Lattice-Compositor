/-
  Lattice.Shapes.Groups - Shape groups and layer data

  Part of Shapes module. Max 500 lines.

  Source: ui/src/types/shapes.ts (lines 314-440)
-/

import Lattice.Primitives
import Lattice.Enums
import Lattice.Shapes.Enums
import Lattice.Shapes.Primitives
import Lattice.Shapes.Generators
import Lattice.Shapes.Modifiers
import Lattice.Shapes.Operators

namespace Lattice.Shapes.Groups

open Lattice.Primitives
open Lattice.Enums
open Lattice.Shapes.Enums
open Lattice.Shapes.Primitives
open Lattice.Shapes.Generators
open Lattice.Shapes.Modifiers
open Lattice.Shapes.Operators

/-! ## Shape Transform -/

/-- Shape transform with animatable properties -/
structure ShapeTransform where
  name : NonEmptyString
  anchorPoint : AnimatablePropertyRef
  position : AnimatablePropertyRef
  scale : AnimatablePropertyRef      -- Percentage (100 = 100%)
  rotation : AnimatablePropertyRef   -- Degrees
  skew : AnimatablePropertyRef       -- Degrees
  skewAxis : AnimatablePropertyRef   -- Degrees
  opacity : AnimatablePropertyRef    -- 0-100%
  deriving Repr

/-! ## Repeater -/

/-- Repeater transform settings -/
structure RepeaterTransform where
  anchorPoint : AnimatablePropertyRef
  position : AnimatablePropertyRef
  scale : AnimatablePropertyRef       -- End scale (100 = no change)
  rotation : AnimatablePropertyRef    -- Rotation per copy
  startOpacity : AnimatablePropertyRef -- Opacity of first copy
  endOpacity : AnimatablePropertyRef   -- Opacity of last copy
  deriving Repr

/-- Repeater operator -/
structure RepeaterOperator where
  name : NonEmptyString
  copies : AnimatablePropertyRef
  offset : AnimatablePropertyRef  -- Offset from original (degrees for radial)
  composite : RepeaterComposite   -- Stack order
  transform : RepeaterTransform
  deriving Repr

/-! ## Non-Group Shape Content -/

/-- Non-group shape content (used inside ShapeGroup.contents to avoid circular dependency) -/
inductive NonGroupShapeContent where
  | generator : ShapeGenerator → NonGroupShapeContent
  | modifier : ShapeModifier → NonGroupShapeContent
  | pathOperator : PathOperator → NonGroupShapeContent
  | illustratorOperator : IllustratorOperator → NonGroupShapeContent
  | transform : ShapeTransform → NonGroupShapeContent
  | repeater : RepeaterOperator → NonGroupShapeContent
  deriving Repr

/-! ## Shape Group -/

/-- Shape group (contains non-group content only to prevent recursion) -/
structure ShapeGroup where
  name : NonEmptyString
  contents : Array NonGroupShapeContent
  transform : ShapeTransform
  blendMode : BlendMode
  deriving Repr

/-! ## Full Shape Content -/

/-- Full shape content (includes groups for root-level ShapeLayerData.contents) -/
inductive ShapeContent where
  | nonGroup : NonGroupShapeContent → ShapeContent
  | group : ShapeGroup → ShapeContent
  deriving Repr

/-! ## Shape Layer Data -/

/-- Shape layer data -/
structure ShapeLayerData where
  contents : Array ShapeContent
  blendMode : BlendMode
  quality : ShapeQuality
  gpuAccelerated : Bool
  deriving Repr

/-! ## Content Accessors -/

/-- Get name from non-group content -/
def NonGroupShapeContent.name : NonGroupShapeContent → NonEmptyString
  | generator g => g.name
  | modifier m => m.name
  | pathOperator p => p.name
  | illustratorOperator i => i.name
  | transform t => t.name
  | repeater r => r.name

/-- Get content type from non-group content -/
def NonGroupShapeContent.contentType : NonGroupShapeContent → ShapeContentType
  | generator g => g.contentType
  | modifier m => m.contentType
  | pathOperator p => p.contentType
  | illustratorOperator _ => ShapeContentType.transform  -- Placeholder
  | transform _ => ShapeContentType.transform
  | repeater _ => ShapeContentType.repeater

/-- Get name from shape content -/
def ShapeContent.name : ShapeContent → NonEmptyString
  | nonGroup n => n.name
  | group g => g.name

/-! ## Default Factories -/

/-- Default shape transform name -/
def defaultTransformName : NonEmptyString :=
  ⟨"Transform", by decide⟩

/-- Default group name -/
def defaultGroupName : NonEmptyString :=
  ⟨"Group", by decide⟩

end Lattice.Shapes.Groups
