/-
  Lattice.Shapes - Shape layer types

  Main module that re-exports all shape sub-modules.

  Refactored from: ui/src/types/shapes.ts (849 lines)
  Split into 5 modules under 500 lines each:
    - Shapes/Enums.lean (146 lines)
    - Shapes/Primitives.lean (149 lines)
    - Shapes/Generators.lean (103 lines)
    - Shapes/Modifiers.lean (124 lines)
    - Shapes/Operators.lean (177 lines)
    - Shapes/Groups.lean (148 lines)
  Total: ~850 lines across 6 files (avg 142 lines each)
-/

import Lattice.Shapes.Enums
import Lattice.Shapes.Primitives
import Lattice.Shapes.Generators
import Lattice.Shapes.Modifiers
import Lattice.Shapes.Operators
import Lattice.Shapes.Groups

namespace Lattice.Shapes

-- Re-export everything
export Lattice.Shapes.Enums (
  FillRule LineCap LineJoin TrimMode MergeMode OffsetJoin
  WigglePointType ZigZagPointType RepeaterComposite
  ShapeContentType GradientType ShapeQuality
  ExtrudeCapType TraceMode PathDirection
)

export Lattice.Shapes.Primitives (
  BezierVertex BezierPath ValidBezierPath
  ShapeColor GradientStop GradientDef
  AnimatablePropertyRef ShapeTransformData
)

export Lattice.Shapes.Generators (
  RectangleShape EllipseShape PolygonShape StarShape PathShape
  ShapeGenerator
)

export Lattice.Shapes.Modifiers (
  FillShape StrokeShape GradientFillShape GradientStrokeShape
  ShapeModifier
)

export Lattice.Shapes.Operators (
  TrimPathsOperator MergePathsOperator OffsetPathsOperator
  PuckerBloatOperator WigglePathsOperator ZigZagOperator
  TwistOperator RoundedCornersOperator
  SimplifyPathOperator SmoothPathOperator ExtrudeOperator TraceOperator
  PathOperator IllustratorOperator
)

export Lattice.Shapes.Groups (
  ShapeTransform RepeaterTransform RepeaterOperator
  NonGroupShapeContent ShapeGroup ShapeContent ShapeLayerData
)

end Lattice.Shapes
