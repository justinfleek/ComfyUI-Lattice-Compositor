/-
  Lattice.Spline - Spline and path types

  Refactored from: ui/src/types/spline.ts (382 lines)
  Single file under 500 lines.

  Bezier paths, control points, path effects, level of detail.
-/

import Lattice.Primitives
import Lattice.Shapes.Enums

namespace Lattice.Spline

open Lattice.Primitives
open Lattice.Shapes.Enums

/-! ## Control Point Enums -/

/-- Control point type -/
inductive ControlPointType where
  | corner     -- Sharp corner
  | smooth     -- Smooth curve (handles aligned but different lengths)
  | symmetric  -- Symmetric curve (handles aligned and same length)
  deriving Repr, BEq, DecidableEq

/-- LOD mode -/
inductive LODMode where
  | zoom       -- Simplify based on zoom level
  | playback   -- Simplify during playback
  | both       -- Both modes
  deriving Repr, BEq, DecidableEq

/-- Wave type for wave effect -/
inductive WaveType where
  | sine
  | triangle
  | square
  deriving Repr, BEq, DecidableEq

/-- Path effect type -/
inductive SplinePathEffectType where
  | offsetPath
  | roughen
  | wiggle
  | zigzag
  | wave
  deriving Repr, BEq, DecidableEq

/-- Stroke type -/
inductive StrokeType where
  | solid
  | gradient
  deriving Repr, BEq, DecidableEq

/-- ZigZag point type -/
inductive SplineZigZagPointType where
  | corner
  | smooth
  deriving Repr, BEq, DecidableEq

/-! ## Handle Types -/

/-- 2D handle position -/
structure Handle where
  x : Float
  y : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-! ## Control Point -/

/-- Static control point -/
structure ControlPoint where
  id : NonEmptyString
  x : Float
  y : Float
  depth : Option Float
  handleIn : Option Handle
  handleOut : Option Handle
  pointType : ControlPointType
  group : Option NonEmptyString
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-- Animatable control point (uses property IDs) -/
structure AnimatableControlPoint where
  id : NonEmptyString
  x : NonEmptyString           -- AnimatableProperty ID
  y : NonEmptyString           -- AnimatableProperty ID
  depth : Option NonEmptyString -- AnimatableProperty ID
  handleIn : Option (NonEmptyString × NonEmptyString)  -- x, y property IDs
  handleOut : Option (NonEmptyString × NonEmptyString) -- x, y property IDs
  pointType : ControlPointType
  group : Option NonEmptyString
  deriving Repr

/-- Evaluated control point at a specific frame -/
structure EvaluatedControlPoint where
  id : NonEmptyString
  x : Float
  y : Float
  depth : Float
  handleIn : Option Handle
  handleOut : Option Handle
  pointType : ControlPointType
  group : Option NonEmptyString
  x_finite : x.isFinite
  y_finite : y.isFinite
  depth_finite : depth.isFinite
  deriving Repr

/-! ## Gradient Types -/

/-- RGBA color -/
structure SplineRGBA where
  r : Nat
  g : Nat
  b : Nat
  a : Float
  r_le_255 : r ≤ 255
  g_le_255 : g ≤ 255
  b_le_255 : b ≤ 255
  a_ge_0 : a ≥ 0
  a_le_1 : a ≤ 1
  a_finite : a.isFinite
  deriving Repr

/-- Gradient stop -/
structure SplineGradientStop where
  position : Float
  color : SplineRGBA
  pos_ge_0 : position ≥ 0
  pos_le_1 : position ≤ 1
  pos_finite : position.isFinite
  deriving Repr

/-- Stroke gradient definition -/
structure SplineStrokeGradient where
  gradientType : GradientType
  stops : Array SplineGradientStop
  followPath : Bool
  spread : Float  -- 0-100%
  offsetKeyframes : Option (Array (FrameNumber × Float))
  h_min_stops : stops.size ≥ 2
  spread_ge_0 : spread ≥ 0
  spread_le_100 : spread ≤ 100
  spread_finite : spread.isFinite
  deriving Repr

/-! ## Path Effects -/

/-- Base path effect -/
structure PathEffectBase where
  id : NonEmptyString
  enabled : Bool
  order : Nat
  deriving Repr

/-- Offset path effect -/
structure OffsetPathEffect extends PathEffectBase where
  amount : NonEmptyString      -- AnimatableProperty ID
  lineJoin : LineJoin
  miterLimit : NonEmptyString  -- AnimatableProperty ID
  deriving Repr

/-- Roughen effect -/
structure RoughenEffect extends PathEffectBase where
  size : NonEmptyString        -- AnimatableProperty ID
  detail : NonEmptyString      -- AnimatableProperty ID
  seed : Nat
  deriving Repr

/-- Wiggle path effect -/
structure WigglePathEffect extends PathEffectBase where
  size : NonEmptyString
  detail : NonEmptyString
  temporalPhase : NonEmptyString
  spatialPhase : NonEmptyString
  correlation : NonEmptyString
  seed : Nat
  deriving Repr

/-- ZigZag effect -/
structure ZigZagEffect extends PathEffectBase where
  size : NonEmptyString
  ridgesPerSegment : NonEmptyString
  pointType : SplineZigZagPointType
  deriving Repr

/-- Wave effect -/
structure WaveEffect extends PathEffectBase where
  amplitude : NonEmptyString
  frequency : NonEmptyString
  phase : NonEmptyString
  waveType : WaveType
  deriving Repr

/-- Path effect instance -/
inductive SplinePathEffectInstance where
  | offsetPath : OffsetPathEffect → SplinePathEffectInstance
  | roughen : RoughenEffect → SplinePathEffectInstance
  | wiggle : WigglePathEffect → SplinePathEffectInstance
  | zigzag : ZigZagEffect → SplinePathEffectInstance
  | wave : WaveEffect → SplinePathEffectInstance
  deriving Repr

/-! ## Level of Detail -/

/-- Single LOD level -/
structure LODLevel where
  tolerance : Float
  controlPoints : Array ControlPoint
  pointCount : Nat
  quality : Option Nat
  complexity : Option Float
  tolerance_positive : tolerance > 0
  tolerance_finite : tolerance.isFinite
  deriving Repr

/-- LOD settings -/
structure SplineLODSettings where
  enabled : Bool
  mode : LODMode
  levels : Array LODLevel
  maxPointsForPreview : Nat
  simplificationTolerance : Float
  cullingEnabled : Bool
  cullMargin : Float
  simplificationTolerance_positive : simplificationTolerance > 0
  simplificationTolerance_finite : simplificationTolerance.isFinite
  cullMargin_ge_0 : cullMargin ≥ 0
  cullMargin_finite : cullMargin.isFinite
  deriving Repr

/-! ## Spline Data -/

/-- Full spline data -/
structure SplineData where
  pathData : String
  controlPoints : Array ControlPoint
  closed : Bool
  -- Stroke
  strokeType : StrokeType
  stroke : NonEmptyString      -- Hex color
  strokeGradient : Option SplineStrokeGradient
  strokeWidth : Float
  strokeOpacity : Float        -- 0-100
  lineCap : LineCap
  lineJoin : LineJoin
  strokeMiterLimit : Float
  dashArray : Option (Array Float)
  dashOffset : Option Float
  -- Fill
  fill : Option NonEmptyString -- Hex color
  fillOpacity : Float          -- 0-100
  -- Trim paths
  trimStart : Option Float     -- 0-100%
  trimEnd : Option Float       -- 0-100%
  trimOffset : Option Float    -- degrees
  -- Effects
  pathEffects : Array SplinePathEffectInstance
  -- Animation
  animatedControlPoints : Option (Array AnimatableControlPoint)
  animated : Bool
  -- LOD
  lod : Option SplineLODSettings
  -- Audio reactive
  audioReactiveEnabled : Bool
  audioReactiveSourceLayerId : Option NonEmptyString
  -- Proofs
  strokeWidth_positive : strokeWidth > 0
  strokeWidth_finite : strokeWidth.isFinite
  strokeOpacity_ge_0 : strokeOpacity ≥ 0
  strokeOpacity_le_100 : strokeOpacity ≤ 100
  strokeOpacity_finite : strokeOpacity.isFinite
  fillOpacity_ge_0 : fillOpacity ≥ 0
  fillOpacity_le_100 : fillOpacity ≤ 100
  fillOpacity_finite : fillOpacity.isFinite
  deriving Repr

/-! ## Path Layer Data (motion paths, no visual) -/

/-- Path layer data (for motion paths, text-on-path, etc.) -/
structure PathLayerData where
  pathData : String
  controlPoints : Array ControlPoint
  closed : Bool
  showGuide : Bool
  guideColor : NonEmptyString
  guideDashPattern : (Float × Float)
  animatedControlPoints : Option (Array AnimatableControlPoint)
  animated : Bool
  deriving Repr

end Lattice.Spline
