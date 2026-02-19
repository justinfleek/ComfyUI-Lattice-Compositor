-- | Lattice.Services.ColorCorrection.Curves - Curve Interpolation Functions
-- |
-- | Pure mathematical functions for curve-based color adjustment:
-- | - Cubic Bezier evaluation
-- | - Catmull-Rom tangent calculation
-- | - S-curve generation
-- | - Lift curve generation
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts (lines 468-705)

module Lattice.Services.ColorCorrection.Curves
  ( CurvePoint
  , cubicBezier
  , catmullRomTangent
  , segmentParameter
  , evaluateCurveSegment
  , createSCurve
  , createLiftCurve
  , identityCurve
  , clampToUint8
  ) where

import Prelude

import Math (max, min, round)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | A point on a curve
type CurvePoint =
  { x :: Number  -- ^ Input value (0-255)
  , y :: Number  -- ^ Output value (0-255)
  }

--------------------------------------------------------------------------------
-- Cubic Bezier
--------------------------------------------------------------------------------

-- | Evaluate a cubic Bezier curve at parameter t.
-- |
-- | Formula: B(t) = (1-t)³P₀ + 3(1-t)²tP₁ + 3(1-t)t²P₂ + t³P₃
cubicBezier :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezier p0 p1 p2 p3 t =
  let t2 = t * t
      t3 = t2 * t
      mt = 1.0 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
  in mt3 * p0 + 3.0 * mt2 * t * p1 + 3.0 * mt * t2 * p2 + t3 * p3

--------------------------------------------------------------------------------
-- Catmull-Rom Tangent
--------------------------------------------------------------------------------

-- | Calculate Catmull-Rom tangent for a curve segment.
catmullRomTangent :: Number -> Number -> Number -> Number -> Number -> Number
catmullRomTangent prevY prevX nextY nextX segmentWidth =
  let dx = nextX - prevX
  in if dx < 0.0001 then 0.0
     else ((nextY - prevY) / dx) * segmentWidth

--------------------------------------------------------------------------------
-- Curve Evaluation
--------------------------------------------------------------------------------

-- | Linear interpolation parameter for a value in a segment.
segmentParameter :: Number -> Number -> Number -> Number
segmentParameter value segmentStart segmentEnd =
  let range = segmentEnd - segmentStart
  in if range < 0.0001 then 0.0
     else max 0.0 (min 1.0 ((value - segmentStart) / range))

-- | Evaluate a curve segment using cubic interpolation.
evaluateCurveSegment :: Number -> Number -> Number -> Number -> Boolean
                     -> Number -> Number -> Boolean -> Number -> Number
                     -> Number -> Number
evaluateCurveSegment p0x p0y p1x p1y hasPrev prevX prevY hasNext nextX nextY t =
  let segWidth = p1x - p0x
      tangent0 = if hasPrev
                 then catmullRomTangent prevY prevX p1y p1x segWidth
                 else 0.0
      tangent1 = if hasNext
                 then catmullRomTangent p0y p0x nextY nextX segWidth
                 else 0.0
      cp1y = p0y + tangent0 / 3.0
      cp2y = p1y - tangent1 / 3.0
      result = cubicBezier p0y cp1y cp2y p1y t
  in max 0.0 (min 255.0 result)

--------------------------------------------------------------------------------
-- Preset Curves
--------------------------------------------------------------------------------

-- | Create an S-curve for contrast adjustment.
createSCurve :: Number -> Array CurvePoint
createSCurve amount =
  let midPoint = 128.0
      adjustment = amount * 50.0
  in [ { x: 0.0,   y: 0.0 }
     , { x: 64.0,  y: max 0.0 (64.0 - adjustment) }
     , { x: midPoint, y: midPoint }
     , { x: 192.0, y: min 255.0 (192.0 + adjustment) }
     , { x: 255.0, y: 255.0 }
     ]

-- | Create a lift curve for shadow/highlight adjustment.
createLiftCurve :: Number -> Number -> Array CurvePoint
createLiftCurve shadowLift highlightLift =
  [ { x: 0.0,   y: max 0.0 (min 128.0 shadowLift) }
  , { x: 128.0, y: 128.0 }
  , { x: 255.0, y: max 128.0 (min 255.0 (255.0 + highlightLift)) }
  ]

-- | Identity curve (input = output).
identityCurve :: Array CurvePoint
identityCurve = [{ x: 0.0, y: 0.0 }, { x: 255.0, y: 255.0 }]

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Clamp and round to valid 8-bit range.
clampToUint8 :: Number -> Number
clampToUint8 value = round (max 0.0 (min 255.0 value))
