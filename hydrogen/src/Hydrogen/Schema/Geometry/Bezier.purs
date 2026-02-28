-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // bezier
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier — Quadratic and cubic Bezier curves.
-- |
-- | ## Design Philosophy
-- |
-- | Bezier curves are the mathematical foundation for smooth motion in digital
-- | systems. Every animation, easing function, and path is built on them.
-- |
-- | Two variants are provided:
-- | - **QuadBezier**: 3 control points (P0, P1, P2) — simpler, cheaper
-- | - **CubicBezier**: 4 control points (P0, P1, P2, P3) — more flexible, standard
-- |
-- | Both use the De Casteljau algorithm for evaluation and subdivision.
-- |
-- | ## Mathematical Foundation
-- |
-- | Quadratic: B(t) = (1-t)²P0 + 2(1-t)tP1 + t²P2
-- | Cubic:     B(t) = (1-t)³P0 + 3(1-t)²tP1 + 3(1-t)t²P2 + t³P3
-- |
-- | Parameter t ∈ [0, 1] traces the curve from start to end.
-- |
-- | ## Use Cases
-- |
-- | - Animation easing curves (CSS cubic-bezier)
-- | - Path segments in vector graphics
-- | - Motion trajectories for agents
-- | - Smooth interpolation between states
-- | - Font glyph outlines
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D for control points)
-- | - Schema.Geometry.Vector (tangent vectors)

module Hydrogen.Schema.Geometry.Bezier
  ( -- * Quadratic Bezier
    QuadBezier(QuadBezier)
  , quadBezier
  
  -- * Cubic Bezier
  , CubicBezier(CubicBezier)
  , cubicBezier
  
  -- * Accessors
  , quadStart
  , quadControl
  , quadEnd
  , cubicStart
  , cubicControl1
  , cubicControl2
  , cubicEnd
  
  -- * Evaluation
  , quadPointAt
  , cubicPointAt
  , quadTangentAt
  , cubicTangentAt
  
  -- * Subdivision
  , quadSplitAt
  , cubicSplitAt
  
  -- * Geometry
  , quadBoundingBox
  , cubicBoundingBox
  , quadLength
  , cubicLength
  , quadCurvatureAt
  , cubicCurvatureAt
  
  -- * Hit Testing
  , quadClosestParameter
  , cubicClosestParameter
  , quadDistanceToPoint
  , cubicDistanceToPoint
  
  -- * Common Easing Curves
  , easeLinear
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , negate
  , min
  , max
  )

import Data.Number (sqrt)
import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Data.Int (toNumber)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2, magnitude2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // quadratic bezier
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quadratic Bezier curve with 3 control points.
-- |
-- | P0 = start point (on curve)
-- | P1 = control point (off curve, defines tangent)
-- | P2 = end point (on curve)
newtype QuadBezier = QuadBezier
  { p0 :: Point2D
  , p1 :: Point2D
  , p2 :: Point2D
  }

derive instance eqQuadBezier :: Eq QuadBezier

instance showQuadBezier :: Show QuadBezier where
  show (QuadBezier b) = "(QuadBezier p0:" <> show b.p0 
    <> " p1:" <> show b.p1 
    <> " p2:" <> show b.p2 <> ")"

-- | Create a quadratic Bezier curve
quadBezier :: Point2D -> Point2D -> Point2D -> QuadBezier
quadBezier p0 p1 p2 = QuadBezier { p0, p1, p2 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cubic bezier
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cubic Bezier curve with 4 control points.
-- |
-- | P0 = start point (on curve)
-- | P1 = first control point (defines start tangent)
-- | P2 = second control point (defines end tangent)
-- | P3 = end point (on curve)
-- |
-- | This is the standard form used in SVG paths and CSS animations.
newtype CubicBezier = CubicBezier
  { p0 :: Point2D
  , p1 :: Point2D
  , p2 :: Point2D
  , p3 :: Point2D
  }

derive instance eqCubicBezier :: Eq CubicBezier

instance showCubicBezier :: Show CubicBezier where
  show (CubicBezier b) = "(CubicBezier p0:" <> show b.p0 
    <> " p1:" <> show b.p1 
    <> " p2:" <> show b.p2 
    <> " p3:" <> show b.p3 <> ")"

-- | Create a cubic Bezier curve
cubicBezier :: Point2D -> Point2D -> Point2D -> Point2D -> CubicBezier
cubicBezier p0 p1 p2 p3 = CubicBezier { p0, p1, p2, p3 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get start point of quadratic Bezier
quadStart :: QuadBezier -> Point2D
quadStart (QuadBezier b) = b.p0

-- | Get control point of quadratic Bezier
quadControl :: QuadBezier -> Point2D
quadControl (QuadBezier b) = b.p1

-- | Get end point of quadratic Bezier
quadEnd :: QuadBezier -> Point2D
quadEnd (QuadBezier b) = b.p2

-- | Get start point of cubic Bezier
cubicStart :: CubicBezier -> Point2D
cubicStart (CubicBezier b) = b.p0

-- | Get first control point of cubic Bezier
cubicControl1 :: CubicBezier -> Point2D
cubicControl1 (CubicBezier b) = b.p1

-- | Get second control point of cubic Bezier
cubicControl2 :: CubicBezier -> Point2D
cubicControl2 (CubicBezier b) = b.p2

-- | Get end point of cubic Bezier
cubicEnd :: CubicBezier -> Point2D
cubicEnd (CubicBezier b) = b.p3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate quadratic Bezier at parameter t ∈ [0, 1].
-- |
-- | Uses De Casteljau algorithm for numerical stability.
-- | B(t) = (1-t)²P0 + 2(1-t)tP1 + t²P2
quadPointAt :: Number -> QuadBezier -> Point2D
quadPointAt t (QuadBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    -- De Casteljau: linear interpolation at each level
    -- Level 1: interpolate between adjacent control points
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    q0x = mt * p0.x + t' * p1.x
    q0y = mt * p0.y + t' * p1.y
    q1x = mt * p1.x + t' * p2.x
    q1y = mt * p1.y + t' * p2.y
    
    -- Level 2: interpolate between level 1 points
    rx = mt * q0x + t' * q1x
    ry = mt * q0y + t' * q1y
  in
    point2D rx ry

-- | Evaluate cubic Bezier at parameter t ∈ [0, 1].
-- |
-- | Uses De Casteljau algorithm for numerical stability.
-- | B(t) = (1-t)³P0 + 3(1-t)²tP1 + 3(1-t)t²P2 + t³P3
cubicPointAt :: Number -> CubicBezier -> Point2D
cubicPointAt t (CubicBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    (Point2D p3) = b.p3
    
    -- Level 1
    q0x = mt * p0.x + t' * p1.x
    q0y = mt * p0.y + t' * p1.y
    q1x = mt * p1.x + t' * p2.x
    q1y = mt * p1.y + t' * p2.y
    q2x = mt * p2.x + t' * p3.x
    q2y = mt * p2.y + t' * p3.y
    
    -- Level 2
    r0x = mt * q0x + t' * q1x
    r0y = mt * q0y + t' * q1y
    r1x = mt * q1x + t' * q2x
    r1y = mt * q1y + t' * q2y
    
    -- Level 3 (final point)
    sx = mt * r0x + t' * r1x
    sy = mt * r0y + t' * r1y
  in
    point2D sx sy

-- | Tangent vector at parameter t for quadratic Bezier.
-- |
-- | The derivative of a quadratic Bezier is a linear function:
-- | B'(t) = 2(1-t)(P1-P0) + 2t(P2-P1)
quadTangentAt :: Number -> QuadBezier -> Vector2D
quadTangentAt t (QuadBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    -- Derivative coefficients
    dx = 2.0 * (mt * (p1.x - p0.x) + t' * (p2.x - p1.x))
    dy = 2.0 * (mt * (p1.y - p0.y) + t' * (p2.y - p1.y))
  in
    vec2 dx dy

-- | Tangent vector at parameter t for cubic Bezier.
-- |
-- | The derivative of a cubic Bezier is a quadratic function:
-- | B'(t) = 3(1-t)²(P1-P0) + 6(1-t)t(P2-P1) + 3t²(P3-P2)
cubicTangentAt :: Number -> CubicBezier -> Vector2D
cubicTangentAt t (CubicBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    (Point2D p3) = b.p3
    
    -- Derivative coefficients
    c0x = p1.x - p0.x
    c0y = p1.y - p0.y
    c1x = p2.x - p1.x
    c1y = p2.y - p1.y
    c2x = p3.x - p2.x
    c2y = p3.y - p2.y
    
    dx = 3.0 * (mt * mt * c0x + 2.0 * mt * t' * c1x + t' * t' * c2x)
    dy = 3.0 * (mt * mt * c0y + 2.0 * mt * t' * c1y + t' * t' * c2y)
  in
    vec2 dx dy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // subdivision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Split quadratic Bezier at parameter t into two curves.
-- |
-- | Uses De Casteljau algorithm — the intermediate points from evaluation
-- | become the control points of the two resulting curves.
quadSplitAt :: Number -> QuadBezier -> { left :: QuadBezier, right :: QuadBezier }
quadSplitAt t (QuadBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    -- Level 1 points
    q0 = point2D (mt * p0.x + t' * p1.x) (mt * p0.y + t' * p1.y)
    q1 = point2D (mt * p1.x + t' * p2.x) (mt * p1.y + t' * p2.y)
    
    -- Level 2 point (the split point)
    (Point2D q0') = q0
    (Point2D q1') = q1
    r = point2D (mt * q0'.x + t' * q1'.x) (mt * q0'.y + t' * q1'.y)
  in
    { left: quadBezier b.p0 q0 r
    , right: quadBezier r q1 b.p2
    }

-- | Split cubic Bezier at parameter t into two curves.
-- |
-- | Uses De Casteljau algorithm.
cubicSplitAt :: Number -> CubicBezier -> { left :: CubicBezier, right :: CubicBezier }
cubicSplitAt t (CubicBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    (Point2D p3) = b.p3
    
    -- Level 1 points
    q0 = point2D (mt * p0.x + t' * p1.x) (mt * p0.y + t' * p1.y)
    q1 = point2D (mt * p1.x + t' * p2.x) (mt * p1.y + t' * p2.y)
    q2 = point2D (mt * p2.x + t' * p3.x) (mt * p2.y + t' * p3.y)
    
    -- Level 2 points
    (Point2D q0') = q0
    (Point2D q1') = q1
    (Point2D q2') = q2
    r0 = point2D (mt * q0'.x + t' * q1'.x) (mt * q0'.y + t' * q1'.y)
    r1 = point2D (mt * q1'.x + t' * q2'.x) (mt * q1'.y + t' * q2'.y)
    
    -- Level 3 point (the split point)
    (Point2D r0') = r0
    (Point2D r1') = r1
    s = point2D (mt * r0'.x + t' * r1'.x) (mt * r0'.y + t' * r1'.y)
  in
    { left: cubicBezier b.p0 q0 r0 s
    , right: cubicBezier s r1 q2 b.p3
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis-aligned bounding box for quadratic Bezier.
-- |
-- | Finds extrema by solving B'(t) = 0 for each axis.
quadBoundingBox :: QuadBezier -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
quadBoundingBox (QuadBezier b) =
  let
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    -- Start with endpoints
    minX0 = min p0.x p2.x
    maxX0 = max p0.x p2.x
    minY0 = min p0.y p2.y
    maxY0 = max p0.y p2.y
    
    -- Find t where derivative is zero for each axis
    -- B'(t) = 2[(1-t)(P1-P0) + t(P2-P1)] = 0
    -- Solving: t = (P0-P1) / (P0 - 2P1 + P2)
    
    -- X axis extremum
    denomX = p0.x - 2.0 * p1.x + p2.x
    tX = if denomX == 0.0 then (-1.0) else (p0.x - p1.x) / denomX
    extremeX = if tX > 0.0 && tX < 1.0
      then quadPointAtX tX p0.x p1.x p2.x
      else p0.x  -- dummy, won't affect bounds
    
    -- Y axis extremum  
    denomY = p0.y - 2.0 * p1.y + p2.y
    tY = if denomY == 0.0 then (-1.0) else (p0.y - p1.y) / denomY
    extremeY = if tY > 0.0 && tY < 1.0
      then quadPointAtY tY p0.y p1.y p2.y
      else p0.y
    
    -- Expand bounds if extrema are within curve
    minX1 = if tX > 0.0 && tX < 1.0 then min minX0 extremeX else minX0
    maxX1 = if tX > 0.0 && tX < 1.0 then max maxX0 extremeX else maxX0
    minY1 = if tY > 0.0 && tY < 1.0 then min minY0 extremeY else minY0
    maxY1 = if tY > 0.0 && tY < 1.0 then max maxY0 extremeY else maxY0
  in
    { minX: minX1, minY: minY1, maxX: maxX1, maxY: maxY1 }

-- | Axis-aligned bounding box for cubic Bezier.
-- |
-- | Finds extrema by solving the quadratic B'(t) = 0 for each axis.
cubicBoundingBox :: CubicBezier -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
cubicBoundingBox (CubicBezier b) =
  let
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    (Point2D p3) = b.p3
    
    -- Start with endpoints
    minX0 = min p0.x p3.x
    maxX0 = max p0.x p3.x
    minY0 = min p0.y p3.y
    maxY0 = max p0.y p3.y
    
    -- X axis extrema
    xExtrema = cubicExtrema p0.x p1.x p2.x p3.x
    minX1 = foldExtrema min minX0 xExtrema (CubicBezier b) getX
    maxX1 = foldExtrema max maxX0 xExtrema (CubicBezier b) getX
    
    -- Y axis extrema
    yExtrema = cubicExtrema p0.y p1.y p2.y p3.y
    minY1 = foldExtrema min minY0 yExtrema (CubicBezier b) getY
    maxY1 = foldExtrema max maxY0 yExtrema (CubicBezier b) getY
  in
    { minX: minX1, minY: minY1, maxX: maxX1, maxY: maxY1 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // arc length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximate arc length of quadratic Bezier.
-- |
-- | Uses Gaussian quadrature (5-point) for numerical integration.
-- | Accuracy is typically within 0.1% for well-behaved curves.
quadLength :: QuadBezier -> Number
quadLength curve =
  gaussianQuadrature5 (\t -> magnitude2 (quadTangentAt t curve)) 0.0 1.0

-- | Approximate arc length of cubic Bezier.
-- |
-- | Uses Gaussian quadrature (5-point) for numerical integration.
cubicLength :: CubicBezier -> Number
cubicLength curve =
  gaussianQuadrature5 (\t -> magnitude2 (cubicTangentAt t curve)) 0.0 1.0

-- | 5-point Gaussian quadrature for numerical integration.
-- |
-- | Integrates f over [a, b] using Legendre-Gauss weights.
-- | This provides O(h^10) accuracy for smooth functions.
gaussianQuadrature5 :: (Number -> Number) -> Number -> Number -> Number
gaussianQuadrature5 f a b =
  let
    -- Gauss-Legendre nodes and weights for n=5
    -- Nodes are roots of P_5(x) on [-1, 1]
    nodes = 
      [ { x: 0.0, w: 0.5688888888888889 }
      , { x: 0.5384693101056831, w: 0.47862867049936647 }
      , { x: negate 0.5384693101056831, w: 0.47862867049936647 }
      , { x: 0.9061798459386640, w: 0.23692688505618908 }
      , { x: negate 0.9061798459386640, w: 0.23692688505618908 }
      ]
    
    -- Transform from [-1, 1] to [a, b]
    halfWidth = (b - a) / 2.0
    midpoint = (a + b) / 2.0
    
    -- Sum weighted function evaluations
    sumTerms = foldl (\acc node -> 
      let t = midpoint + halfWidth * node.x
      in acc + node.w * f t
    ) 0.0 nodes
  in
    halfWidth * sumTerms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // curvature
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signed curvature at parameter t for quadratic Bezier.
-- |
-- | Curvature κ = (x'y'' - y'x'') / (x'² + y'²)^(3/2)
-- | Positive = counter-clockwise, Negative = clockwise
-- |
-- | Returns 0 if tangent magnitude is near zero (degenerate case).
quadCurvatureAt :: Number -> QuadBezier -> Number
quadCurvatureAt t (QuadBezier b) =
  let
    t' = clamp01 t
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    -- First derivative (tangent)
    -- B'(t) = 2[(1-t)(P1-P0) + t(P2-P1)]
    mt = 1.0 - t'
    dx = 2.0 * (mt * (p1.x - p0.x) + t' * (p2.x - p1.x))
    dy = 2.0 * (mt * (p1.y - p0.y) + t' * (p2.y - p1.y))
    
    -- Second derivative (constant for quadratic)
    -- B''(t) = 2(P0 - 2P1 + P2)
    ddx = 2.0 * (p0.x - 2.0 * p1.x + p2.x)
    ddy = 2.0 * (p0.y - 2.0 * p1.y + p2.y)
    
    -- Curvature formula
    cross = dx * ddy - dy * ddx
    speedSq = dx * dx + dy * dy
    speed = sqrt speedSq
    speedCubed = speedSq * speed
  in
    if speedCubed < epsilon then 0.0
    else cross / speedCubed

-- | Signed curvature at parameter t for cubic Bezier.
-- |
-- | Returns 0 if tangent magnitude is near zero.
cubicCurvatureAt :: Number -> CubicBezier -> Number
cubicCurvatureAt t (CubicBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    (Point2D p3) = b.p3
    
    -- Derivative control points
    c0x = p1.x - p0.x
    c0y = p1.y - p0.y
    c1x = p2.x - p1.x
    c1y = p2.y - p1.y
    c2x = p3.x - p2.x
    c2y = p3.y - p2.y
    
    -- First derivative
    -- B'(t) = 3[(1-t)²(P1-P0) + 2(1-t)t(P2-P1) + t²(P3-P2)]
    dx = 3.0 * (mt * mt * c0x + 2.0 * mt * t' * c1x + t' * t' * c2x)
    dy = 3.0 * (mt * mt * c0y + 2.0 * mt * t' * c1y + t' * t' * c2y)
    
    -- Second derivative
    -- B''(t) = 6[(1-t)(P0-2P1+P2) + t(P1-2P2+P3)]
    d0x = p0.x - 2.0 * p1.x + p2.x
    d0y = p0.y - 2.0 * p1.y + p2.y
    d1x = p1.x - 2.0 * p2.x + p3.x
    d1y = p1.y - 2.0 * p2.y + p3.y
    
    ddx = 6.0 * (mt * d0x + t' * d1x)
    ddy = 6.0 * (mt * d0y + t' * d1y)
    
    -- Curvature
    cross = dx * ddy - dy * ddx
    speedSq = dx * dx + dy * dy
    speed = sqrt speedSq
    speedCubed = speedSq * speed
  in
    if speedCubed < epsilon then 0.0
    else cross / speedCubed

-- | Small value for numerical comparisons
epsilon :: Number
epsilon = 0.0000001

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hit testing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find parameter t where quadratic Bezier is closest to given point.
-- |
-- | Uses iterative refinement (golden section search) to find the minimum
-- | distance. Returns t ∈ [0, 1].
-- |
-- | Returns Nothing if curve is degenerate (all control points coincident).
quadClosestParameter :: Point2D -> QuadBezier -> Maybe Number
quadClosestParameter target curve =
  let
    -- Check for degenerate curve
    (Point2D p0) = quadStart curve
    (Point2D p2) = quadEnd curve
    dx = p2.x - p0.x
    dy = p2.y - p0.y
    curveSpan = sqrt (dx * dx + dy * dy)
  in
    if curveSpan < epsilon then Nothing
    else Just (goldenSectionSearch (\t -> quadDistanceSq t target curve) 0.0 1.0 20)

-- | Find parameter t where cubic Bezier is closest to given point.
-- |
-- | Uses iterative refinement (golden section search) to find the minimum
-- | distance. Returns t ∈ [0, 1].
-- |
-- | Returns Nothing if curve is degenerate.
cubicClosestParameter :: Point2D -> CubicBezier -> Maybe Number
cubicClosestParameter target curve =
  let
    (Point2D p0) = cubicStart curve
    (Point2D p3) = cubicEnd curve
    dx = p3.x - p0.x
    dy = p3.y - p0.y
    curveSpan = sqrt (dx * dx + dy * dy)
  in
    if curveSpan < epsilon then Nothing
    else Just (goldenSectionSearch (\t -> cubicDistanceSq t target curve) 0.0 1.0 20)

-- | Distance from a point to the closest point on a quadratic Bezier.
-- |
-- | Returns Nothing if curve is degenerate.
quadDistanceToPoint :: Point2D -> QuadBezier -> Maybe Number
quadDistanceToPoint target curve =
  case quadClosestParameter target curve of
    Nothing -> Nothing
    Just t -> 
      let 
        closest = quadPointAt t curve
        (Point2D c) = closest
        (Point2D p) = target
        dx = c.x - p.x
        dy = c.y - p.y
      in Just (sqrt (dx * dx + dy * dy))

-- | Distance from a point to the closest point on a cubic Bezier.
-- |
-- | Returns Nothing if curve is degenerate.
cubicDistanceToPoint :: Point2D -> CubicBezier -> Maybe Number
cubicDistanceToPoint target curve =
  case cubicClosestParameter target curve of
    Nothing -> Nothing
    Just t ->
      let
        closest = cubicPointAt t curve
        (Point2D c) = closest
        (Point2D p) = target
        dx = c.x - p.x
        dy = c.y - p.y
      in Just (sqrt (dx * dx + dy * dy))

-- | Squared distance from point on curve at t to target point.
quadDistanceSq :: Number -> Point2D -> QuadBezier -> Number
quadDistanceSq t target curve =
  let
    (Point2D p) = quadPointAt t curve
    (Point2D q) = target
    dx = p.x - q.x
    dy = p.y - q.y
  in dx * dx + dy * dy

-- | Squared distance from point on curve at t to target point.
cubicDistanceSq :: Number -> Point2D -> CubicBezier -> Number
cubicDistanceSq t target curve =
  let
    (Point2D p) = cubicPointAt t curve
    (Point2D q) = target
    dx = p.x - q.x
    dy = p.y - q.y
  in dx * dx + dy * dy

-- | Golden section search for minimum of unimodal function on [a, b].
-- |
-- | Uses the golden ratio to efficiently narrow down the minimum.
-- | Iterations parameter controls precision (20 gives ~10^-9 precision).
goldenSectionSearch :: (Number -> Number) -> Number -> Number -> Int -> Number
goldenSectionSearch f a b iterations =
  goldenSectionImpl f a b iterations phi invPhi
  where
    -- Golden ratio constants
    phi = (1.0 + sqrt 5.0) / 2.0
    invPhi = 1.0 / phi

goldenSectionImpl :: (Number -> Number) -> Number -> Number -> Int -> Number -> Number -> Number
goldenSectionImpl f a b remaining phi invPhi =
  if remaining <= 0 || (b - a) < epsilon then
    (a + b) / 2.0
  else
    let
      c = b - (b - a) * invPhi
      d = a + (b - a) * invPhi
      fc = f c
      fd = f d
    in
      if fc < fd then
        goldenSectionImpl f a d (remaining - 1) phi invPhi
      else
        goldenSectionImpl f c b (remaining - 1) phi invPhi

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // common easing curves
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear easing (no acceleration).
-- |
-- | CSS: cubic-bezier(0.0, 0.0, 1.0, 1.0)
easeLinear :: CubicBezier
easeLinear = cubicBezier 
  (point2D 0.0 0.0) 
  (point2D 0.0 0.0) 
  (point2D 1.0 1.0) 
  (point2D 1.0 1.0)

-- | Ease-in quadratic (slow start).
-- |
-- | CSS: cubic-bezier(0.55, 0.085, 0.68, 0.53)
easeInQuad :: CubicBezier
easeInQuad = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.55 0.085)
  (point2D 0.68 0.53)
  (point2D 1.0 1.0)

-- | Ease-out quadratic (slow end).
-- |
-- | CSS: cubic-bezier(0.25, 0.46, 0.45, 0.94)
easeOutQuad :: CubicBezier
easeOutQuad = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.25 0.46)
  (point2D 0.45 0.94)
  (point2D 1.0 1.0)

-- | Ease-in-out quadratic (slow start and end).
-- |
-- | CSS: cubic-bezier(0.455, 0.03, 0.515, 0.955)
easeInOutQuad :: CubicBezier
easeInOutQuad = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.455 0.03)
  (point2D 0.515 0.955)
  (point2D 1.0 1.0)

-- | Ease-in cubic (slower start than quadratic).
-- |
-- | CSS: cubic-bezier(0.55, 0.055, 0.675, 0.19)
easeInCubic :: CubicBezier
easeInCubic = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.55 0.055)
  (point2D 0.675 0.19)
  (point2D 1.0 1.0)

-- | Ease-out cubic (slower end than quadratic).
-- |
-- | CSS: cubic-bezier(0.215, 0.61, 0.355, 1.0)
easeOutCubic :: CubicBezier
easeOutCubic = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.215 0.61)
  (point2D 0.355 1.0)
  (point2D 1.0 1.0)

-- | Ease-in-out cubic (slower start and end than quadratic).
-- |
-- | CSS: cubic-bezier(0.645, 0.045, 0.355, 1.0)
easeInOutCubic :: CubicBezier
easeInOutCubic = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.645 0.045)
  (point2D 0.355 1.0)
  (point2D 1.0 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | true = n

-- | Evaluate quadratic at t for single axis
quadPointAtX :: Number -> Number -> Number -> Number -> Number
quadPointAtX t p0 p1 p2 =
  let mt = 1.0 - t
  in mt * mt * p0 + 2.0 * mt * t * p1 + t * t * p2

quadPointAtY :: Number -> Number -> Number -> Number -> Number
quadPointAtY = quadPointAtX

-- | Find t values where cubic derivative is zero (extrema).
-- |
-- | Solves: 3(1-t)²(P1-P0) + 6(1-t)t(P2-P1) + 3t²(P3-P2) = 0
-- | Simplifies to quadratic: at² + bt + c = 0
cubicExtrema :: Number -> Number -> Number -> Number -> Array Number
cubicExtrema p0 p1 p2 p3 =
  let
    -- Coefficients of derivative
    c0 = p1 - p0
    c1 = p2 - p1
    c2 = p3 - p2
    
    -- Quadratic coefficients: at² + bt + c = 0
    a = c0 - 2.0 * c1 + c2
    b = 2.0 * (c1 - c0)
    c = c0
    
    discriminant = b * b - 4.0 * a * c
  in
    if a == 0.0 then
      -- Linear case
      if b == 0.0 then []
      else 
        let t = negate c / b
        in if t > 0.0 && t < 1.0 then [t] else []
    else if discriminant < 0.0 then
      -- No real roots
      []
    else if discriminant == 0.0 then
      -- One root
      let t = negate b / (2.0 * a)
      in if t > 0.0 && t < 1.0 then [t] else []
    else
      -- Two roots
      let
        sqrtD = sqrt discriminant
        t1 = (negate b - sqrtD) / (2.0 * a)
        t2 = (negate b + sqrtD) / (2.0 * a)
        valid1 = t1 > 0.0 && t1 < 1.0
        valid2 = t2 > 0.0 && t2 < 1.0
      in
        if valid1 && valid2 then [t1, t2]
        else if valid1 then [t1]
        else if valid2 then [t2]
        else []

-- | Fold extrema into bounds
foldExtrema 
  :: (Number -> Number -> Number) 
  -> Number 
  -> Array Number 
  -> CubicBezier 
  -> (Point2D -> Number) 
  -> Number
foldExtrema f initial ts curve accessor =
  foldl (\acc t -> f acc (accessor (cubicPointAt t curve))) initial ts

-- | Get X coordinate from Point2D
getX :: Point2D -> Number
getX (Point2D p) = p.x

-- | Get Y coordinate from Point2D
getY :: Point2D -> Number
getY (Point2D p) = p.y
