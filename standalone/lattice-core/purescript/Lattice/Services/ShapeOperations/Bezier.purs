-- | Lattice.Services.ShapeOperations.Bezier - Cubic Bezier Curve Operations
-- |
-- | Pure cubic Bezier curve math:
-- | - Point evaluation at parameter t
-- | - Derivative (tangent) evaluation
-- | - De Casteljau subdivision
-- | - Arc length approximation
-- | - Bounding box calculation
-- |
-- | Source: ui/src/services/shapeOperations.ts (bezier utilities)

module Lattice.Services.ShapeOperations.Bezier
  ( -- * Types
    CubicBezier
  , BoundingBox
  , mkCubicBezier, mkBoundingBox
    -- * Point Evaluation
  , evalPoint, cubicBezierPoint
    -- * Derivative (Tangent)
  , evalDerivative, evalTangent, evalNormal
    -- * De Casteljau Subdivision
  , split, splitCubicBezier
    -- * Arc Length
  , arcLength, cubicBezierLength
  , parameterAtArcLength
    -- * Bounding Box
  , boundingBox
    -- * Flatten
  , flatten
    -- * Curvature
  , curvature
  ) where

import Prelude
import Data.Array (filter, foldl, range, (..), (:))
import Data.Int (toNumber)
import Data.Tuple (Tuple(..))
import Math (abs, sqrt) as Math

import Lattice.Services.ShapeOperations.Point2D as P2D

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | A cubic Bezier curve defined by 4 control points
type CubicBezier =
  { p0 :: P2D.Point2D  -- ^ Start point
  , p1 :: P2D.Point2D  -- ^ Start control
  , p2 :: P2D.Point2D  -- ^ End control
  , p3 :: P2D.Point2D  -- ^ End point
  }

-- | Constructor for CubicBezier
mkCubicBezier :: P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> CubicBezier
mkCubicBezier p0 p1 p2 p3 = { p0, p1, p2, p3 }

-- | Axis-aligned bounding box
type BoundingBox =
  { minX :: Number
  , minY :: Number
  , maxX :: Number
  , maxY :: Number
  }

-- | Constructor for BoundingBox
mkBoundingBox :: Number -> Number -> Number -> Number -> BoundingBox
mkBoundingBox minX minY maxX maxY = { minX, minY, maxX, maxY }

-- ────────────────────────────────────────────────────────────────────────────
-- Point Evaluation
-- ────────────────────────────────────────────────────────────────────────────

-- | Evaluate cubic Bezier at parameter t ∈ [0, 1].
-- | Uses the explicit form:
-- | B(t) = (1-t)³·P₀ + 3(1-t)²t·P₁ + 3(1-t)t²·P₂ + t³·P₃
evalPoint :: CubicBezier -> Number -> P2D.Point2D
evalPoint curve t =
  let mt = 1.0 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
      t2 = t * t
      t3 = t2 * t

      x = mt3 * curve.p0.x + 3.0 * mt2 * t * curve.p1.x +
          3.0 * mt * t2 * curve.p2.x + t3 * curve.p3.x
      y = mt3 * curve.p0.y + 3.0 * mt2 * t * curve.p1.y +
          3.0 * mt * t2 * curve.p2.y + t3 * curve.p3.y
  in { x, y }

-- | Evaluate cubic Bezier at t using 4 separate points
cubicBezierPoint :: P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> Number -> P2D.Point2D
cubicBezierPoint p0 p1 p2 p3 t = evalPoint { p0, p1, p2, p3 } t

-- ────────────────────────────────────────────────────────────────────────────
-- Derivative (Tangent)
-- ────────────────────────────────────────────────────────────────────────────

-- | Evaluate first derivative (tangent) of cubic Bezier at t.
-- | B'(t) = 3(1-t)²(P₁-P₀) + 6(1-t)t(P₂-P₁) + 3t²(P₃-P₂)
evalDerivative :: CubicBezier -> Number -> P2D.Point2D
evalDerivative curve t =
  let mt = 1.0 - t
      mt2 = mt * mt
      t2 = t * t

      dx = 3.0 * mt2 * (curve.p1.x - curve.p0.x) +
           6.0 * mt * t * (curve.p2.x - curve.p1.x) +
           3.0 * t2 * (curve.p3.x - curve.p2.x)
      dy = 3.0 * mt2 * (curve.p1.y - curve.p0.y) +
           6.0 * mt * t * (curve.p2.y - curve.p1.y) +
           3.0 * t2 * (curve.p3.y - curve.p2.y)
  in { x: dx, y: dy }

-- | Get normalized tangent at t
evalTangent :: CubicBezier -> Number -> P2D.Point2D
evalTangent curve t = P2D.normalize (evalDerivative curve t)

-- | Get normal (perpendicular to tangent) at t
evalNormal :: CubicBezier -> Number -> P2D.Point2D
evalNormal curve t = P2D.perpendicular (evalTangent curve t)

-- ────────────────────────────────────────────────────────────────────────────
-- De Casteljau Subdivision
-- ────────────────────────────────────────────────────────────────────────────

-- | Split a cubic Bezier at t using de Casteljau's algorithm.
-- | Returns (leftCurve, rightCurve)
split :: CubicBezier -> Number -> Tuple CubicBezier CubicBezier
split curve t =
  -- First level
  let q0 = P2D.lerp curve.p0 curve.p1 t
      q1 = P2D.lerp curve.p1 curve.p2 t
      q2 = P2D.lerp curve.p2 curve.p3 t

      -- Second level
      r0 = P2D.lerp q0 q1 t
      r1 = P2D.lerp q1 q2 t

      -- Split point
      s = P2D.lerp r0 r1 t

      left = { p0: curve.p0, p1: q0, p2: r0, p3: s }
      right = { p0: s, p1: r1, p2: q2, p3: curve.p3 }
  in Tuple left right

-- | Split using 4 separate points, return as arrays of 4 points each
splitCubicBezier :: P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> Number
                 -> Tuple (Array P2D.Point2D) (Array P2D.Point2D)
splitCubicBezier p0 p1 p2 p3 t =
  let Tuple left right = split { p0, p1, p2, p3 } t
  in Tuple [left.p0, left.p1, left.p2, left.p3]
           [right.p0, right.p1, right.p2, right.p3]

-- ────────────────────────────────────────────────────────────────────────────
-- Arc Length
-- ────────────────────────────────────────────────────────────────────────────

-- | Approximate arc length using subdivision.
arcLength :: CubicBezier -> Int -> Number
arcLength curve subdivisions =
  let n = max 1 subdivisions
      accumulate i prev accLen
        | i > n = accLen
        | otherwise =
            let t = toNumber i / toNumber n
                curr = evalPoint curve t
                segLen = P2D.distance prev curr
            in accumulate (i + 1) curr (accLen + segLen)
  in accumulate 1 (evalPoint curve 0.0) 0.0

-- | Arc length using 4 separate points
cubicBezierLength :: P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> Int -> Number
cubicBezierLength p0 p1 p2 p3 subdivisions =
  arcLength { p0, p1, p2, p3 } subdivisions

-- ────────────────────────────────────────────────────────────────────────────
-- Point at Arc Length
-- ────────────────────────────────────────────────────────────────────────────

-- | Find parameter t corresponding to a given arc length distance.
parameterAtArcLength :: CubicBezier -> Number -> Number -> Number -> Number
parameterAtArcLength curve targetDistance totalLength tolerance =
  let total = if totalLength > 0.0 then totalLength else arcLength curve 32
  in if total < tolerance then 0.0
     else if targetDistance <= 0.0 then 0.0
     else if targetDistance >= total then 1.0
     else
       let search lo hi fuel
             | fuel <= 0 = (lo + hi) / 2.0
             | hi - lo < tolerance = (lo + hi) / 2.0
             | otherwise =
                 let mid = (lo + hi) / 2.0
                     Tuple left _ = split curve mid
                     leftLen = arcLength left 16
                 in if leftLen < targetDistance
                    then search mid hi (fuel - 1)
                    else search lo mid (fuel - 1)
       in search 0.0 1.0 50

-- ────────────────────────────────────────────────────────────────────────────
-- Bounding Box
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate tight bounding box of cubic Bezier.
boundingBox :: CubicBezier -> BoundingBox
boundingBox curve =
  -- Start with endpoints
  let minX0 = min curve.p0.x curve.p3.x
      maxX0 = max curve.p0.x curve.p3.x
      minY0 = min curve.p0.y curve.p3.y
      maxY0 = max curve.p0.y curve.p3.y

      -- Coefficients for derivative
      ax = 3.0 * (-curve.p0.x + 3.0 * curve.p1.x - 3.0 * curve.p2.x + curve.p3.x)
      bx = 6.0 * (curve.p0.x - 2.0 * curve.p1.x + curve.p2.x)
      cx = 3.0 * (curve.p1.x - curve.p0.x)

      ay = 3.0 * (-curve.p0.y + 3.0 * curve.p1.y - 3.0 * curve.p2.y + curve.p3.y)
      by = 6.0 * (curve.p0.y - 2.0 * curve.p1.y + curve.p2.y)
      cy = 3.0 * (curve.p1.y - curve.p0.y)

      -- Solve quadratic
      solveQuadratic a b c
        | Math.abs a < 0.0001 =
            if Math.abs b < 0.0001 then []
            else let t = -c / b
                 in if t > 0.0 && t < 1.0 then [t] else []
        | otherwise =
            let disc = b * b - 4.0 * a * c
            in if disc < 0.0 then []
               else let sqrtDisc = Math.sqrt disc
                        t1 = (-b + sqrtDisc) / (2.0 * a)
                        t2 = (-b - sqrtDisc) / (2.0 * a)
                        valid t = t > 0.0 && t < 1.0
                    in filter valid (if t1 == t2 then [t1] else [t1, t2])

      xRoots = solveQuadratic ax bx cx
      yRoots = solveQuadratic ay by cy

      updateBoundsX acc t =
        let pt = evalPoint curve t
        in { mn: min acc.mn pt.x, mx: max acc.mx pt.x }

      updateBoundsY acc t =
        let pt = evalPoint curve t
        in { mn: min acc.mn pt.y, mx: max acc.mx pt.y }

      xBounds = foldl updateBoundsX { mn: minX0, mx: maxX0 } xRoots
      yBounds = foldl updateBoundsY { mn: minY0, mx: maxY0 } yRoots

  in { minX: xBounds.mn, minY: yBounds.mn, maxX: xBounds.mx, maxY: yBounds.mx }

-- ────────────────────────────────────────────────────────────────────────────
-- Flatten
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert Bezier curve to polyline with specified number of segments
flatten :: CubicBezier -> Int -> Array P2D.Point2D
flatten curve segments =
  let n = max 2 segments
  in map (\i -> evalPoint curve (toNumber i / toNumber n)) (range 0 n)

-- ────────────────────────────────────────────────────────────────────────────
-- Curvature
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate curvature at parameter t.
-- | κ = |B'(t) × B''(t)| / |B'(t)|³
curvature :: CubicBezier -> Number -> Number
curvature curve t =
  let d1 = evalDerivative curve t
      speed = P2D.len d1
  in if speed < 0.0001 then 0.0
     else
       let mt = 1.0 - t
           d2x = 6.0 * mt * (curve.p2.x - 2.0 * curve.p1.x + curve.p0.x) +
                 6.0 * t * (curve.p3.x - 2.0 * curve.p2.x + curve.p1.x)
           d2y = 6.0 * mt * (curve.p2.y - 2.0 * curve.p1.y + curve.p0.y) +
                 6.0 * t * (curve.p3.y - 2.0 * curve.p2.y + curve.p1.y)
           crossMag = Math.abs (d1.x * d2y - d1.y * d2x)
       in crossMag / (speed * speed * speed)
