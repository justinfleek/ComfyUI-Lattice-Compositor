{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.ShapeOperations.Bezier
Description : Cubic Bezier Curve Operations
Copyright   : (c) Lattice, 2026
License     : MIT

Pure cubic Bezier curve math:
- Point evaluation at parameter t
- Derivative (tangent) evaluation
- De Casteljau subdivision
- Arc length approximation
- Bounding box calculation

Source: ui/src/services/shapeOperations.ts (bezier utilities)
-}

module Lattice.Services.ShapeOperations.Bezier
  ( -- * Types
    CubicBezier(..)
  , BoundingBox(..)
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

import Data.Vector (Vector)
import qualified Data.Vector as V

import Lattice.Services.ShapeOperations.Point2D

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | A cubic Bezier curve defined by 4 control points:
-- p0 = start point, p1 = start control, p2 = end control, p3 = end point
data CubicBezier = CubicBezier
  { cbP0 :: Point2D
  , cbP1 :: Point2D
  , cbP2 :: Point2D
  , cbP3 :: Point2D
  } deriving (Show, Eq)

-- | Axis-aligned bounding box
data BoundingBox = BoundingBox
  { bbMinX :: Double
  , bbMinY :: Double
  , bbMaxX :: Double
  , bbMaxY :: Double
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Point Evaluation
--------------------------------------------------------------------------------

-- | Evaluate cubic Bezier at parameter t ∈ [0, 1].
-- Uses the explicit form:
-- B(t) = (1-t)³·P₀ + 3(1-t)²t·P₁ + 3(1-t)t²·P₂ + t³·P₃
evalPoint :: CubicBezier -> Double -> Point2D
evalPoint (CubicBezier p0 p1 p2 p3) t =
  let mt = 1 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
      t2 = t * t
      t3 = t2 * t

      x = mt3 * px p0 + 3 * mt2 * t * px p1 +
          3 * mt * t2 * px p2 + t3 * px p3
      y = mt3 * py p0 + 3 * mt2 * t * py p1 +
          3 * mt * t2 * py p2 + t3 * py p3
  in Point2D x y

-- | Evaluate cubic Bezier at t using 4 separate points
cubicBezierPoint :: Point2D -> Point2D -> Point2D -> Point2D -> Double -> Point2D
cubicBezierPoint p0 p1 p2 p3 t = evalPoint (CubicBezier p0 p1 p2 p3) t

--------------------------------------------------------------------------------
-- Derivative (Tangent)
--------------------------------------------------------------------------------

-- | Evaluate first derivative (tangent) of cubic Bezier at t.
-- B'(t) = 3(1-t)²(P₁-P₀) + 6(1-t)t(P₂-P₁) + 3t²(P₃-P₂)
evalDerivative :: CubicBezier -> Double -> Point2D
evalDerivative (CubicBezier p0 p1 p2 p3) t =
  let mt = 1 - t
      mt2 = mt * mt
      t2 = t * t

      dx = 3 * mt2 * (px p1 - px p0) +
           6 * mt * t * (px p2 - px p1) +
           3 * t2 * (px p3 - px p2)
      dy = 3 * mt2 * (py p1 - py p0) +
           6 * mt * t * (py p2 - py p1) +
           3 * t2 * (py p3 - py p2)
  in Point2D dx dy

-- | Get normalized tangent at t
evalTangent :: CubicBezier -> Double -> Point2D
evalTangent curve t = normalize (evalDerivative curve t)

-- | Get normal (perpendicular to tangent) at t
evalNormal :: CubicBezier -> Double -> Point2D
evalNormal curve t = perpendicular (evalTangent curve t)

--------------------------------------------------------------------------------
-- De Casteljau Subdivision
--------------------------------------------------------------------------------

-- | Split a cubic Bezier at t using de Casteljau's algorithm.
-- Returns (leftCurve, rightCurve) where:
-- - leftCurve covers [0, t]
-- - rightCurve covers [t, 1]
split :: CubicBezier -> Double -> (CubicBezier, CubicBezier)
split (CubicBezier p0 p1 p2 p3) t =
  -- First level
  let q0 = lerp p0 p1 t
      q1 = lerp p1 p2 t
      q2 = lerp p2 p3 t

      -- Second level
      r0 = lerp q0 q1 t
      r1 = lerp q1 q2 t

      -- Split point
      s = lerp r0 r1 t

      left = CubicBezier p0 q0 r0 s
      right = CubicBezier s r1 q2 p3
  in (left, right)

-- | Split using 4 separate points, return as vectors of 4 points each
splitCubicBezier :: Point2D -> Point2D -> Point2D -> Point2D -> Double
                 -> (Vector Point2D, Vector Point2D)
splitCubicBezier p0 p1 p2 p3 t =
  let (CubicBezier l0 l1 l2 l3, CubicBezier r0 r1 r2 r3) =
        split (CubicBezier p0 p1 p2 p3) t
  in (V.fromList [l0, l1, l2, l3], V.fromList [r0, r1, r2, r3])

--------------------------------------------------------------------------------
-- Arc Length
--------------------------------------------------------------------------------

-- | Approximate arc length using subdivision.
-- subdivisions: number of linear segments to use
arcLength :: CubicBezier -> Int -> Double
arcLength curve subdivisions =
  let n = max 1 subdivisions
      accumulate i prev accLen
        | i > n = accLen
        | otherwise =
            let t = fromIntegral i / fromIntegral n
                curr = evalPoint curve t
                segLen = distance prev curr
            in accumulate (i + 1) curr (accLen + segLen)
  in accumulate 1 (evalPoint curve 0) 0

-- | Arc length using 4 separate points
cubicBezierLength :: Point2D -> Point2D -> Point2D -> Point2D -> Int -> Double
cubicBezierLength p0 p1 p2 p3 subdivisions =
  arcLength (CubicBezier p0 p1 p2 p3) subdivisions

--------------------------------------------------------------------------------
-- Point at Arc Length
--------------------------------------------------------------------------------

-- | Find parameter t corresponding to a given arc length distance.
-- Uses binary search to find t where arcLength(0, t) ≈ targetDistance.
parameterAtArcLength :: CubicBezier -> Double -> Double -> Double -> Double
parameterAtArcLength curve targetDistance totalLength tolerance =
  let total = if totalLength > 0 then totalLength else arcLength curve 32
  in if total < tolerance then 0
     else if targetDistance <= 0 then 0
     else if targetDistance >= total then 1
     else
       -- Binary search for t
       let search lo hi fuel
             | fuel <= 0 = (lo + hi) / 2
             | hi - lo < tolerance = (lo + hi) / 2
             | otherwise =
                 let mid = (lo + hi) / 2
                     (left, _) = split curve mid
                     leftLen = arcLength left 16
                 in if leftLen < targetDistance
                    then search mid hi (fuel - 1)
                    else search lo mid (fuel - 1)
       in search 0 1 (50 :: Int)

--------------------------------------------------------------------------------
-- Bounding Box
--------------------------------------------------------------------------------

-- | Calculate tight bounding box of cubic Bezier.
-- Finds extrema by solving B'(t) = 0 for x and y components.
boundingBox :: CubicBezier -> BoundingBox
boundingBox (CubicBezier p0 p1 p2 p3) =
  -- Start with endpoints
  let minX0 = min (px p0) (px p3)
      maxX0 = max (px p0) (px p3)
      minY0 = min (py p0) (py p3)
      maxY0 = max (py p0) (py p3)

      -- Coefficients for x: B'(t) = ax*t^2 + bx*t + cx (rearranged for roots)
      ax = 3 * (-px p0 + 3 * px p1 - 3 * px p2 + px p3)
      bx = 6 * (px p0 - 2 * px p1 + px p2)
      cx = 3 * (px p1 - px p0)

      ay = 3 * (-py p0 + 3 * py p1 - 3 * py p2 + py p3)
      by = 6 * (py p0 - 2 * py p1 + py p2)
      cy = 3 * (py p1 - py p0)

      -- Solve quadratic at² + bt + c = 0
      solveQuadratic a b c
        | abs a < 0.0001 =
            if abs b < 0.0001 then []
            else let t = -c / b
                 in if t > 0 && t < 1 then [t] else []
        | otherwise =
            let disc = b * b - 4 * a * c
            in if disc < 0 then []
               else let sqrtDisc = sqrt disc
                        t1 = (-b + sqrtDisc) / (2 * a)
                        t2 = (-b - sqrtDisc) / (2 * a)
                        valid t = t > 0 && t < 1
                    in filter valid (if t1 == t2 then [t1] else [t1, t2])

      xRoots = solveQuadratic ax bx cx
      yRoots = solveQuadratic ay by cy

      updateBounds (mn, mx) t =
        let pt = evalPoint (CubicBezier p0 p1 p2 p3) t
        in (min mn (px pt), max mx (px pt))

      updateBoundsY (mn, mx) t =
        let pt = evalPoint (CubicBezier p0 p1 p2 p3) t
        in (min mn (py pt), max mx (py pt))

      (minX, maxX) = foldl updateBounds (minX0, maxX0) xRoots
      (minY, maxY) = foldl updateBoundsY (minY0, maxY0) yRoots

  in BoundingBox minX minY maxX maxY

--------------------------------------------------------------------------------
-- Flatten
--------------------------------------------------------------------------------

-- | Convert Bezier curve to polyline with specified number of segments
flatten :: CubicBezier -> Int -> Vector Point2D
flatten curve segments =
  let n = max 2 segments
  in V.generate (n + 1) $ \i ->
       let t = fromIntegral i / fromIntegral n
       in evalPoint curve t

--------------------------------------------------------------------------------
-- Curvature
--------------------------------------------------------------------------------

-- | Calculate curvature at parameter t.
-- κ = |B'(t) × B''(t)| / |B'(t)|³
-- Returns 0 if velocity is near zero.
curvature :: CubicBezier -> Double -> Double
curvature curve@(CubicBezier p0 p1 p2 p3) t =
  let d1 = evalDerivative curve t
      speed = len d1
  in if speed < 0.0001 then 0
     else
       -- Second derivative
       let mt = 1 - t
           d2x = 6 * mt * (px p2 - 2 * px p1 + px p0) +
                 6 * t * (px p3 - 2 * px p2 + px p1)
           d2y = 6 * mt * (py p2 - 2 * py p1 + py p0) +
                 6 * t * (py p3 - 2 * py p2 + py p1)
           crossMag = abs (px d1 * d2y - py d1 * d2x)
       in crossMag / (speed * speed * speed)
