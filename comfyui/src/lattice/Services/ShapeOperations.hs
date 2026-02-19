-- |
-- Module      : Lattice.Services.ShapeOperations
-- Description : Pure 2D shape operations for bezier paths
-- 
-- Migrated from ui/src/services/shapeOperations.ts
-- Unique 2D vector operations not already in PathMorphing
-- Note: Many functions duplicate PathMorphing - only unique ones migrated here
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.ShapeOperations
  ( -- 2D Vector operations
    normalize2D
  , perpendicular2D
  , dot2D
  , cross2D
  , rotatePoint2D
  , rotateAround2D
  -- Bezier operations
  , cubicBezierDerivative2D
  , cubicBezierLength2D
  ) where

import Lattice.Types.LayerDataShapes (Point2D(..))
import Lattice.Utils.NumericSafety
  ( ensureFinite
  , safeSqrt
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 2D VECTOR OPERATIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Normalize a Point2D vector to unit length
-- Returns zero vector if length is too small
normalize2D :: Point2D -> Point2D
normalize2D (Point2D x y) =
  let len = safeSqrt (x * x + y * y)
  in if len < 0.0001
     then Point2D 0.0 0.0
     else Point2D (x / len) (y / len)

-- | Get perpendicular vector (rotate 90 degrees counterclockwise)
perpendicular2D :: Point2D -> Point2D
perpendicular2D (Point2D x y) = Point2D (-y) x

-- | Dot product of two Point2D vectors
dot2D :: Point2D -> Point2D -> Double
dot2D (Point2D x1 y1) (Point2D x2 y2) =
  ensureFinite (x1 * x2 + y1 * y2) 0.0

-- | Cross product of two Point2D vectors (returns scalar)
cross2D :: Point2D -> Point2D -> Double
cross2D (Point2D x1 y1) (Point2D x2 y2) =
  ensureFinite (x1 * y2 - y1 * x2) 0.0

-- | Rotate point around origin
rotatePoint2D :: Point2D -> Double -> Point2D
rotatePoint2D (Point2D x y) angle =
  let cosAngle = cos angle
      sinAngle = sin angle
      newX = x * cosAngle - y * sinAngle
      newY = x * sinAngle + y * cosAngle
  in Point2D (ensureFinite newX 0.0) (ensureFinite newY 0.0)

-- | Rotate point around center
rotateAround2D :: Point2D -> Point2D -> Double -> Point2D
rotateAround2D point center angle =
  let Point2D px py = point
      Point2D cx cy = center
      -- Translate to origin
      translated = Point2D (px - cx) (py - cy)
      -- Rotate
      rotated = rotatePoint2D translated angle
      -- Translate back
      Point2D rx ry = rotated
  in Point2D (rx + cx) (ry + cy)

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // bezier // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Evaluate cubic bezier derivative at t (tangent direction)
cubicBezierDerivative2D ::
  Point2D -> Point2D -> Point2D -> Point2D -> Double -> Point2D
cubicBezierDerivative2D p0 p1 p2 p3 t =
  let mt = 1 - t
      mt2 = mt * mt
      t2 = t * t
      Point2D x0 y0 = p0
      Point2D x1 y1 = p1
      Point2D x2 y2 = p2
      Point2D x3 y3 = p3
      dx = 3 * mt2 * (x1 - x0) + 6 * mt * t * (x2 - x1) + 3 * t2 * (x3 - x2)
      dy = 3 * mt2 * (y1 - y0) + 6 * mt * t * (y2 - y1) + 3 * t2 * (y3 - y2)
  in Point2D (ensureFinite dx 0.0) (ensureFinite dy 0.0)

-- | Approximate arc length of cubic bezier using adaptive subdivision
cubicBezierLength2D ::
  Point2D -> Point2D -> Point2D -> Point2D -> Int -> Double
cubicBezierLength2D p0 p1 p2 p3 subdivisions =
  let subdivisionsD = fromIntegral subdivisions
      -- Helper to evaluate bezier at t
      bezierAt t =
        let mt = 1 - t
            mt2 = mt * mt
            mt3 = mt2 * mt
            t2 = t * t
            t3 = t2 * t
            Point2D x0 y0 = p0
            Point2D x1 y1 = p1
            Point2D x2 y2 = p2
            Point2D x3 y3 = p3
            x = mt3 * x0 + 3 * mt2 * t * x1 + 3 * mt * t2 * x2 + t3 * x3
            y = mt3 * y0 + 3 * mt2 * t * y1 + 3 * mt * t2 * y2 + t3 * y3
        in Point2D (ensureFinite x 0.0) (ensureFinite y 0.0)
      -- Helper to calculate distance
      pointDistance (Point2D x1 y1) (Point2D x2 y2) =
        let dx = x2 - x1
            dy = y2 - y1
        in safeSqrt (dx * dx + dy * dy)
      -- Calculate length by sampling
      go i prev acc
        | i > subdivisions = acc
        | otherwise =
            let t = fromIntegral i / subdivisionsD
                curr = bezierAt t
                dist = pointDistance prev curr
            in go (i + 1) curr (acc + dist)
  in go 1 p0 0.0
