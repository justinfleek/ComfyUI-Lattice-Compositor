-- | Lattice.Services.Path.BezierCore - Core Bezier Curve Math
-- |
-- | Pure mathematical functions for Bezier curve operations:
-- | - Point and vertex operations
-- | - Cubic Bezier evaluation
-- | - de Casteljau subdivision algorithm
-- | - Arc length estimation
-- |
-- | Source: ui/src/services/pathMorphing.ts

module Lattice.Services.Path.BezierCore
  ( -- * Types
    Point2D, BezierVertex, BezierPath, BezierSegment
    -- * Point Operations
  , zeroPoint, clonePoint, addPoints, subPoints, scalePoint, pointDistance
  , lerp, lerpPoint
    -- * Vertex Operations
  , cloneVertex, inHandleAbsolute, outHandleAbsolute, lerpVertex
    -- * Cubic Bezier
  , cubicBezierPoint, cubicBezierDerivative, splitCubicBezier
    -- * Arc Length
  , estimateSegmentLength, getSegmentControlPoints, getPathLength, getSegmentLengths
  ) where

import Prelude
import Data.Array (length, index, (!!))
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Math (sqrt) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D point
type Point2D =
  { x :: Number
  , y :: Number
  }

-- | Bezier vertex with point and control handles
type BezierVertex =
  { point :: Point2D
  , inHandle :: Point2D   -- Relative to point
  , outHandle :: Point2D  -- Relative to point
  }

-- | Bezier path (open or closed)
type BezierPath =
  { vertices :: Array BezierVertex
  , closed :: Boolean
  }

-- | Segment of a cubic Bezier (4 control points)
type BezierSegment =
  { p0 :: Point2D
  , p1 :: Point2D
  , p2 :: Point2D
  , p3 :: Point2D
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Point Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Create zero point
zeroPoint :: Point2D
zeroPoint = { x: 0.0, y: 0.0 }

-- | Clone a point
clonePoint :: Point2D -> Point2D
clonePoint p = { x: p.x, y: p.y }

-- | Add two points
addPoints :: Point2D -> Point2D -> Point2D
addPoints a b = { x: a.x + b.x, y: a.y + b.y }

-- | Subtract two points
subPoints :: Point2D -> Point2D -> Point2D
subPoints a b = { x: a.x - b.x, y: a.y - b.y }

-- | Scale a point
scalePoint :: Point2D -> Number -> Point2D
scalePoint p s = { x: p.x * s, y: p.y * s }

-- | Distance between two points
pointDistance :: Point2D -> Point2D -> Number
pointDistance a b =
  let dx = b.x - a.x
      dy = b.y - a.y
  in Math.sqrt (dx * dx + dy * dy)

-- | Linear interpolation between two numbers
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Linear interpolation between two points
lerpPoint :: Point2D -> Point2D -> Number -> Point2D
lerpPoint a b t = { x: lerp a.x b.x t, y: lerp a.y b.y t }

-- ────────────────────────────────────────────────────────────────────────────
-- Vertex Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Clone a vertex
cloneVertex :: BezierVertex -> BezierVertex
cloneVertex v =
  { point: clonePoint v.point
  , inHandle: clonePoint v.inHandle
  , outHandle: clonePoint v.outHandle
  }

-- | Get absolute position of in-handle
inHandleAbsolute :: BezierVertex -> Point2D
inHandleAbsolute v = addPoints v.point v.inHandle

-- | Get absolute position of out-handle
outHandleAbsolute :: BezierVertex -> Point2D
outHandleAbsolute v = addPoints v.point v.outHandle

-- | Interpolate between two vertices
lerpVertex :: BezierVertex -> BezierVertex -> Number -> BezierVertex
lerpVertex v1 v2 t =
  { point: lerpPoint v1.point v2.point t
  , inHandle: lerpPoint v1.inHandle v2.inHandle t
  , outHandle: lerpPoint v1.outHandle v2.outHandle t
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Cubic Bezier Evaluation
-- ────────────────────────────────────────────────────────────────────────────

-- | Evaluate a cubic Bezier curve at parameter t.
-- |
-- | Uses the standard cubic Bezier formula:
-- | B(t) = (1-t)³P₀ + 3(1-t)²tP₁ + 3(1-t)t²P₂ + t³P₃
cubicBezierPoint :: Point2D -> Point2D -> Point2D -> Point2D -> Number -> Point2D
cubicBezierPoint p0 p1 p2 p3 t =
  let mt = 1.0 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
      t2 = t * t
      t3 = t2 * t
      x = mt3 * p0.x + 3.0 * mt2 * t * p1.x + 3.0 * mt * t2 * p2.x + t3 * p3.x
      y = mt3 * p0.y + 3.0 * mt2 * t * p1.y + 3.0 * mt * t2 * p2.y + t3 * p3.y
  in { x, y }

-- | Cubic Bezier derivative at parameter t.
-- |
-- | Returns tangent vector (not normalized).
cubicBezierDerivative :: Point2D -> Point2D -> Point2D -> Point2D -> Number -> Point2D
cubicBezierDerivative p0 p1 p2 p3 t =
  let mt = 1.0 - t
      mt2 = mt * mt
      t2 = t * t
      d01 = subPoints p1 p0
      d12 = subPoints p2 p1
      d23 = subPoints p3 p2
      x = 3.0 * mt2 * d01.x + 6.0 * mt * t * d12.x + 3.0 * t2 * d23.x
      y = 3.0 * mt2 * d01.y + 6.0 * mt * t * d12.y + 3.0 * t2 * d23.y
  in { x, y }

-- | Split a cubic Bezier at parameter t using de Casteljau's algorithm.
-- |
-- | Returns { left, right } where:
-- | - left covers [0, t]
-- | - right covers [t, 1]
splitCubicBezier :: Point2D -> Point2D -> Point2D -> Point2D -> Number
                -> { left :: BezierSegment, right :: BezierSegment }
splitCubicBezier p0 p1 p2 p3 t =
  let q0 = lerpPoint p0 p1 t
      q1 = lerpPoint p1 p2 t
      q2 = lerpPoint p2 p3 t
      r0 = lerpPoint q0 q1 t
      r1 = lerpPoint q1 q2 t
      s = lerpPoint r0 r1 t
      left = { p0: p0, p1: q0, p2: r0, p3: s }
      right = { p0: s, p1: r1, p2: q2, p3: p3 }
  in { left, right }

-- ────────────────────────────────────────────────────────────────────────────
-- Arc Length Estimation
-- ────────────────────────────────────────────────────────────────────────────

-- | Estimate arc length of a cubic Bezier segment using chord approximation.
estimateSegmentLength :: Point2D -> Point2D -> Point2D -> Point2D -> Int -> Number
estimateSegmentLength p0 p1 p2 p3 samples
  | samples <= 0 = 0.0
  | otherwise = go 1 p0 0.0
  where
    go i prev acc
      | i > samples = acc
      | otherwise =
          let t = Int.toNumber i / Int.toNumber samples
              curr = cubicBezierPoint p0 p1 p2 p3 t
              dist = pointDistance prev curr
          in go (i + 1) curr (acc + dist)

-- | Get segment control points from a path.
getSegmentControlPoints :: BezierPath -> Int
                       -> Maybe { p0 :: Point2D, p1 :: Point2D, p2 :: Point2D, p3 :: Point2D }
getSegmentControlPoints path segmentIndex
  | length path.vertices == 0 = Nothing
  | segmentIndex < 0 || segmentIndex >= length path.vertices = Nothing
  | otherwise = do
      v0 <- path.vertices !! segmentIndex
      let n = length path.vertices
          nextIdx = (segmentIndex + 1) `mod` n
      v1 <- path.vertices !! nextIdx
      let p0 = v0.point
          p1 = outHandleAbsolute v0
          p2 = inHandleAbsolute v1
          p3 = v1.point
      pure { p0, p1, p2, p3 }

-- | Calculate total arc length of a path.
getPathLength :: BezierPath -> Int -> Number
getPathLength path samplesPerSegment
  | length path.vertices == 0 = 0.0
  | otherwise = go 0 0.0
  where
    numSegments = if path.closed
                  then length path.vertices
                  else length path.vertices - 1
    go i acc
      | i >= numSegments = acc
      | otherwise = case getSegmentControlPoints path i of
          Just pts ->
            let len = estimateSegmentLength pts.p0 pts.p1 pts.p2 pts.p3 samplesPerSegment
            in go (i + 1) (acc + len)
          Nothing -> acc

-- | Calculate arc lengths of each segment.
getSegmentLengths :: BezierPath -> Int -> Array Number
getSegmentLengths path samplesPerSegment
  | length path.vertices == 0 = []
  | otherwise = go 0 []
  where
    numSegments = if path.closed
                  then length path.vertices
                  else length path.vertices - 1
    go i acc
      | i >= numSegments = acc
      | otherwise = case getSegmentControlPoints path i of
          Just pts ->
            let len = estimateSegmentLength pts.p0 pts.p1 pts.p2 pts.p3 samplesPerSegment
            in go (i + 1) (acc <> [len])
          Nothing -> go (i + 1) acc
