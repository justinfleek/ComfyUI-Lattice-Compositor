{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Path.BezierCore
Description : Core Bezier Curve Math
Copyright   : (c) Lattice, 2026
License     : MIT

Pure mathematical functions for Bezier curve operations:
- Point and vertex operations
- Cubic Bezier evaluation
- de Casteljau subdivision algorithm
- Arc length estimation

Source: ui/src/services/pathMorphing.ts
-}

module Lattice.Services.Path.BezierCore
  ( -- * Types
    Point2D(..), BezierVertex(..), BezierPath(..), BezierSegment(..)
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

import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D point
data Point2D = Point2D
  { px :: Double
  , py :: Double
  } deriving (Eq, Show)

-- | Bezier vertex with point and control handles
data BezierVertex = BezierVertex
  { bvPoint :: Point2D
  , bvInHandle :: Point2D   -- Relative to point
  , bvOutHandle :: Point2D  -- Relative to point
  } deriving (Eq, Show)

-- | Bezier path (open or closed)
data BezierPath = BezierPath
  { bpVertices :: Vector BezierVertex
  , bpClosed :: Bool
  } deriving (Eq, Show)

-- | Segment of a cubic Bezier (4 control points)
data BezierSegment = BezierSegment
  { bsP0 :: Point2D
  , bsP1 :: Point2D
  , bsP2 :: Point2D
  , bsP3 :: Point2D
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Point Operations
--------------------------------------------------------------------------------

-- | Create zero point
zeroPoint :: Point2D
zeroPoint = Point2D 0 0

-- | Clone a point
clonePoint :: Point2D -> Point2D
clonePoint (Point2D x y) = Point2D x y

-- | Add two points
addPoints :: Point2D -> Point2D -> Point2D
addPoints (Point2D x1 y1) (Point2D x2 y2) = Point2D (x1 + x2) (y1 + y2)

-- | Subtract two points
subPoints :: Point2D -> Point2D -> Point2D
subPoints (Point2D x1 y1) (Point2D x2 y2) = Point2D (x1 - x2) (y1 - y2)

-- | Scale a point
scalePoint :: Point2D -> Double -> Point2D
scalePoint (Point2D x y) s = Point2D (x * s) (y * s)

-- | Distance between two points
pointDistance :: Point2D -> Point2D -> Double
pointDistance (Point2D x1 y1) (Point2D x2 y2) =
  let dx = x2 - x1
      dy = y2 - y1
  in sqrt (dx * dx + dy * dy)

-- | Linear interpolation between two numbers
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * t

-- | Linear interpolation between two points
lerpPoint :: Point2D -> Point2D -> Double -> Point2D
lerpPoint (Point2D x1 y1) (Point2D x2 y2) t =
  Point2D (lerp x1 x2 t) (lerp y1 y2 t)

--------------------------------------------------------------------------------
-- Vertex Operations
--------------------------------------------------------------------------------

-- | Clone a vertex
cloneVertex :: BezierVertex -> BezierVertex
cloneVertex (BezierVertex p i o) =
  BezierVertex (clonePoint p) (clonePoint i) (clonePoint o)

-- | Get absolute position of in-handle
inHandleAbsolute :: BezierVertex -> Point2D
inHandleAbsolute v = addPoints (bvPoint v) (bvInHandle v)

-- | Get absolute position of out-handle
outHandleAbsolute :: BezierVertex -> Point2D
outHandleAbsolute v = addPoints (bvPoint v) (bvOutHandle v)

-- | Interpolate between two vertices
lerpVertex :: BezierVertex -> BezierVertex -> Double -> BezierVertex
lerpVertex v1 v2 t = BezierVertex
  { bvPoint = lerpPoint (bvPoint v1) (bvPoint v2) t
  , bvInHandle = lerpPoint (bvInHandle v1) (bvInHandle v2) t
  , bvOutHandle = lerpPoint (bvOutHandle v1) (bvOutHandle v2) t
  }

--------------------------------------------------------------------------------
-- Cubic Bezier Evaluation
--------------------------------------------------------------------------------

-- | Evaluate a cubic Bezier curve at parameter t.
--
--   Uses the standard cubic Bezier formula:
--   B(t) = (1-t)³P₀ + 3(1-t)²tP₁ + 3(1-t)t²P₂ + t³P₃
cubicBezierPoint :: Point2D -> Point2D -> Point2D -> Point2D -> Double -> Point2D
cubicBezierPoint p0 p1 p2 p3 t =
  let mt = 1 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
      t2 = t * t
      t3 = t2 * t
      x = mt3 * px p0 + 3 * mt2 * t * px p1 + 3 * mt * t2 * px p2 + t3 * px p3
      y = mt3 * py p0 + 3 * mt2 * t * py p1 + 3 * mt * t2 * py p2 + t3 * py p3
  in Point2D x y

-- | Cubic Bezier derivative at parameter t.
--
--   Returns tangent vector (not normalized).
cubicBezierDerivative :: Point2D -> Point2D -> Point2D -> Point2D -> Double -> Point2D
cubicBezierDerivative p0 p1 p2 p3 t =
  let mt = 1 - t
      mt2 = mt * mt
      t2 = t * t
      d01 = subPoints p1 p0
      d12 = subPoints p2 p1
      d23 = subPoints p3 p2
      x = 3 * mt2 * px d01 + 6 * mt * t * px d12 + 3 * t2 * px d23
      y = 3 * mt2 * py d01 + 6 * mt * t * py d12 + 3 * t2 * py d23
  in Point2D x y

-- | Split a cubic Bezier at parameter t using de Casteljau's algorithm.
--
--   Returns (leftSegment, rightSegment) where:
--   - leftSegment covers [0, t]
--   - rightSegment covers [t, 1]
splitCubicBezier :: Point2D -> Point2D -> Point2D -> Point2D -> Double
                -> (BezierSegment, BezierSegment)
splitCubicBezier p0 p1 p2 p3 t =
  let q0 = lerpPoint p0 p1 t
      q1 = lerpPoint p1 p2 t
      q2 = lerpPoint p2 p3 t
      r0 = lerpPoint q0 q1 t
      r1 = lerpPoint q1 q2 t
      s = lerpPoint r0 r1 t
      left = BezierSegment p0 q0 r0 s
      right = BezierSegment s r1 q2 p3
  in (left, right)

--------------------------------------------------------------------------------
-- Arc Length Estimation
--------------------------------------------------------------------------------

-- | Estimate arc length of a cubic Bezier segment using chord approximation.
estimateSegmentLength :: Point2D -> Point2D -> Point2D -> Point2D -> Int -> Double
estimateSegmentLength p0 p1 p2 p3 samples
  | samples <= 0 = 0
  | otherwise = go 1 p0 0
  where
    go i prev acc
      | i > samples = acc
      | otherwise =
          let t = fromIntegral i / fromIntegral samples
              curr = cubicBezierPoint p0 p1 p2 p3 t
              dist = pointDistance prev curr
          in go (i + 1) curr (acc + dist)

-- | Get segment control points from a path.
getSegmentControlPoints :: BezierPath -> Int -> Maybe (Point2D, Point2D, Point2D, Point2D)
getSegmentControlPoints path segmentIndex
  | V.null (bpVertices path) = Nothing
  | segmentIndex < 0 || segmentIndex >= V.length (bpVertices path) = Nothing
  | otherwise =
      let n = V.length (bpVertices path)
          v0 = bpVertices path V.! segmentIndex
          nextIdx = (segmentIndex + 1) `mod` n
          v1 = bpVertices path V.! nextIdx
          p0 = bvPoint v0
          p1 = outHandleAbsolute v0
          p2 = inHandleAbsolute v1
          p3 = bvPoint v1
      in Just (p0, p1, p2, p3)

-- | Calculate total arc length of a path.
getPathLength :: BezierPath -> Int -> Double
getPathLength path samplesPerSegment
  | V.null (bpVertices path) = 0
  | otherwise = go 0 0
  where
    numSegments = if bpClosed path
                  then V.length (bpVertices path)
                  else V.length (bpVertices path) - 1
    go i acc
      | i >= numSegments = acc
      | otherwise = case getSegmentControlPoints path i of
          Just (p0, p1, p2, p3) ->
            let len = estimateSegmentLength p0 p1 p2 p3 samplesPerSegment
            in go (i + 1) (acc + len)
          Nothing -> acc

-- | Calculate arc lengths of each segment.
getSegmentLengths :: BezierPath -> Int -> Vector Double
getSegmentLengths path samplesPerSegment
  | V.null (bpVertices path) = V.empty
  | otherwise = V.generate numSegments segmentLength
  where
    numSegments = if bpClosed path
                  then V.length (bpVertices path)
                  else V.length (bpVertices path) - 1
    segmentLength i = case getSegmentControlPoints path i of
      Just (p0, p1, p2, p3) -> estimateSegmentLength p0 p1 p2 p3 samplesPerSegment
      Nothing -> 0
