-- |
-- Module      : Lattice.Services.PathMorphing
-- Description : Pure path morphing functions for bezier path interpolation
-- 
-- Migrated from ui/src/services/pathMorphing.ts
-- Pure geometric operations for path morphing
-- Note: Logger calls removed, errors returned via Either
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.PathMorphing
  ( -- Utility functions
    clonePoint
  , cloneVertex
  , clonePath
  , pointDistance
  , pointLerp
  , pointLerpNumber
  , addPoints
  , subtractPoints
  , scalePoint
  -- Cubic bezier operations
  , cubicBezierPoint
  , splitCubicBezier
  , estimateSegmentLength
  -- Path analysis
  , getSegmentControlPoints
  , getPathLength
  , getSegmentLengths
  , getPointAtArcLength
  -- Subdivision
  , subdivideSegmentAt
  , subdivideToVertexCount
  , resamplePath
  -- Correspondence
  , calculateTravelDistance
  , findOptimalRotation
  , rotateVertices
  -- Main API
  , prepareMorphPaths
  , morphPaths
  , morphPathsAuto
  , getCorrespondence
  -- Types
  , MorphConfig(..)
  , PointMatchingStrategy(..)
  , CorrespondenceMethod(..)
  , PreparedMorphPaths(..)
  , ArcLengthResult(..)
  ) where

import Data.List (findIndex)
import Lattice.Types.LayerDataShapes
  ( BezierPath(..)
  , BezierVertex(..)
  , Point2D(..)
  )
import Lattice.Utils.NumericSafety
  ( ensureFinite
  , safeSqrt
  , clamp01
  )
import qualified Data.Text as T

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Strategy for matching point counts
data PointMatchingStrategy
  = PointMatchingSubdivideShorter
  | PointMatchingSubdivideBoth
  | PointMatchingResample
  deriving (Eq, Show)

-- | Method for finding optimal vertex correspondence
data CorrespondenceMethod
  = CorrespondenceIndex
  | CorrespondenceNearestRotation
  | CorrespondenceNearestDistance
  | CorrespondenceManual
  deriving (Eq, Show)

-- | Configuration for path morphing preparation
data MorphConfig = MorphConfig
  { morphConfigPointMatchingStrategy :: PointMatchingStrategy
  , morphConfigCorrespondenceMethod :: CorrespondenceMethod
  , morphConfigManualMapping :: Maybe [Int]
  , morphConfigResampleCount :: Maybe Int
  }
  deriving (Eq, Show)

-- | Result of preparing two paths for morphing
data PreparedMorphPaths = PreparedMorphPaths
  { preparedMorphPathsSource :: BezierPath
  , preparedMorphPathsTarget :: BezierPath
  , preparedMorphPathsRotationOffset :: Int
  , preparedMorphPathsReversed :: Bool
  }
  deriving (Eq, Show)

-- | Result of getting point at arc length
data ArcLengthResult = ArcLengthResult
  { arcLengthResultPoint :: Point2D
  , arcLengthResultSegmentIndex :: Int
  , arcLengthResultT :: Double
  }
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // utility // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Clone a point
clonePoint :: Point2D -> Point2D
clonePoint (Point2D x y) = Point2D x y

-- | Clone a vertex
cloneVertex :: BezierVertex -> BezierVertex
cloneVertex (BezierVertex point inHandle outHandle) =
  BezierVertex (clonePoint point) (clonePoint inHandle) (clonePoint outHandle)

-- | Clone a path
clonePath :: BezierPath -> BezierPath
clonePath (BezierPath vertices closed) =
  BezierPath (map cloneVertex vertices) closed

-- | Calculate distance between two points
pointDistance :: Point2D -> Point2D -> Double
pointDistance (Point2D x1 y1) (Point2D x2 y2) =
  let dx = x2 - x1
      dy = y2 - y1
  in safeSqrt (dx * dx + dy * dy)

-- | Linear interpolation between two numbers
pointLerpNumber :: Double -> Double -> Double -> Double
pointLerpNumber a b t = a + (b - a) * t

-- | Linear interpolation between two points
pointLerp :: Point2D -> Point2D -> Double -> Point2D
pointLerp (Point2D x1 y1) (Point2D x2 y2) t =
  Point2D (pointLerpNumber x1 x2 t) (pointLerpNumber y1 y2 t)

-- | Add two points
addPoints :: Point2D -> Point2D -> Point2D
addPoints (Point2D x1 y1) (Point2D x2 y2) =
  Point2D (x1 + x2) (y1 + y2)

-- | Subtract two points
subtractPoints :: Point2D -> Point2D -> Point2D
subtractPoints (Point2D x1 y1) (Point2D x2 y2) =
  Point2D (x1 - x2) (y1 - y2)

-- | Scale a point
scalePoint :: Point2D -> Double -> Point2D
scalePoint (Point2D x y) s =
  Point2D (x * s) (y * s)

-- ════════════════════════════════════════════════════════════════════════════
--                                             // cubic // bezier // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Evaluate a cubic bezier curve at parameter t
cubicBezierPoint :: Point2D -> Point2D -> Point2D -> Point2D -> Double -> Point2D
cubicBezierPoint p0 p1 p2 p3 t =
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

-- | Split a cubic bezier at parameter t using de Casteljau's algorithm
splitCubicBezier ::
  Point2D -> Point2D -> Point2D -> Point2D -> Double ->
  ([Point2D], [Point2D])
splitCubicBezier p0 p1 p2 p3 t =
  let q0 = pointLerp p0 p1 t
      q1 = pointLerp p1 p2 t
      q2 = pointLerp p2 p3 t
      r0 = pointLerp q0 q1 t
      r1 = pointLerp q1 q2 t
      s = pointLerp r0 r1 t
      left = [p0, q0, r0, s]
      right = [s, r1, q2, p3]
  in (left, right)

-- | Estimate arc length of a cubic bezier segment using chord approximation
estimateSegmentLength ::
  Point2D -> Point2D -> Point2D -> Point2D -> Int -> Double
estimateSegmentLength p0 p1 p2 p3 samples =
  let samplesD = fromIntegral samples
      go i prev acc
        | i > samples = acc
        | otherwise =
            let t = fromIntegral i / samplesD
                curr = cubicBezierPoint p0 p1 p2 p3 t
                dist = pointDistance prev curr
            in go (i + 1) curr (acc + dist)
  in go 1 p0 0.0

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // path // analysis
-- ════════════════════════════════════════════════════════════════════════════

-- | Get segment control points from a path
getSegmentControlPoints ::
  BezierPath -> Int -> Maybe (Point2D, Point2D, Point2D, Point2D)
getSegmentControlPoints (BezierPath vertices closed) segmentIndex =
  -- Use drop with pattern matching - type-safe access
  case drop segmentIndex vertices of
    [] -> Nothing
    (v0 : _) ->
      let nextIdx = if closed
                    then (segmentIndex + 1) `mod` length vertices
                    else segmentIndex + 1
      in case drop nextIdx vertices of
        [] -> Nothing
        (v1 : _) ->
          let p0 = bezierVertexPoint v0
              p1 = addPoints (bezierVertexPoint v0) (bezierVertexOutHandle v0)
              p2 = addPoints (bezierVertexPoint v1) (bezierVertexInHandle v1)
              p3 = bezierVertexPoint v1
          in Just (p0, p1, p2, p3)

-- | Calculate total arc length of a path
getPathLength :: BezierPath -> Int -> Double
getPathLength path samplesPerSegment =
  let numSegments = if bezierPathClosed path
                    then length (bezierPathVertices path)
                    else length (bezierPathVertices path) - 1
      go i acc
        | i >= numSegments = acc
        | otherwise =
            case getSegmentControlPoints path i of
              Nothing -> acc
              Just (p0, p1, p2, p3) ->
                let segLength = estimateSegmentLength p0 p1 p2 p3 samplesPerSegment
                in go (i + 1) (acc + segLength)
  in go 0 0.0

-- | Calculate arc lengths of each segment
getSegmentLengths :: BezierPath -> Int -> [Double]
getSegmentLengths path samplesPerSegment =
  let numSegments = if bezierPathClosed path
                    then length (bezierPathVertices path)
                    else length (bezierPathVertices path) - 1
      go i
        | i >= numSegments = []
        | otherwise =
            case getSegmentControlPoints path i of
              Nothing -> []
              Just (p0, p1, p2, p3) ->
                let segLength = estimateSegmentLength p0 p1 p2 p3 samplesPerSegment
                in segLength : go (i + 1)
  in go 0

-- | Get point at a specific arc length along the path
getPointAtArcLength ::
  BezierPath -> Double -> [Double] -> ArcLengthResult
getPointAtArcLength path targetLength segmentLengths =
  let go i accumulated
        | i >= length segmentLengths =
            -- Fallback: return last point
            let vertices = bezierPathVertices path
            in case drop (length vertices - 1) vertices of
              [] -> ArcLengthResult (Point2D 0.0 0.0) (length segmentLengths - 1) 1.0
              (lastVertex : _) ->
                ArcLengthResult (bezierVertexPoint lastVertex) (length segmentLengths - 1) 1.0
        | otherwise =
            case drop i segmentLengths of
              [] -> go (i + 1) accumulated
              (segmentLength : _) ->
                if accumulated + segmentLength >= targetLength || i == length segmentLengths - 1
                then
                  let localT = if segmentLength > 0
                               then (targetLength - accumulated) / segmentLength
                               else 0.0
                      clampedT = clamp01 localT
                  in case getSegmentControlPoints path i of
                    Nothing -> go (i + 1) (accumulated + segmentLength)
                    Just (p0, p1, p2, p3) ->
                      let point = cubicBezierPoint p0 p1 p2 p3 clampedT
                      in ArcLengthResult point i localT
                else go (i + 1) (accumulated + segmentLength)
  in go 0 0.0

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // subdivision
-- ════════════════════════════════════════════════════════════════════════════

-- | Subdivide a path segment at a specific t value
subdivideSegmentAt :: BezierPath -> Int -> Double -> Maybe BezierPath
subdivideSegmentAt path segmentIndex t =
  let (BezierPath vertices closed) = clonePath path
  in case drop segmentIndex vertices of
    [] -> Nothing
    (v0 : _) ->
      let nextIdx = if closed
                    then (segmentIndex + 1) `mod` length vertices
                    else segmentIndex + 1
      in case drop nextIdx vertices of
        [] -> Nothing
        (v1 : _) ->
          let p0 = bezierVertexPoint v0
              p1 = addPoints (bezierVertexPoint v0) (bezierVertexOutHandle v0)
              p2 = addPoints (bezierVertexPoint v1) (bezierVertexInHandle v1)
              p3 = bezierVertexPoint v1
              (left, right) = splitCubicBezier p0 p1 p2 p3 t
              -- Extract points from left and right segments
              leftP0 = case safeListGet left 0 of Just p -> p; Nothing -> p0
              leftP1 = case safeListGet left 1 of Just p -> p; Nothing -> p1
              leftP2 = case safeListGet left 2 of Just p -> p; Nothing -> p2
              leftP3 = case safeListGet left 3 of Just p -> p; Nothing -> p3
              rightP0 = case safeListGet right 0 of Just p -> p; Nothing -> p0
              rightP1 = case safeListGet right 1 of Just p -> p; Nothing -> p1
              rightP2 = case safeListGet right 2 of Just p -> p; Nothing -> p2
              rightP3 = case safeListGet right 3 of Just p -> p; Nothing -> p3
              -- Update v0's out handle
              newV0OutHandle = subtractPoints leftP1 leftP0
              -- Create new vertex at split point
              newVertex = BezierVertex
                (clonePoint leftP3)
                (subtractPoints leftP2 leftP3)
                (subtractPoints rightP1 rightP0)
              -- Update v1's in handle
              newV1InHandle = subtractPoints rightP2 rightP3
              -- Insert new vertex
              (before, after) = splitAt (segmentIndex + 1) vertices
              newV0 = BezierVertex
                (bezierVertexPoint v0)
                (bezierVertexInHandle v0)
                newV0OutHandle
              newV1 = BezierVertex
                (bezierVertexPoint v1)
                newV1InHandle
                (bezierVertexOutHandle v1)
              newVertices = take segmentIndex vertices ++ [newV0] ++ [newVertex] ++ [newV1] ++ drop (segmentIndex + 2) vertices
          in Just (BezierPath newVertices closed)

-- Helper to safely get list element
safeListGet :: [a] -> Int -> Maybe a
safeListGet [] _ = Nothing
safeListGet (x:xs) 0 = Just x
safeListGet (_:xs) n = safeListGet xs (n - 1)

-- | Subdivide a path to have a specific number of vertices
subdivideToVertexCount :: BezierPath -> Int -> BezierPath
subdivideToVertexCount path targetCount
  | length (bezierPathVertices path) >= targetCount = clonePath path
  | otherwise =
      let go current
            | length (bezierPathVertices current) >= targetCount = current
            | otherwise =
                let currentLengths = getSegmentLengths current 10
                    (maxIndex, _) = findMaxLength currentLengths 0 0 0.0
                in case subdivideSegmentAt current maxIndex 0.5 of
                  Nothing -> current
                  Just subdivided -> go subdivided
          findMaxLength [] _ bestIdx bestLen = (bestIdx, bestLen)
          findMaxLength (l:ls) idx bestIdx bestLen
            | l > bestLen = findMaxLength ls (idx + 1) idx l
            | otherwise = findMaxLength ls (idx + 1) bestIdx bestLen
      in go (clonePath path)

-- | Resample a path with evenly spaced vertices
resamplePath :: BezierPath -> Int -> BezierPath
resamplePath path vertexCount
  | vertexCount < 2 = clonePath path
  | otherwise =
      let segmentLengths = getSegmentLengths path 10
          totalLength = sum segmentLengths
          vertices = bezierPathVertices path
      in if totalLength == 0
         then
           -- Degenerate path - just clone vertices
           let go i
                 | i >= vertexCount = []
                 | otherwise =
                     let srcIdx = (i * length vertices) `div` vertexCount
                     in case drop srcIdx vertices of
                       [] -> []
                       (v : _) -> cloneVertex v : go (i + 1)
           in BezierPath (go 0) (bezierPathClosed path)
         else
           let spacing = totalLength / if bezierPathClosed path
                                      then fromIntegral vertexCount
                                      else fromIntegral (vertexCount - 1)
               go i
                 | i >= vertexCount = []
                 | otherwise =
                     let targetLength = fromIntegral i * spacing
                         result = getPointAtArcLength path targetLength segmentLengths
                         point = arcLengthResultPoint result
                         -- Calculate tangent for handles
                         prevLength = max 0.0 (targetLength - spacing * 0.33)
                         nextLength = min totalLength (targetLength + spacing * 0.33)
                         prevResult = getPointAtArcLength path prevLength segmentLengths
                         nextResult = getPointAtArcLength path nextLength segmentLengths
                         prevPoint = arcLengthResultPoint prevResult
                         nextPoint = arcLengthResultPoint nextResult
                         tangent = Point2D
                           ((point2DX nextPoint - point2DX prevPoint) * 0.5)
                           ((point2DY nextPoint - point2DY prevPoint) * 0.5)
                         handleScale = 0.33
                         newVertex = BezierVertex
                           (clonePoint point)
                           (scalePoint tangent (-handleScale))
                           (scalePoint tangent handleScale)
                     in newVertex : go (i + 1)
           in BezierPath (go 0) (bezierPathClosed path)

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // correspondence
-- ════════════════════════════════════════════════════════════════════════════

-- | Calculate total travel distance for a given rotation offset
calculateTravelDistance ::
  BezierPath -> BezierPath -> Int -> Bool -> Double
calculateTravelDistance source target rotationOffset reversed =
  let n = length (bezierPathVertices source)
      sourceVertices = bezierPathVertices source
      targetVertices = bezierPathVertices target
      go i acc
        | i >= n = acc
        | otherwise =
            let srcIdx = i
                tgtIdx = if reversed
                         then (n - 1 - i + rotationOffset + n) `mod` n
                         else (i + rotationOffset + n) `mod` n
                srcPoint = case drop srcIdx sourceVertices of
                  [] -> Point2D 0.0 0.0
                  (v : _) -> bezierVertexPoint v
                tgtPoint = case drop tgtIdx targetVertices of
                  [] -> Point2D 0.0 0.0
                  (v : _) -> bezierVertexPoint v
                dist = pointDistance srcPoint tgtPoint
            in go (i + 1) (acc + dist)
  in go 0 0.0

-- | Find optimal rotation offset to minimize travel distance
findOptimalRotation :: BezierPath -> BezierPath -> (Int, Bool)
findOptimalRotation source target =
  let n = length (bezierPathVertices source)
      go offset bestOffset bestReversed bestDist
        | offset >= n = (bestOffset, bestReversed)
        | otherwise =
            let dist = calculateTravelDistance source target offset False
                (newBestOffset, newBestReversed, newBestDist) =
                  if dist < bestDist
                  then (offset, False, dist)
                  else (bestOffset, bestReversed, bestDist)
                (finalOffset, finalReversed, finalDist) =
                  if bezierPathClosed source && bezierPathClosed target
                  then
                    let distRev = calculateTravelDistance source target offset True
                    in if distRev < newBestDist
                       then (offset, True, distRev)
                       else (newBestOffset, newBestReversed, newBestDist)
                  else (newBestOffset, newBestReversed, newBestDist)
            in go (offset + 1) finalOffset finalReversed finalDist
  in go 0 0 False (1e308)  -- Large number as initial best distance

-- | Rotate and optionally reverse a path's vertices
rotateVertices :: BezierPath -> Int -> Bool -> BezierPath
rotateVertices path offset reverse =
  let n = length (bezierPathVertices path)
      vertices = bezierPathVertices path
      go i
        | i >= n = []
        | otherwise =
            let srcIdx = if reverse
                         then (n - 1 - i + offset + n) `mod` n
                         else (i + offset + n) `mod` n
            in case drop srcIdx vertices of
              [] -> []
              (srcVertex : _) ->
                let newVertex = if reverse
                                then BezierVertex
                                  (clonePoint (bezierVertexPoint srcVertex))
                                  (clonePoint (bezierVertexOutHandle srcVertex))
                                  (clonePoint (bezierVertexInHandle srcVertex))
                                else cloneVertex srcVertex
                in newVertex : go (i + 1)
  in BezierPath (go 0) (bezierPathClosed path)

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // main // api
-- ════════════════════════════════════════════════════════════════════════════

-- | Default morph configuration
defaultMorphConfig :: MorphConfig
defaultMorphConfig = MorphConfig
  { morphConfigPointMatchingStrategy = PointMatchingSubdivideShorter
  , morphConfigCorrespondenceMethod = CorrespondenceNearestRotation
  , morphConfigManualMapping = Nothing
  , morphConfigResampleCount = Nothing
  }

-- | Prepare two paths for morphing by matching vertex counts and finding optimal correspondence
prepareMorphPaths ::
  BezierPath -> BezierPath -> MorphConfig -> Either T.Text PreparedMorphPaths
prepareMorphPaths source target config =
  let sourceVertices = bezierPathVertices source
      targetVertices = bezierPathVertices target
  in if null sourceVertices || null targetVertices
     then Left "Cannot morph empty paths"
     else
       let sourceCount = length sourceVertices
           targetCount = length targetVertices
           -- Step 1: Match vertex counts
           (preparedSource, preparedTarget) =
             if sourceCount == targetCount
             then (clonePath source, clonePath target)
             else
               case morphConfigPointMatchingStrategy config of
                 PointMatchingSubdivideShorter ->
                   if sourceCount < targetCount
                   then (subdivideToVertexCount source targetCount, clonePath target)
                   else (clonePath source, subdivideToVertexCount target sourceCount)
                 PointMatchingSubdivideBoth ->
                   let maxCount = max sourceCount targetCount
                   in (subdivideToVertexCount source maxCount, subdivideToVertexCount target maxCount)
                 PointMatchingResample ->
                   let resampleCount = case morphConfigResampleCount config of
                         Just n | n >= 2 -> n
                         _ -> max sourceCount targetCount
                   in (resamplePath source resampleCount, resamplePath target resampleCount)
           -- Step 2: Find optimal correspondence
           (rotationOffset, reversed) =
             if bezierPathClosed preparedSource && bezierPathClosed preparedTarget
             then
               case morphConfigCorrespondenceMethod config of
                 CorrespondenceNearestRotation -> findOptimalRotation preparedSource preparedTarget
                 CorrespondenceNearestDistance -> findOptimalRotation preparedSource preparedTarget
                 CorrespondenceManual -> (0, False)  -- Manual mapping not implemented
                 CorrespondenceIndex -> (0, False)
             else (0, False)
           -- Apply rotation to target if needed
           finalTarget = if rotationOffset /= 0 || reversed
                        then rotateVertices preparedTarget rotationOffset reversed
                        else preparedTarget
       in Right (PreparedMorphPaths preparedSource finalTarget rotationOffset reversed)

-- | Interpolate between two prepared paths
morphPaths :: BezierPath -> BezierPath -> Double -> Either T.Text BezierPath
morphPaths source target t
  | t <= 0.0 = Right (clonePath source)
  | t >= 1.0 = Right (clonePath target)
  | otherwise =
      let sourceVertices = bezierPathVertices source
          targetVertices = bezierPathVertices target
      in if length sourceVertices /= length targetVertices
         then Left "Paths have different vertex counts - use prepareMorphPaths() first"
         else
           let go i
                 | i >= length sourceVertices = []
                 | otherwise =
                     case (drop i sourceVertices, drop i targetVertices) of
                       ((srcV : _), (tgtV : _)) ->
                         let newVertex =
                               BezierVertex
                                 (pointLerp (bezierVertexPoint srcV) (bezierVertexPoint tgtV) t)
                                 (pointLerp (bezierVertexInHandle srcV) (bezierVertexInHandle tgtV) t)
                                 (pointLerp (bezierVertexOutHandle srcV) (bezierVertexOutHandle tgtV) t)
                         in newVertex : go (i + 1)
                       _ -> []
           in Right (BezierPath (go 0) (bezierPathClosed source))

-- | Convenience function to morph between two arbitrary paths
morphPathsAuto :: BezierPath -> BezierPath -> Double -> MorphConfig -> Either T.Text BezierPath
morphPathsAuto source target t config =
  case prepareMorphPaths source target config of
    Left err -> Left err
    Right prepared ->
      morphPaths (preparedMorphPathsSource prepared) (preparedMorphPathsTarget prepared) t

-- | Calculate the optimal correspondence between two paths
getCorrespondence ::
  BezierPath -> BezierPath -> Either T.Text [(Int, Int)]
getCorrespondence source target =
  case prepareMorphPaths source target defaultMorphConfig of
    Left err -> Left err
    Right prepared ->
      let n = length (bezierPathVertices (preparedMorphPathsSource prepared))
          rotationOffset = preparedMorphPathsRotationOffset prepared
          reversed = preparedMorphPathsReversed prepared
          go i
            | i >= n = []
            | otherwise =
                let targetIdx = if reversed
                                then (n - 1 - i - rotationOffset + 2 * n) `mod` n
                                else (i - rotationOffset + n) `mod` n
                in (i, targetIdx) : go (i + 1)
      in Right (go 0)
