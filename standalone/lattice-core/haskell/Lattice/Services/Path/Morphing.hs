{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Path.Morphing
Description : Path Morphing Algorithms
Copyright   : (c) Lattice, 2026
License     : MIT

Pure mathematical functions for Bezier path morphing:
- Subdivision for point count matching
- Correspondence optimization (rotation, reversal)
- Travel distance calculation
- Vertex interpolation

Source: ui/src/services/pathMorphing.ts
-}

module Lattice.Services.Path.Morphing
  ( -- * Types
    PointMatchingStrategy(..), CorrespondenceMethod(..)
  , MorphConfig(..), PreparedMorphPaths(..)
  , defaultMorphConfig
    -- * Correspondence
  , calculateTravelDistance, findOptimalRotation, rotateVertices
    -- * Subdivision
  , subdivideSegmentAt, subdivideToVertexCount, findLongestSegment
    -- * Resampling
  , getPointAtArcLength, resamplePath
    -- * Morphing
  , morphPaths, prepareMorphPaths, morphPathsAuto
    -- * Utilities
  , clonePath
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V
import Lattice.Services.Path.BezierCore

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Point matching strategy for paths with different vertex counts
data PointMatchingStrategy
  = SubdivideShorter  -- ^ Add vertices to shorter path
  | SubdivideBoth     -- ^ Add vertices to both paths to match
  | Resample          -- ^ Resample both with even spacing
  deriving (Eq, Show)

-- | Correspondence method for closed paths
data CorrespondenceMethod
  = IndexCorrespondence    -- ^ Direct index matching
  | NearestRotation        -- ^ Find rotation that minimizes travel
  | NearestDistance        -- ^ Same as NearestRotation
  | ManualCorrespondence   -- ^ Use manual mapping
  deriving (Eq, Show)

-- | Morph configuration
data MorphConfig = MorphConfig
  { mcPointMatchingStrategy :: PointMatchingStrategy
  , mcCorrespondenceMethod :: CorrespondenceMethod
  , mcResampleCount :: Maybe Int
  } deriving (Eq, Show)

-- | Result of preparing paths for morphing
data PreparedMorphPaths = PreparedMorphPaths
  { pmpSource :: BezierPath
  , pmpTarget :: BezierPath
  , pmpRotationOffset :: Int
  , pmpReversed :: Bool
  } deriving (Eq, Show)

-- | Default configuration
defaultMorphConfig :: MorphConfig
defaultMorphConfig = MorphConfig SubdivideShorter NearestRotation Nothing

--------------------------------------------------------------------------------
-- Path Cloning
--------------------------------------------------------------------------------

-- | Clone a path
clonePath :: BezierPath -> BezierPath
clonePath path = BezierPath
  { bpVertices = V.map cloneVertex (bpVertices path)
  , bpClosed = bpClosed path
  }

--------------------------------------------------------------------------------
-- Correspondence / Travel Distance
--------------------------------------------------------------------------------

-- | Calculate total travel distance for a given rotation offset.
calculateTravelDistance :: BezierPath -> BezierPath -> Int -> Bool -> Double
calculateTravelDistance source target rotationOffset reversed
  | V.null (bpVertices source) || n /= V.length (bpVertices target) = 0
  | otherwise = sum [dist i | i <- [0..n-1]]
  where
    n = V.length (bpVertices source)
    dist i =
      let srcIdx = i
          tgtIdx = if reversed
                   then (n - 1 - i + rotationOffset + n) `mod` n
                   else (i + rotationOffset) `mod` n
          srcPoint = bvPoint (bpVertices source V.! srcIdx)
          tgtPoint = bvPoint (bpVertices target V.! tgtIdx)
      in pointDistance srcPoint tgtPoint

-- | Find optimal rotation offset to minimize travel distance.
findOptimalRotation :: BezierPath -> BezierPath -> (Int, Bool)
findOptimalRotation source target
  | V.null (bpVertices source) = (0, False)
  | otherwise = findBest 0 0 False (1/0)
  where
    n = V.length (bpVertices source)
    findBest offset bestOffset bestReversed bestDist
      | offset >= n = (bestOffset, bestReversed)
      | otherwise =
          let dist = calculateTravelDistance source target offset False
              (bo1, br1, bd1) = if dist < bestDist
                                then (offset, False, dist)
                                else (bestOffset, bestReversed, bestDist)
              (bo2, br2, bd2) =
                if bpClosed source && bpClosed target
                then let distRev = calculateTravelDistance source target offset True
                     in if distRev < bd1
                        then (offset, True, distRev)
                        else (bo1, br1, bd1)
                else (bo1, br1, bd1)
          in findBest (offset + 1) bo2 br2 bd2

-- | Rotate and optionally reverse a path's vertices.
rotateVertices :: BezierPath -> Int -> Bool -> BezierPath
rotateVertices path offset reverse
  | V.null (bpVertices path) = path
  | otherwise = BezierPath
      { bpVertices = V.generate n makeVertex
      , bpClosed = bpClosed path
      }
  where
    n = V.length (bpVertices path)
    makeVertex i =
      let srcIdx = if reverse
                   then (n - 1 - i + offset + n) `mod` n
                   else (i + offset) `mod` n
          srcVertex = bpVertices path V.! srcIdx
      in if reverse
         then BezierVertex
              { bvPoint = clonePoint (bvPoint srcVertex)
              , bvInHandle = clonePoint (bvOutHandle srcVertex)
              , bvOutHandle = clonePoint (bvInHandle srcVertex)
              }
         else cloneVertex srcVertex

--------------------------------------------------------------------------------
-- Subdivision
--------------------------------------------------------------------------------

-- | Subdivide a segment at parameter t.
subdivideSegmentAt :: BezierPath -> Int -> Double -> BezierPath
subdivideSegmentAt path segmentIndex t
  | V.null (bpVertices path) || segmentIndex >= n = path
  | otherwise =
      let nextIdx = (segmentIndex + 1) `mod` n
          v0 = bpVertices path V.! segmentIndex
          v1 = bpVertices path V.! nextIdx
          p0 = bvPoint v0
          p1 = outHandleAbsolute v0
          p2 = inHandleAbsolute v1
          p3 = bvPoint v1
          (left, right) = splitCubicBezier p0 p1 p2 p3 t
          v0' = v0 { bvOutHandle = subPoints (bsP1 left) (bsP0 left) }
          newVertex = BezierVertex
            { bvPoint = clonePoint (bsP3 left)
            , bvInHandle = subPoints (bsP2 left) (bsP3 left)
            , bvOutHandle = subPoints (bsP1 right) (bsP0 right)
            }
          v1' = v1 { bvInHandle = subPoints (bsP2 right) (bsP3 right) }
          before = V.take segmentIndex (bpVertices path)
          after = V.drop (nextIdx + 1) (bpVertices path)
          newVertices = before V.++ V.fromList [v0', newVertex, v1'] V.++ after
      in BezierPath { bpVertices = newVertices, bpClosed = bpClosed path }
  where
    n = V.length (bpVertices path)

-- | Find index of longest segment.
findLongestSegment :: Vector Double -> Int
findLongestSegment lengths
  | V.null lengths = 0
  | otherwise = V.maxIndex lengths

-- | Subdivide a path to have a specific number of vertices.
subdivideToVertexCount :: BezierPath -> Int -> BezierPath
subdivideToVertexCount path targetCount
  | V.length (bpVertices path) >= targetCount = path
  | otherwise =
      let lengths = getSegmentLengths path 10
          maxIdx = findLongestSegment lengths
          newPath = subdivideSegmentAt path maxIdx 0.5
      in subdivideToVertexCount newPath targetCount

--------------------------------------------------------------------------------
-- Resampling
--------------------------------------------------------------------------------

-- | Get point at a specific arc length along the path.
getPointAtArcLength :: BezierPath -> Double -> Vector Double -> Point2D
getPointAtArcLength path targetLength segmentLengths
  | V.null segmentLengths || V.null (bpVertices path) = zeroPoint
  | otherwise = go 0 0
  where
    go i accumulated
      | i >= V.length segmentLengths =
          bvPoint (V.last (bpVertices path))
      | otherwise =
          let segLen = segmentLengths V.! i
          in if accumulated + segLen >= targetLength || i == V.length segmentLengths - 1
             then let localT = if segLen > 0
                               then (targetLength - accumulated) / segLen
                               else 0
                      clampedT = max 0 (min 1 localT)
                  in case getSegmentControlPoints path i of
                       Just (p0, p1, p2, p3) -> cubicBezierPoint p0 p1 p2 p3 clampedT
                       Nothing -> bvPoint (bpVertices path V.! i)
             else go (i + 1) (accumulated + segLen)

-- | Resample a path with evenly spaced vertices.
resamplePath :: BezierPath -> Int -> BezierPath
resamplePath path vertexCount
  | vertexCount < 2 || V.null (bpVertices path) = clonePath path
  | totalLength == 0 = clonePath path
  | otherwise = BezierPath
      { bpVertices = V.generate vertexCount makeVertex
      , bpClosed = bpClosed path
      }
  where
    segmentLengths = getSegmentLengths path 10
    totalLength = V.sum segmentLengths
    spacing = totalLength / (if bpClosed path then fromIntegral vertexCount else fromIntegral (vertexCount - 1))
    makeVertex i =
      let targetLength = fromIntegral i * spacing
          point = getPointAtArcLength path targetLength segmentLengths
          prevLength = max 0 (targetLength - spacing * 0.33)
          nextLength = min totalLength (targetLength + spacing * 0.33)
          prevPoint = getPointAtArcLength path prevLength segmentLengths
          nextPoint = getPointAtArcLength path nextLength segmentLengths
          tangent = scalePoint (subPoints nextPoint prevPoint) 0.5
          handleScale = 0.33
      in BezierVertex
         { bvPoint = clonePoint point
         , bvInHandle = scalePoint tangent (-handleScale)
         , bvOutHandle = scalePoint tangent handleScale
         }

--------------------------------------------------------------------------------
-- Main Morphing Functions
--------------------------------------------------------------------------------

-- | Interpolate between two prepared paths.
morphPaths :: BezierPath -> BezierPath -> Double -> BezierPath
morphPaths source target t
  | clampedT == 0 = clonePath source
  | clampedT == 1 = clonePath target
  | otherwise = BezierPath
      { bpVertices = V.zipWith (\v1 v2 -> lerpVertex v1 v2 clampedT)
                               (bpVertices source)
                               (bpVertices target)
      , bpClosed = bpClosed source
      }
  where
    clampedT = max 0 (min 1 t)

-- | Prepare two paths for morphing.
prepareMorphPaths :: BezierPath -> BezierPath -> MorphConfig -> PreparedMorphPaths
prepareMorphPaths source target config
  | V.null (bpVertices source) || V.null (bpVertices target) =
      PreparedMorphPaths (clonePath source) (clonePath target) 0 False
  | otherwise =
      let -- Step 1: Match vertex counts
          (prepSource, prepTarget) =
            if V.length (bpVertices source) == V.length (bpVertices target)
            then (clonePath source, clonePath target)
            else case mcPointMatchingStrategy config of
              SubdivideShorter ->
                if V.length (bpVertices source) < V.length (bpVertices target)
                then (subdivideToVertexCount source (V.length (bpVertices target)),
                      clonePath target)
                else (clonePath source,
                      subdivideToVertexCount target (V.length (bpVertices source)))
              SubdivideBoth ->
                let maxCount = max (V.length (bpVertices source))
                                   (V.length (bpVertices target))
                in (subdivideToVertexCount source maxCount,
                    subdivideToVertexCount target maxCount)
              Resample ->
                let count = maybe (max (V.length (bpVertices source))
                                       (V.length (bpVertices target)))
                                  id (mcResampleCount config)
                in (resamplePath source count, resamplePath target count)

          -- Step 2: Find optimal correspondence
          (rotationOffset, reversed) =
            if bpClosed prepSource && bpClosed prepTarget
            then case mcCorrespondenceMethod config of
              NearestRotation -> findOptimalRotation prepSource prepTarget
              NearestDistance -> findOptimalRotation prepSource prepTarget
              _ -> (0, False)
            else (0, False)

          -- Apply rotation
          finalTarget =
            if rotationOffset /= 0 || reversed
            then rotateVertices prepTarget rotationOffset reversed
            else prepTarget

      in PreparedMorphPaths prepSource finalTarget rotationOffset reversed

-- | Convenience function: prepare and morph in one step.
morphPathsAuto :: BezierPath -> BezierPath -> Double -> MorphConfig -> BezierPath
morphPathsAuto source target t config =
  let prepared = prepareMorphPaths source target config
  in morphPaths (pmpSource prepared) (pmpTarget prepared) t
