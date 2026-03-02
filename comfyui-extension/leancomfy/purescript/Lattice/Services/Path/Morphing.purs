-- | Lattice.Services.Path.Morphing - Path Morphing Algorithms
-- |
-- | Pure mathematical functions for Bezier path morphing:
-- | - Subdivision for point count matching
-- | - Correspondence optimization (rotation, reversal)
-- | - Travel distance calculation
-- | - Vertex interpolation
-- |
-- | Source: ui/src/services/pathMorphing.ts

module Lattice.Services.Path.Morphing
  ( -- * Types
    PointMatchingStrategy(..), CorrespondenceMethod(..)
  , MorphConfig, PreparedMorphPaths
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

import Prelude
import Data.Array (length, index, (!!), take, drop, zipWith, snoc, foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Math (max, min) as Math

import Lattice.Services.Path.BezierCore

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Point matching strategy for paths with different vertex counts
data PointMatchingStrategy
  = SubdivideShorter  -- ^ Add vertices to shorter path
  | SubdivideBoth     -- ^ Add vertices to both paths to match
  | Resample          -- ^ Resample both with even spacing

derive instance eqPointMatchingStrategy :: Eq PointMatchingStrategy

-- | Correspondence method for closed paths
data CorrespondenceMethod
  = IndexCorrespondence    -- ^ Direct index matching
  | NearestRotation        -- ^ Find rotation that minimizes travel
  | NearestDistance        -- ^ Same as NearestRotation
  | ManualCorrespondence   -- ^ Use manual mapping

derive instance eqCorrespondenceMethod :: Eq CorrespondenceMethod

-- | Morph configuration
type MorphConfig =
  { pointMatchingStrategy :: PointMatchingStrategy
  , correspondenceMethod :: CorrespondenceMethod
  , resampleCount :: Maybe Int
  }

-- | Result of preparing paths for morphing
type PreparedMorphPaths =
  { source :: BezierPath
  , target :: BezierPath
  , rotationOffset :: Int
  , reversed :: Boolean
  }

-- | Default configuration
defaultMorphConfig :: MorphConfig
defaultMorphConfig =
  { pointMatchingStrategy: SubdivideShorter
  , correspondenceMethod: NearestRotation
  , resampleCount: Nothing
  }

--------------------------------------------------------------------------------
-- Path Cloning
--------------------------------------------------------------------------------

-- | Clone a path
clonePath :: BezierPath -> BezierPath
clonePath path =
  { vertices: map cloneVertex path.vertices
  , closed: path.closed
  }

--------------------------------------------------------------------------------
-- Correspondence / Travel Distance
--------------------------------------------------------------------------------

-- | Calculate total travel distance for a given rotation offset.
calculateTravelDistance :: BezierPath -> BezierPath -> Int -> Boolean -> Number
calculateTravelDistance source target rotationOffset reversed =
  let n = length source.vertices
  in if length source.vertices == 0 || n /= length target.vertices
     then 0.0
     else go n 0 0.0
  where
    go n i acc
      | i >= n = acc
      | otherwise =
          let srcIdx = i
              tgtIdx = if reversed
                       then (n - 1 - i + rotationOffset + n) `mod` n
                       else (i + rotationOffset) `mod` n
              srcPoint = fromMaybe zeroPoint (map _.point (source.vertices !! srcIdx))
              tgtPoint = fromMaybe zeroPoint (map _.point (target.vertices !! tgtIdx))
              dist = pointDistance srcPoint tgtPoint
          in go n (i + 1) (acc + dist)

-- | Find optimal rotation offset to minimize travel distance.
findOptimalRotation :: BezierPath -> BezierPath -> { offset :: Int, reversed :: Boolean }
findOptimalRotation source target
  | length source.vertices == 0 = { offset: 0, reversed: false }
  | otherwise = findBest 0 0 false infinity
  where
    n = length source.vertices
    infinity = 1.0 / 0.0

    findBest offset bestOffset bestReversed bestDist
      | offset >= n = { offset: bestOffset, reversed: bestReversed }
      | otherwise =
          let dist = calculateTravelDistance source target offset false
              r1 = if dist < bestDist
                   then { o: offset, r: false, d: dist }
                   else { o: bestOffset, r: bestReversed, d: bestDist }
              r2 = if source.closed && target.closed
                   then let distRev = calculateTravelDistance source target offset true
                        in if distRev < r1.d
                           then { o: offset, r: true, d: distRev }
                           else r1
                   else r1
          in findBest (offset + 1) r2.o r2.r r2.d

-- | Rotate and optionally reverse a path's vertices.
rotateVertices :: BezierPath -> Int -> Boolean -> BezierPath
rotateVertices path offset reverse
  | length path.vertices == 0 = path
  | otherwise =
      { vertices: mapWithIndex makeVertex path.vertices
      , closed: path.closed
      }
  where
    n = length path.vertices
    mapWithIndex f arr = go 0 []
      where
        go i acc
          | i >= length arr = acc
          | otherwise = go (i + 1) (snoc acc (f i))

    makeVertex i =
      let srcIdx = if reverse
                   then (n - 1 - i + offset + n) `mod` n
                   else (i + offset) `mod` n
          srcVertex = fromMaybe defaultVertex (path.vertices !! srcIdx)
      in if reverse
         then { point: clonePoint srcVertex.point
              , inHandle: clonePoint srcVertex.outHandle
              , outHandle: clonePoint srcVertex.inHandle
              }
         else cloneVertex srcVertex

    defaultVertex = { point: zeroPoint, inHandle: zeroPoint, outHandle: zeroPoint }

--------------------------------------------------------------------------------
-- Subdivision
--------------------------------------------------------------------------------

-- | Find index of longest segment.
findLongestSegment :: Array Number -> Int
findLongestSegment lengths
  | length lengths == 0 = 0
  | otherwise = go 0 0 0.0
  where
    go i maxIdx maxLen
      | i >= length lengths = maxIdx
      | otherwise =
          let len = fromMaybe 0.0 (lengths !! i)
          in if len > maxLen
             then go (i + 1) i len
             else go (i + 1) maxIdx maxLen

-- | Subdivide a segment at parameter t.
subdivideSegmentAt :: BezierPath -> Int -> Number -> BezierPath
subdivideSegmentAt path segmentIndex t =
  let n = length path.vertices
  in if length path.vertices == 0 || segmentIndex >= n
     then path
     else fromMaybe path do
       v0 <- path.vertices !! segmentIndex
       let nextIdx = (segmentIndex + 1) `mod` n
       v1 <- path.vertices !! nextIdx
       let p0 = v0.point
           p1 = outHandleAbsolute v0
           p2 = inHandleAbsolute v1
           p3 = v1.point
           result = splitCubicBezier p0 p1 p2 p3 t
           v0' = v0 { outHandle = subPoints result.left.p1 result.left.p0 }
           newVertex =
             { point: clonePoint result.left.p3
             , inHandle: subPoints result.left.p2 result.left.p3
             , outHandle: subPoints result.right.p1 result.right.p0
             }
           v1' = v1 { inHandle = subPoints result.right.p2 result.right.p3 }
           before = take segmentIndex path.vertices
           after = drop (nextIdx + 1) path.vertices
           newVertices = before <> [v0', newVertex, v1'] <> after
       pure { vertices: newVertices, closed: path.closed }

-- | Subdivide a path to have a specific number of vertices.
subdivideToVertexCount :: BezierPath -> Int -> BezierPath
subdivideToVertexCount path targetCount
  | length path.vertices >= targetCount = path
  | otherwise =
      let lengths = getSegmentLengths path 10
          maxIdx = findLongestSegment lengths
          newPath = subdivideSegmentAt path maxIdx 0.5
      in subdivideToVertexCount newPath targetCount

--------------------------------------------------------------------------------
-- Resampling
--------------------------------------------------------------------------------

-- | Get point at a specific arc length along the path.
getPointAtArcLength :: BezierPath -> Number -> Array Number -> Point2D
getPointAtArcLength path targetLength segmentLengths
  | length segmentLengths == 0 || length path.vertices == 0 = zeroPoint
  | otherwise = go 0 0.0
  where
    go i accumulated
      | i >= length segmentLengths =
          fromMaybe zeroPoint (map _.point (path.vertices !! (length path.vertices - 1)))
      | otherwise =
          let segLen = fromMaybe 0.0 (segmentLengths !! i)
          in if accumulated + segLen >= targetLength || i == length segmentLengths - 1
             then let localT = if segLen > 0.0
                               then (targetLength - accumulated) / segLen
                               else 0.0
                      clampedT = Math.max 0.0 (Math.min 1.0 localT)
                  in case getSegmentControlPoints path i of
                       Just pts -> cubicBezierPoint pts.p0 pts.p1 pts.p2 pts.p3 clampedT
                       Nothing -> fromMaybe zeroPoint (map _.point (path.vertices !! i))
             else go (i + 1) (accumulated + segLen)

-- | Resample a path with evenly spaced vertices.
resamplePath :: BezierPath -> Int -> BezierPath
resamplePath path vertexCount
  | vertexCount < 2 || length path.vertices == 0 = clonePath path
  | otherwise =
      let segmentLengths = getSegmentLengths path 10
          totalLength = foldl (+) 0.0 segmentLengths
      in if totalLength == 0.0
         then clonePath path
         else
           let spacing = totalLength / (if path.closed then toNumber vertexCount else toNumber (vertexCount - 1))

               mapRange start end f
                 | start >= end = []
                 | otherwise = [f start] <> mapRange (start + 1) end f

               makeVertex i =
                 let targetLen = toNumber i * spacing
                     point = getPointAtArcLength path targetLen segmentLengths
                     prevLength = Math.max 0.0 (targetLen - spacing * 0.33)
                     nextLength = Math.min totalLength (targetLen + spacing * 0.33)
                     prevPoint = getPointAtArcLength path prevLength segmentLengths
                     nextPoint = getPointAtArcLength path nextLength segmentLengths
                     tangent = scalePoint (subPoints nextPoint prevPoint) 0.5
                     handleScale = 0.33
                 in { point: clonePoint point
                    , inHandle: scalePoint tangent (-handleScale)
                    , outHandle: scalePoint tangent handleScale
                    }
           in { vertices: mapRange 0 vertexCount makeVertex
              , closed: path.closed
              }

--------------------------------------------------------------------------------
-- Main Morphing Functions
--------------------------------------------------------------------------------

-- | Interpolate between two prepared paths.
morphPaths :: BezierPath -> BezierPath -> Number -> BezierPath
morphPaths source target t =
  let clampedT = Math.max 0.0 (Math.min 1.0 t)
  in if clampedT == 0.0
     then clonePath source
     else if clampedT == 1.0
     then clonePath target
     else
       { vertices: zipWith (\v1 v2 -> lerpVertex v1 v2 clampedT)
                            source.vertices
                            target.vertices
       , closed: source.closed
       }

-- | Prepare two paths for morphing.
prepareMorphPaths :: BezierPath -> BezierPath -> MorphConfig -> PreparedMorphPaths
prepareMorphPaths source target config
  | length source.vertices == 0 || length target.vertices == 0 =
      { source: clonePath source, target: clonePath target, rotationOffset: 0, reversed: false }
  | otherwise =
      let -- Step 1: Match vertex counts
          prepared =
            if length source.vertices == length target.vertices
            then { s: clonePath source, t: clonePath target }
            else case config.pointMatchingStrategy of
              SubdivideShorter ->
                if length source.vertices < length target.vertices
                then { s: subdivideToVertexCount source (length target.vertices)
                     , t: clonePath target }
                else { s: clonePath source
                     , t: subdivideToVertexCount target (length source.vertices) }
              SubdivideBoth ->
                let maxCount = max (length source.vertices) (length target.vertices)
                in { s: subdivideToVertexCount source maxCount
                   , t: subdivideToVertexCount target maxCount }
              Resample ->
                let count = fromMaybe (max (length source.vertices)
                                           (length target.vertices))
                                      config.resampleCount
                in { s: resamplePath source count, t: resamplePath target count }

          -- Step 2: Find optimal correspondence
          correspondence =
            if prepared.s.closed && prepared.t.closed
            then case config.correspondenceMethod of
              NearestRotation -> findOptimalRotation prepared.s prepared.t
              NearestDistance -> findOptimalRotation prepared.s prepared.t
              _ -> { offset: 0, reversed: false }
            else { offset: 0, reversed: false }

          -- Apply rotation
          finalTarget =
            if correspondence.offset /= 0 || correspondence.reversed
            then rotateVertices prepared.t correspondence.offset correspondence.reversed
            else prepared.t

      in { source: prepared.s
         , target: finalTarget
         , rotationOffset: correspondence.offset
         , reversed: correspondence.reversed
         }

-- | Convenience function: prepare and morph in one step.
morphPathsAuto :: BezierPath -> BezierPath -> Number -> MorphConfig -> BezierPath
morphPathsAuto source target t config =
  let prepared = prepareMorphPaths source target config
  in morphPaths prepared.source prepared.target t
