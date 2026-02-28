-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // scene3d // path metrics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathMetrics — Path validation, endpoints, and analysis metrics.
-- |
-- | ## Design
-- | Provides utilities for:
-- | - Validating paths before evaluation
-- | - Accessing path endpoints
-- | - Computing path metrics (sinuosity, chord length)

module Hydrogen.GPU.Scene3D.PathMetrics
  ( -- * Validation
    isPathValidAt
  , isPathEmpty
  , canInterpolate
  
  -- * Endpoint Access
  , pathStartPoint
  , pathEndPoint
  , pathChord
  , pathChordLength
  
  -- * Path Info
  , pathPointCount
  , pathSegmentCount
  
  -- * Metrics
  , pathSinuosity
  , pathSinuosityOr
  , pathComplexity
  
  -- * Predicates
  , isPathClosed
  , hasMinPoints
  
  -- * Utilities
  , roundToInt
  , dropN
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , (&&)
  , bind
  , pure
  )

import Data.Array (length, head, last, null, drop)
import Data.Int (round, toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3
  , subtractVec3
  , lengthVec3
  )

import Hydrogen.GPU.Scene3D.Path (Path3D)
import Hydrogen.GPU.Scene3D.PathArcLength (pathTotalArcLength)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a path is valid for evaluation at parameter t.
-- |
-- | A valid path has:
-- | - At least one point (for position queries)
-- | - At least two points (for tangent/normal queries)
-- | - Parameter t in valid range [0, 1]
isPathValidAt :: Path3D -> Number -> Boolean -> Boolean
isPathValidAt path t requireTangent =
  let
    pts = path.points
    n = length pts
    hasEnoughPoints = if requireTangent then n >= 2 else n >= 1
    tInRange = t >= 0.0 && t <= 1.0
  in
    hasEnoughPoints && tInRange

-- | Check if a path is empty (has no control points).
isPathEmpty :: Path3D -> Boolean
isPathEmpty path = null path.points

-- | Check if path has enough points for interpolation.
canInterpolate :: Path3D -> Boolean
canInterpolate path = length path.points >= 2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // endpoint access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the first point's position on the path.
pathStartPoint :: Path3D -> Maybe (Vec3 Number)
pathStartPoint path = do
  pt <- head path.points
  pure pt.position

-- | Get the last point's position on the path.
pathEndPoint :: Path3D -> Maybe (Vec3 Number)
pathEndPoint path = do
  pt <- last path.points
  pure pt.position

-- | Get the vector from start to end of the path (chord).
-- |
-- | Useful for:
-- | - Quick approximation of path direction
-- | - Bounding box calculations
-- | - Checking if path doubles back
pathChord :: Path3D -> Maybe (Vec3 Number)
pathChord path = do
  startPt <- pathStartPoint path
  endPt <- pathEndPoint path
  pure (subtractVec3 endPt startPt)

-- | Get the straight-line distance from start to end.
pathChordLength :: Path3D -> Maybe Number
pathChordLength path = do
  chord <- pathChord path
  pure (lengthVec3 chord)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // metrics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute the "sinuosity" of a path.
-- |
-- | Sinuosity = arc length / chord length
-- | - 1.0 = perfectly straight
-- | - > 1.0 = curved (higher = more winding)
-- |
-- | Used in: river analysis, road design, animation path complexity.
pathSinuosity :: Path3D -> Maybe Number
pathSinuosity path = do
  arcLen <- pathTotalArcLength path
  chordLen <- pathChordLength path
  if chordLen < 0.000001
    then pure 1.0
    else pure (arcLen / chordLen)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Round a Number to nearest Int.
roundToInt :: Number -> Int
roundToInt = Int.round

-- | Drop first n elements from array.
dropN :: forall a. Int -> Array a -> Array a
dropN n arr = drop n arr

-- | Count the number of control points in a path.
pathPointCount :: Path3D -> Int
pathPointCount path = length path.points

-- | Count the number of segments (edges between points).
-- |
-- | For open paths: n-1 segments for n points
-- | For closed paths: n segments for n points
pathSegmentCount :: Path3D -> Int
pathSegmentCount path =
  let n = length path.points
  in if path.closed then n else maxInt 0 (n - 1)

-- | Maximum of two integers.
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Get sinuosity with a default value for invalid paths.
-- |
-- | Returns the provided default if path cannot compute sinuosity.
pathSinuosityOr :: Number -> Path3D -> Number
pathSinuosityOr defaultVal path =
  case pathSinuosity path of
    Just s -> s
    Nothing -> defaultVal

-- | Check if path is a closed loop.
isPathClosed :: Path3D -> Boolean
isPathClosed path = path.closed

-- | Check if path has at least the given number of points.
hasMinPoints :: Int -> Path3D -> Boolean
hasMinPoints minCount path = length path.points >= minCount

-- | Compute approximate path complexity.
-- |
-- | Complexity = point count + sinuosity bonus
-- | Used for LOD decisions, performance budgeting.
pathComplexity :: Path3D -> Maybe Number
pathComplexity path = do
  sinuosity <- pathSinuosity path
  let pointBonus = Int.toNumber (pathPointCount path)
  pure (pointBonus + sinuosity)
