-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // gpu // scene3d // path arc length
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathArcLength — Arc-length parameterization and uniform sampling.
-- |
-- | ## Design
-- | Provides "uniform speed" traversal of paths where equal parameter
-- | increments produce equal distances traveled along the curve.
-- |
-- | ## Use Cases
-- | - Camera motion along paths (constant velocity)
-- | - Evenly-spaced markers/decorations along curves
-- | - Animation with consistent speed regardless of curve complexity

module Hydrogen.GPU.Scene3D.PathArcLength
  ( -- * Arc-Length Evaluation
    evalPathArcLength
  , pathTotalArcLength
  , evalPathAtArcLength
  
  -- * Uniform Sampling
  , samplePath
  , samplePathUniform
  , decimateSamples
  
  -- * Segment Length Utilities
  , sumSegmentLengths
  , sumSegmentLengthsFold
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , (==)
  , bind
  , pure
  , map
  )

import Data.Array (length, head, foldl, snoc, tail, (..))
import Data.Int (toNumber, floor, rem) as Int
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3
  , subtractVec3
  , lengthVec3
  )

import Hydrogen.GPU.Scene3D.Path (Path3D)
import Hydrogen.GPU.Scene3D.PathEval (evalPath)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // arc-length eval
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of samples for arc-length integration.
arcLengthSamples :: Int
arcLengthSamples = 64

-- | Compute arc length from start of path to parameter t.
-- |
-- | Uses numerical integration via sampling.
evalPathArcLength :: Path3D -> Number -> Maybe Number
evalPathArcLength path t = do
  let
    pts = path.points
    n = length pts
  
  if n < 2 then pure 0.0 else do
    let
      numSamples = floorToInt (toNumber arcLengthSamples * t) + 1
      sampleParams = map (\i -> t * toNumber i / toNumber numSamples) (range 0 numSamples)
    
    positions <- traverse (\s -> evalPath path s) sampleParams
    pure (sumSegmentLengths positions)

-- | Get total arc length of the entire path.
pathTotalArcLength :: Path3D -> Maybe Number
pathTotalArcLength path = evalPathArcLength path 1.0

-- | Evaluate position at a specific arc-length distance from start.
-- |
-- | This gives "uniform speed" parameterization — equal arc-length
-- | increments produce equal distance traveled along the curve.
evalPathAtArcLength :: Path3D -> Number -> Maybe (Vec3 Number)
evalPathAtArcLength path targetLength = do
  totalLen <- pathTotalArcLength path
  
  if targetLength <= 0.0 then
    evalPath path 0.0
  else if targetLength >= totalLen then
    evalPath path 1.0
  else do
    let t = findTForArcLength path targetLength totalLen 0.0 1.0 20
    evalPath path t

-- | Binary search to find t for a target arc length.
findTForArcLength :: Path3D -> Number -> Number -> Number -> Number -> Int -> Number
findTForArcLength path target total lo hi iterations =
  if iterations <= 0 then
    (lo + hi) / 2.0
  else
    let
      mid = (lo + hi) / 2.0
      midLen = mid * total  -- Linear approximation
    in
      if midLen < target then
        findTForArcLength path target total mid hi (iterations - 1)
      else
        findTForArcLength path target total lo mid (iterations - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // uniform sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample the path at regular parameter intervals.
-- |
-- | Returns array of positions from t=0 to t=1.
samplePath :: Path3D -> Int -> Maybe (Array (Vec3 Number))
samplePath path numSamples =
  if numSamples < 2 then Nothing
  else do
    let
      params = map (\i -> toNumber i / toNumber (numSamples - 1)) (range 0 (numSamples - 1))
    traverse (\t -> evalPath path t) params

-- | Sample the path at regular arc-length intervals.
-- |
-- | Produces evenly-spaced points along the curve's actual length.
samplePathUniform :: Path3D -> Int -> Maybe (Array (Vec3 Number))
samplePathUniform path numSamples =
  if numSamples < 2 then Nothing
  else do
    totalLen <- pathTotalArcLength path
    let
      distances = map (\i -> totalLen * toNumber i / toNumber (numSamples - 1)) (range 0 (numSamples - 1))
    traverse (\d -> evalPathAtArcLength path d) distances

-- | Decimate a sampled path by keeping every nth point.
-- |
-- | Useful for LOD (level of detail) systems.
decimateSamples :: forall a. Int -> Array a -> Array a
decimateSamples stride arr =
  if stride <= 1 then arr
  else decimateAccum stride 0 arr []

-- | Accumulator for decimation.
decimateAccum :: forall a. Int -> Int -> Array a -> Array a -> Array a
decimateAccum stride idx arr acc =
  case head arr of
    Nothing -> acc
    Just x ->
      let newAcc = if modInt idx stride == 0 then snoc acc x else acc
      in decimateAccum stride (idx + 1) (dropFirst arr) newAcc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // segment utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum the lengths of segments between consecutive points.
sumSegmentLengths :: Array (Vec3 Number) -> Number
sumSegmentLengths positions =
  case head positions of
    Nothing -> 0.0
    Just firstPos -> sumSegmentsAccum (dropFirst positions) firstPos 0.0

-- | Accumulator for segment length summation.
sumSegmentsAccum :: Array (Vec3 Number) -> Vec3 Number -> Number -> Number
sumSegmentsAccum remaining prevPos totalLen =
  case head remaining of
    Nothing -> totalLen
    Just pos ->
      let segLen = lengthVec3 (subtractVec3 pos prevPos)
      in sumSegmentsAccum (dropFirst remaining) pos (totalLen + segLen)

-- | Sum segment lengths using foldl.
sumSegmentLengthsFold :: Array (Vec3 Number) -> Number
sumSegmentLengthsFold positions =
  case head positions of
    Nothing -> 0.0
    Just firstPos ->
      let
        result = foldl accumSegment { prev: firstPos, total: 0.0 } (dropFirst positions)
      in
        result.total

-- | Accumulator type for fold-based segment summation.
type SegmentAccum = { prev :: Vec3 Number, total :: Number }

-- | Fold accumulator function.
accumSegment :: SegmentAccum -> Vec3 Number -> SegmentAccum
accumSegment acc pos =
  { prev: pos
  , total: acc.total + lengthVec3 (subtractVec3 pos acc.prev)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate integer range.
range :: Int -> Int -> Array Int
range lo hi = lo .. hi

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Floor Number to Int.
floorToInt :: Number -> Int
floorToInt = Int.floor

-- | Integer modulo.
modInt :: Int -> Int -> Int
modInt = Int.rem

-- | Drop first element of array.
dropFirst :: forall a. Array a -> Array a
dropFirst arr = fromMaybe [] (tail arr)

-- | Traverse Maybe over array.
traverse :: forall a b. (a -> Maybe b) -> Array a -> Maybe (Array b)
traverse f arr = traverseAccum f arr []

-- | Traverse accumulator.
traverseAccum :: forall a b. (a -> Maybe b) -> Array a -> Array b -> Maybe (Array b)
traverseAccum f arr acc =
  case head arr of
    Nothing -> Just acc
    Just x -> case f x of
      Nothing -> Nothing
      Just y -> traverseAccum f (dropFirst arr) (snoc acc y)
