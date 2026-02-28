-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // path-operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathOperations — Illustrator/C4D-style path manipulation.
-- |
-- | ## Design Philosophy
-- |
-- | Professional motion graphics requires precise control over path shape:
-- |
-- | - **Add points**: Insert control points without changing curve shape
-- | - **Equalize spacing**: Make distance between points uniform
-- | - **Smooth/simplify**: Reduce points while maintaining shape
-- | - **Subdivide**: Add points for finer control
-- | - **Reverse**: Flip path direction
-- | - **Offset**: Create parallel paths
-- |
-- | These operations mirror tools in:
-- | - Adobe Illustrator (Smooth Tool, Simplify, Add Anchor Point)
-- | - Cinema 4D (Spline tools, Resample, Smooth)
-- | - After Effects (Path operations, Zig Zag)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.PathOperations as PO
-- |
-- | -- Equalize spacing (like C4D's Resample)
-- | uniform = PO.equalizeSpacing 50 path
-- |
-- | -- Smooth with iterations
-- | smoothed = PO.smooth 3 0.5 path
-- |
-- | -- Add point at parameter t
-- | withPoint = PO.insertPoint 0.5 path
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D)
-- | - Schema.Geometry.Spline (CatmullRomSpline)

module Hydrogen.Schema.Motion.PathOperations
  ( -- * Point Insertion
    insertPoint
  , insertPointAtLength
  , subdivide
  , subdivideAdaptive
  
  -- * Spacing
  , equalizeSpacing
  , resample
  , resampleByLength
  
  -- * Smoothing
  , smooth
  , smoothLaplacian
  , simplify
  , simplifyRDP
  
  -- * Direction
  , reversePath
  , flipPath
  
  -- * Offset
  , offsetPath
  , outlinePath
  
  -- * Analysis
  , pathSegmentLengths
  , pathCurvatures
  , findSharpCorners
  , totalCurvature
  
  -- * Utilities
  , closePathLoop
  , openPath
  , splitAtPoint
  , joinPaths
  
  -- * Filtering
  , filterByDistance
  , filterByAngle
  , removeConsecutiveDuplicates
  
  -- * Display
  , showPath
  , showPathCompact
  
  -- * Pair Processing
  , pairAdjacentPoints
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , otherwise
  , negate
  , min
  , max
  , map
  )

import Data.Array (length, index, snoc, reverse, head, last, take, drop, concat, foldl, filter, cons, zipWith)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (sqrt, abs, atan2, pi, floor)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2, normalize2, perpendicular2, getVX, getVY)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // point insertion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Insert a point at parameter t (0-1) on the path.
-- |
-- | The point is interpolated between existing points.
insertPoint :: Number -> Array Point2D -> Array Point2D
insertPoint t pts =
  if length pts < 2 then pts
  else
    let
      n = length pts
      tScaled = clamp01 t * Int.toNumber (n - 1)
      insertIdx = floorInt tScaled + 1
      localT = tScaled - Int.toNumber (floorInt tScaled)
      
      newPoint = case { p1: index pts (insertIdx - 1), p2: index pts insertIdx } of
        { p1: Just (Point2D a), p2: Just (Point2D b) } ->
          point2D (a.x + localT * (b.x - a.x)) (a.y + localT * (b.y - a.y))
        _ -> fromMaybe (point2D 0.0 0.0) (head pts)
      
      before = take insertIdx pts
      after = drop insertIdx pts
    in
      concat [before, [newPoint], after]

-- | Insert point at specific arc length.
insertPointAtLength :: Number -> Array Point2D -> Array Point2D
insertPointAtLength targetLen pts =
  let totalLen = sumSegmentLengths pts
      t = if totalLen < epsilon then 0.0 else clamp01 (targetLen / totalLen)
  in insertPoint t pts

-- | Subdivide path by inserting midpoints.
subdivide :: Int -> Array Point2D -> Array Point2D
subdivide iterations pts =
  if iterations <= 0 then pts
  else subdivide (iterations - 1) (subdivideOnce pts)

-- | Single subdivision pass.
subdivideOnce :: Array Point2D -> Array Point2D
subdivideOnce pts =
  let n = length pts
  in if n < 2 then pts
     else buildArray (n * 2 - 1) (\i ->
       if i `mod` 2 == 0 then
         index pts (i / 2)
       else
         case { p1: index pts (i / 2), p2: index pts (i / 2 + 1) } of
           { p1: Just (Point2D a), p2: Just (Point2D b) } ->
             Just (point2D ((a.x + b.x) / 2.0) ((a.y + b.y) / 2.0))
           _ -> Nothing
     )

-- | Adaptive subdivision based on curvature.
-- |
-- | Adds more points in high-curvature areas.
subdivideAdaptive :: Number -> Array Point2D -> Array Point2D
subdivideAdaptive threshold pts =
  if length pts < 3 then pts
  else
    let curvatures = computeCurvatures pts
    in foldl (\acc i ->
         case { p: index pts i, c: index curvatures i } of
           { p: Just pt, c: Just curv } ->
             if abs curv > threshold && i > 0 then
               -- Insert midpoint before this sharp corner
               case index pts (i - 1) of
                 Just (Point2D prev) ->
                   let (Point2D curr) = pt
                       mid = point2D ((prev.x + curr.x) / 2.0) ((prev.y + curr.y) / 2.0)
                   in snoc (snoc acc mid) pt
                 Nothing -> snoc acc pt
             else snoc acc pt
           _ -> acc
       ) [] (buildIntArray (length pts))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Equalize spacing between points (C4D Resample).
-- |
-- | Creates n evenly-spaced points along the path.
equalizeSpacing :: Int -> Array Point2D -> Array Point2D
equalizeSpacing n pts =
  if n < 2 || length pts < 2 then pts
  else
    let
      totalLen = sumSegmentLengths pts
      segmentLen = totalLen / Int.toNumber (n - 1)
    in
      buildArray n (\i ->
        let targetLen = Int.toNumber i * segmentLen
        in Just (pointAtArcLength targetLen pts)
      )

-- | Resample path to have n points.
resample :: Int -> Array Point2D -> Array Point2D
resample = equalizeSpacing

-- | Resample with target segment length.
resampleByLength :: Number -> Array Point2D -> Array Point2D
resampleByLength segLen pts =
  let 
    totalLen = sumSegmentLengths pts
    numSegs = max 1 (floorInt (totalLen / segLen))
  in equalizeSpacing (numSegs + 1) pts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // smoothing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smooth path with Chaikin's algorithm.
-- |
-- | Each iteration doubles points and moves them toward smoother positions.
-- | - iterations: number of smoothing passes
-- | - factor: 0-1, how much to smooth (0.25 = classic Chaikin)
smooth :: Int -> Number -> Array Point2D -> Array Point2D
smooth iterations factor pts =
  if iterations <= 0 || length pts < 3 then pts
  else smooth (iterations - 1) factor (chaikinSmooth factor pts)

-- | Single Chaikin smoothing pass.
chaikinSmooth :: Number -> Array Point2D -> Array Point2D
chaikinSmooth factor pts =
  let 
    n = length pts
    f = clamp01 factor
    mf = 1.0 - f
  in
    if n < 2 then pts
    else
      let 
        -- Keep first point
        result = fromMaybe [] (map (\p -> [p]) (head pts))
        
        -- Add smoothed interior points
        interior = foldl (\acc i ->
          case { p1: index pts i, p2: index pts (i + 1) } of
            { p1: Just (Point2D a), p2: Just (Point2D b) } ->
              let 
                q = point2D (mf * a.x + f * b.x) (mf * a.y + f * b.y)
                r = point2D (f * a.x + mf * b.x) (f * a.y + mf * b.y)
              in snoc (snoc acc q) r
            _ -> acc
        ) [] (buildIntArray (n - 1))
        
        -- Keep last point
        lastPt = fromMaybe [] (map (\p -> [p]) (last pts))
      in
        concat [result, interior, lastPt]

-- | Laplacian smoothing (moves points toward neighbor average).
smoothLaplacian :: Int -> Number -> Array Point2D -> Array Point2D
smoothLaplacian iterations strength pts =
  if iterations <= 0 || length pts < 3 then pts
  else smoothLaplacian (iterations - 1) strength (laplacianPass strength pts)

-- | Single Laplacian smoothing pass.
laplacianPass :: Number -> Array Point2D -> Array Point2D
laplacianPass strength pts =
  let n = length pts
  in buildArray n (\i ->
       if i == 0 || i == n - 1 then
         -- Keep endpoints fixed
         index pts i
       else
         case { prev: index pts (i - 1), curr: index pts i, next: index pts (i + 1) } of
           { prev: Just (Point2D p), curr: Just (Point2D c), next: Just (Point2D nx) } ->
             let
               avgX = (p.x + nx.x) / 2.0
               avgY = (p.y + nx.y) / 2.0
               newX = c.x + strength * (avgX - c.x)
               newY = c.y + strength * (avgY - c.y)
             in Just (point2D newX newY)
           _ -> index pts i
     )

-- | Simplify path by removing redundant points.
-- |
-- | Uses distance threshold to determine which points to keep.
simplify :: Number -> Array Point2D -> Array Point2D
simplify tolerance pts =
  if length pts < 3 then pts
  else
    foldl (\acc i ->
      case { curr: index pts i, prev: last acc } of
        { curr: Just (Point2D c), prev: Just (Point2D p) } ->
          let 
            dx = c.x - p.x
            dy = c.y - p.y
            dist = sqrt (dx * dx + dy * dy)
          in if dist >= tolerance then snoc acc (point2D c.x c.y) else acc
        { curr: Just pt, prev: Nothing } -> snoc acc pt
        _ -> acc
    ) [] (buildIntArray (length pts))

-- | Ramer-Douglas-Peucker simplification.
-- |
-- | Removes points that deviate less than tolerance from the line
-- | between kept points. Preserves overall shape better than simple
-- | distance thresholding.
simplifyRDP :: Number -> Array Point2D -> Array Point2D
simplifyRDP tolerance pts =
  let n = length pts
  in if n < 3 then pts
     else rdpRecursive tolerance pts 0 (n - 1)

-- | Recursive RDP implementation.
rdpRecursive :: Number -> Array Point2D -> Int -> Int -> Array Point2D
rdpRecursive tolerance pts startIdx endIdx =
  if endIdx <= startIdx + 1 then
    case { s: index pts startIdx, e: index pts endIdx } of
      { s: Just sp, e: Just ep } -> [sp, ep]
      { s: Just sp, e: Nothing } -> [sp]
      _ -> []
  else
    let
      -- Find point with maximum distance from line
      maxResult = findMaxDistance pts startIdx endIdx
      maxDist = maxResult.distance
      maxIdx = maxResult.index
    in
      if maxDist > tolerance then
        -- Recursively simplify both halves
        let 
          left = rdpRecursive tolerance pts startIdx maxIdx
          right = rdpRecursive tolerance pts maxIdx endIdx
        in 
          -- Remove duplicate point at split
          concat [take (length left - 1) left, right]
      else
        -- Just keep endpoints
        case { s: index pts startIdx, e: index pts endIdx } of
          { s: Just sp, e: Just ep } -> [sp, ep]
          _ -> []

-- | Find point with maximum distance from line.
findMaxDistance :: Array Point2D -> Int -> Int -> { distance :: Number, index :: Int }
findMaxDistance pts startIdx endIdx =
  case { s: index pts startIdx, e: index pts endIdx } of
    { s: Just (Point2D start), e: Just (Point2D end) } ->
      foldl (\acc i ->
        case index pts i of
          Just (Point2D p) ->
            let dist = pointToLineDistance p.x p.y start.x start.y end.x end.y
            in if dist > acc.distance then { distance: dist, index: i } else acc
          Nothing -> acc
      ) { distance: 0.0, index: startIdx } (buildIntRange (startIdx + 1) (endIdx - 1))
    _ -> { distance: 0.0, index: startIdx }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reverse path direction.
reversePath :: Array Point2D -> Array Point2D
reversePath = reverse

-- | Flip path (same as reverse).
flipPath :: Array Point2D -> Array Point2D
flipPath = reverse

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Offset path perpendicular to direction.
-- |
-- | Positive distance = left side, negative = right side.
offsetPath :: Number -> Array Point2D -> Array Point2D
offsetPath distance pts =
  let n = length pts
  in buildArray n (\i ->
       case index pts i of
         Nothing -> Nothing
         Just (Point2D p) ->
           let 
             normal = computeNormalAt i pts
             (Point2D offset) = point2D (getVX normal * distance) (getVY normal * distance)
           in Just (point2D (p.x + offset.x) (p.y + offset.y))
     )

-- | Create outline (offset both sides and connect).
outlinePath :: Number -> Array Point2D -> Array Point2D
outlinePath width pts =
  let
    halfWidth = width / 2.0
    left = offsetPath halfWidth pts
    right = offsetPath (negate halfWidth) pts
  in
    concat [left, reverse right]

-- | Compute normal at point index.
computeNormalAt :: Int -> Array Point2D -> Vector2D
computeNormalAt i pts =
  let
    n = length pts
    -- Get direction from neighboring points
    prevIdx = max 0 (i - 1)
    nextIdx = min (n - 1) (i + 1)
  in
    case { prev: index pts prevIdx, next: index pts nextIdx } of
      { prev: Just (Point2D p), next: Just (Point2D nx) } ->
        let 
          dx = nx.x - p.x
          dy = nx.y - p.y
          len = sqrt (dx * dx + dy * dy)
        in 
          if len < epsilon then vec2 0.0 1.0
          else perpendicular2 (normalize2 (vec2 dx dy))
      _ -> vec2 0.0 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get lengths of each path segment.
pathSegmentLengths :: Array Point2D -> Array Number
pathSegmentLengths pts =
  let n = length pts
  in buildArray (max 0 (n - 1)) (\i ->
       case { p1: index pts i, p2: index pts (i + 1) } of
         { p1: Just (Point2D a), p2: Just (Point2D b) } ->
           let dx = b.x - a.x
               dy = b.y - a.y
           in Just (sqrt (dx * dx + dy * dy))
         _ -> Nothing
     )

-- | Get curvature at each point.
pathCurvatures :: Array Point2D -> Array Number
pathCurvatures = computeCurvatures

-- | Find sharp corners (high curvature points).
-- |
-- | Returns indices of points where curvature exceeds threshold.
findSharpCorners :: Number -> Array Point2D -> Array Int
findSharpCorners threshold pts =
  let curvatures = computeCurvatures pts
  in foldl (\acc i ->
       case index curvatures i of
         Just c -> if abs c > threshold then snoc acc i else acc
         Nothing -> acc
     ) [] (buildIntArray (length curvatures))

-- | Total absolute curvature along path.
totalCurvature :: Array Point2D -> Number
totalCurvature pts =
  let curvatures = computeCurvatures pts
  in foldl (\acc c -> acc + abs c) 0.0 curvatures

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Close path by connecting last point to first.
closePathLoop :: Array Point2D -> Array Point2D
closePathLoop pts =
  case head pts of
    Nothing -> pts
    Just firstPt -> 
      case last pts of
        Nothing -> pts
        Just (Point2D lastP) ->
          let (Point2D firstP) = firstPt
              dx = firstP.x - lastP.x
              dy = firstP.y - lastP.y
              dist = sqrt (dx * dx + dy * dy)
          in if dist < epsilon then pts  -- Already closed
             else snoc pts firstPt

-- | Remove closing point if path is closed.
openPath :: Array Point2D -> Array Point2D
openPath pts =
  let n = length pts
  in if n < 2 then pts
     else case { first: head pts, lst: last pts } of
       { first: Just (Point2D f), lst: Just (Point2D l) } ->
         let dx = f.x - l.x
             dy = f.y - l.y
             dist = sqrt (dx * dx + dy * dy)
         in if dist < epsilon then take (n - 1) pts else pts
       _ -> pts

-- | Split path at parameter t.
splitAtPoint :: Number -> Array Point2D -> { before :: Array Point2D, after :: Array Point2D }
splitAtPoint t pts =
  let
    n = length pts
    tScaled = clamp01 t * Int.toNumber (n - 1)
    splitIdx = floorInt tScaled + 1
    localT = tScaled - Int.toNumber (floorInt tScaled)
    
    midPoint = case { p1: index pts (splitIdx - 1), p2: index pts splitIdx } of
      { p1: Just (Point2D a), p2: Just (Point2D b) } ->
        point2D (a.x + localT * (b.x - a.x)) (a.y + localT * (b.y - a.y))
      _ -> fromMaybe (point2D 0.0 0.0) (head pts)
  in
    { before: snoc (take splitIdx pts) midPoint
    , after: cons midPoint (drop splitIdx pts)
    }

-- | Join two paths end-to-end.
joinPaths :: Array Point2D -> Array Point2D -> Array Point2D
joinPaths a b = concat [a, b]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter points by minimum distance from previous.
filterByDistance :: Number -> Array Point2D -> Array Point2D
filterByDistance minDist pts =
  foldl (\acc pt ->
    case last acc of
      Nothing -> snoc acc pt
      Just (Point2D prev) ->
        let (Point2D curr) = pt
            dx = curr.x - prev.x
            dy = curr.y - prev.y
            dist = sqrt (dx * dx + dy * dy)
        in if dist >= minDist then snoc acc pt else acc
  ) [] pts

-- | Filter out points where angle change is below threshold.
filterByAngle :: Number -> Array Point2D -> Array Point2D
filterByAngle minAngle pts =
  let 
    n = length pts
    curvatures = computeCurvatures pts
    -- Always keep first and last
    kept = filter (\i ->
      i == 0 || i == n - 1 || 
      case index curvatures i of
        Just c -> abs c >= minAngle
        Nothing -> true
    ) (buildIntArray n)
  in
    buildArray (length kept) (\i ->
      case index kept i of
        Just idx -> index pts idx
        Nothing -> Nothing
    )

-- | Remove consecutive duplicate points.
removeConsecutiveDuplicates :: Array Point2D -> Array Point2D
removeConsecutiveDuplicates pts =
  foldl (\acc pt ->
    case last acc of
      Nothing -> snoc acc pt
      Just (Point2D prev) ->
        let (Point2D curr) = pt
            dx = curr.x - prev.x
            dy = curr.y - prev.y
            dist = sqrt (dx * dx + dy * dy)
        in if dist > epsilon then snoc acc pt else acc
  ) [] pts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show path as readable string.
showPath :: Array Point2D -> String
showPath pts =
  "Path [" <> showPointList pts <> "]"

-- | Show path in compact format.
showPathCompact :: Array Point2D -> String
showPathCompact pts =
  let n = length pts
  in "Path(" <> show n <> " points)"

-- | Show list of points.
showPointList :: Array Point2D -> String
showPointList pts =
  let n = length pts
  in if n == 0 then ""
     else foldl (\acc i ->
       case index pts i of
         Just (Point2D p) ->
           let separator = if acc == "" then "" else ", "
           in acc <> separator <> "(" <> show p.x <> "," <> show p.y <> ")"
         Nothing -> acc
     ) "" (buildIntArray n)

-- | Pair up adjacent points with zipWith for edge processing.
pairAdjacentPoints :: Array Point2D -> Array { p1 :: Point2D, p2 :: Point2D }
pairAdjacentPoints pts =
  let pts2 = drop 1 pts
  in zipWith (\a b -> { p1: a, p2: b }) pts pts2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum of all segment lengths.
sumSegmentLengths :: Array Point2D -> Number
sumSegmentLengths pts =
  let segments = pathSegmentLengths pts
  in foldl (+) 0.0 segments

-- | Get point at specific arc length.
pointAtArcLength :: Number -> Array Point2D -> Point2D
pointAtArcLength targetLen pts =
  let
    segments = pathSegmentLengths pts
    n = length segments
  in
    findPointAtLength targetLen segments pts 0 0.0 n

-- | Helper to find point at arc length.
findPointAtLength :: Number -> Array Number -> Array Point2D -> Int -> Number -> Int -> Point2D
findPointAtLength target segments pts i accLen n =
  if i >= n then
    fromMaybe (point2D 0.0 0.0) (last pts)
  else
    case index segments i of
      Nothing -> fromMaybe (point2D 0.0 0.0) (last pts)
      Just segLen ->
        if accLen + segLen >= target then
          -- Interpolate within this segment
          let 
            localT = if segLen < epsilon then 0.0 else (target - accLen) / segLen
          in case { p1: index pts i, p2: index pts (i + 1) } of
            { p1: Just (Point2D a), p2: Just (Point2D b) } ->
              point2D (a.x + localT * (b.x - a.x)) (a.y + localT * (b.y - a.y))
            _ -> fromMaybe (point2D 0.0 0.0) (index pts i)
        else
          findPointAtLength target segments pts (i + 1) (accLen + segLen) n

-- | Compute curvature at each point.
computeCurvatures :: Array Point2D -> Array Number
computeCurvatures pts =
  let n = length pts
  in buildArray n (\i ->
       if i == 0 || i == n - 1 then Just 0.0
       else case { prev: index pts (i - 1), curr: index pts i, next: index pts (i + 1) } of
         { prev: Just (Point2D p), curr: Just (Point2D c), next: Just (Point2D nx) } ->
           Just (computeAngle p.x p.y c.x c.y nx.x nx.y)
         _ -> Just 0.0
     )

-- | Compute angle at vertex (curvature approximation).
computeAngle :: Number -> Number -> Number -> Number -> Number -> Number -> Number
computeAngle px py cx cy nx ny =
  let
    -- Vectors from current to neighbors
    v1x = px - cx
    v1y = py - cy
    v2x = nx - cx
    v2y = ny - cy
    
    -- Angle between vectors
    angle1 = atan2 v1y v1x
    angle2 = atan2 v2y v2x
    diff = angle2 - angle1
  in
    -- Normalize to [-π, π]
    if diff > pi then diff - 2.0 * pi
    else if diff < negate pi then diff + 2.0 * pi
    else diff

-- | Distance from point to line.
pointToLineDistance :: Number -> Number -> Number -> Number -> Number -> Number -> Number
pointToLineDistance px py x1 y1 x2 y2 =
  let
    dx = x2 - x1
    dy = y2 - y1
    lengthSq = dx * dx + dy * dy
  in
    if lengthSq < epsilon then
      -- Degenerate line (point)
      let dpx = px - x1
          dpy = py - y1
      in sqrt (dpx * dpx + dpy * dpy)
    else
      -- Perpendicular distance
      abs (dy * px - dx * py + x2 * y1 - y2 * x1) / sqrt lengthSq

-- | Clamp to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Floor to Int
floorInt :: Number -> Int
floorInt n = 
  let floored = floor n
  in if floored >= 0.0 then truncateToInt floored else truncateToInt floored - 1

-- | Truncate Number to Int (simple approximation)
truncateToInt :: Number -> Int
truncateToInt n = truncateImpl n 0

truncateImpl :: Number -> Int -> Int
truncateImpl n acc =
  if n < 1.0 then acc
  else truncateImpl (n - 1.0) (acc + 1)

-- | Integer modulo
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b

-- | Small epsilon
epsilon :: Number
epsilon = 1.0e-10

-- | Build array from function
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Build integer array [0, n-1]
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n Just

-- | Build integer range [start, end]
buildIntRange :: Int -> Int -> Array Int
buildIntRange start end = 
  buildArray (max 0 (end - start + 1)) (\i -> Just (start + i))
