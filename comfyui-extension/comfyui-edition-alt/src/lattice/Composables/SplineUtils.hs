-- |
-- Module      : Lattice.Composables.SplineUtils
-- Description : Bezier/spline math and path operations
--
-- Ported from ui/src/composables/useSplineUtils.ts
-- Pure math: bezier evaluation, arc length, path finding, coordinate transform.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.SplineUtils
  ( -- Types
    LayerTransformValues(..)
  , SplineControlPoint(..)
  , ClosestPointResult(..)
  -- Bezier evaluation
  , evaluateBezier
  , evaluateBezierTangent
  , bezierArcLength
  -- Path operations (Either for "not found" instead of throw)
  , findClosestPointOnPath
  , findPointAtPosition
  --                                                                       // svg
  , generateSplinePath
  , generateCurvePreview
  -- Coordinate transformation
  , transformPointToComp
  , transformPointToLayer
  -- Path smoothing
  , calculateSmoothHandles
  , simplifyPath
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Primitives (Vec2(..), validateFinite)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Layer transform for coordinate conversion (position, rotation, scale, anchor)
data LayerTransformValues = LayerTransformValues
  { layerTransformPosition :: Vec2
  , layerTransformRotation :: Double
  , layerTransformScale :: Vec2
  , layerTransformAnchorPoint :: Vec2
  }
  deriving (Eq, Show)

-- | Control point with optional bezier handles (for spline path)
data SplineControlPoint = SplineControlPoint
  { splineControlPointPos :: Vec2
  , splineControlPointHandleIn :: Maybe Vec2
  , splineControlPointHandleOut :: Maybe Vec2
  }
  deriving (Eq, Show)

-- | Result of finding closest point on path
data ClosestPointResult = ClosestPointResult
  { closestPointX :: Double
  , closestPointY :: Double
  , closestPointSegmentIndex :: Int
  , closestPointT :: Double
  }
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                             // bezier // curve // evaluation
-- ════════════════════════════════════════════════════════════════════════════

-- | Evaluate cubic bezier at parameter t (0..1)
evaluateBezier :: Vec2 -> Vec2 -> Vec2 -> Vec2 -> Double -> Vec2
evaluateBezier p0 h0 h1 p1 t =
  let mt = 1 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
      t2 = t * t
      t3 = t2 * t
      x = mt3 * vec2X p0 + 3 * mt2 * t * vec2X h0 + 3 * mt * t2 * vec2X h1 + t3 * vec2X p1
      y = mt3 * vec2Y p0 + 3 * mt2 * t * vec2Y h0 + 3 * mt * t2 * vec2Y h1 + t3 * vec2Y p1
  in Vec2 x y

-- | Tangent (derivative) of cubic bezier at t
evaluateBezierTangent :: Vec2 -> Vec2 -> Vec2 -> Vec2 -> Double -> Vec2
evaluateBezierTangent p0 h0 h1 p1 t =
  let mt = 1 - t
      mt2 = mt * mt
      t2 = t * t
      dx = 3 * mt2 * (vec2X h0 - vec2X p0) + 6 * mt * t * (vec2X h1 - vec2X h0) + 3 * t2 * (vec2X p1 - vec2X h1)
      dy = 3 * mt2 * (vec2Y h0 - vec2Y p0) + 6 * mt * t * (vec2Y h1 - vec2Y h0) + 3 * t2 * (vec2Y p1 - vec2Y h1)
  in Vec2 dx dy

-- | Approximate arc length of bezier segment (Gaussian quadrature style sampling)
bezierArcLength :: Vec2 -> Vec2 -> Vec2 -> Vec2 -> Int -> Double
bezierArcLength p0 h0 h1 p1 samples =
  let step = 1 / fromIntegral (max 1 samples)
      go i acc prev
        | i > samples = acc
        | otherwise =
            let t = step * fromIntegral i
                curr = evaluateBezier p0 h0 h1 p1 t
                dx = vec2X curr - vec2X prev
                dy = vec2Y curr - vec2Y prev
                seg = sqrt (dx * dx + dy * dy)
            in go (i + 1) (acc + seg) curr
  in go 1 0 p0

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // path // operations
-- ════════════════════════════════════════════════════════════════════════════

distance :: Vec2 -> Vec2 -> Double
distance a b = sqrt ((vec2X a - vec2X b) ** 2 + (vec2Y a - vec2Y b) ** 2)

getHandleOut :: SplineControlPoint -> Vec2
getHandleOut cp = case splineControlPointHandleOut cp of
  Just h -> h
  Nothing -> splineControlPointPos cp

getHandleIn :: SplineControlPoint -> Vec2
getHandleIn cp = case splineControlPointHandleIn cp of
  Just h -> h
  Nothing -> splineControlPointPos cp

-- | Build segments (index, p0, p1) without (!!)
segmentsFor :: [SplineControlPoint] -> Bool -> [(Int, SplineControlPoint, SplineControlPoint)]
segmentsFor [] _ = []
segmentsFor [_] _ = []
segmentsFor cps False = zip3 [0 ..] cps (tail cps)
segmentsFor cps True = zip3 [0 ..] cps (tail cps ++ [head cps])

-- | Find closest point on path; Left if &lt; 2 points or no point within threshold
findClosestPointOnPath
  :: Vec2
  -> [SplineControlPoint]
  -> Bool
  -> Double
  -> Either Text ClosestPointResult
findClosestPointOnPath pos cps closed threshold
  | length cps < 2 = Left "[SplineUtils] Cannot find closest point on path: Insufficient control points (minimum 2)."
  | otherwise =
      let segs = segmentsFor cps closed
          sampleSegment (i, p0, p1) =
            let h0 = getHandleOut p0
                h1 = getHandleIn p1
                pos0 = splineControlPointPos p0
                pos1 = splineControlPointPos p1
                sample t = evaluateBezier pos0 h0 h1 pos1 t
                ts = [0, 0.02 .. 1]
                candidates = [ (sample t, t, distance pos (sample t)) | t <- ts ]
                best (pt, t, d) (pt', t', d') = if d < d' then (pt, t, d) else (pt', t', d')
                bestOf = foldr1 best candidates
            in (i, bestOf)
          segmentBests = map sampleSegment segs
          globalBest (i, (pt, t, d)) (i', (pt', t', d')) =
            if d < d' then (i, (pt, t, d)) else (i', (pt', t', d'))
          (segIdx, (pt, t, d)) = foldr1 globalBest segmentBests
      in if d < threshold
           then Right (ClosestPointResult (vec2X pt) (vec2Y pt) segIdx t)
           else Left "[SplineUtils] No point on path within threshold."

-- | Find control point at position; Left if none within threshold
findPointAtPosition
  :: Vec2
  -> [SplineControlPoint]
  -> Double
  -> Either Text SplineControlPoint
findPointAtPosition pos cps threshold =
  case dropWhile (\cp -> distance pos (splineControlPointPos cp) >= threshold) cps of
    [] -> Left "[SplineUtils] No point at position within threshold."
    (p : _) -> Right p

-- ════════════════════════════════════════════════════════════════════════════
--                                                 // svg // path // generation
-- ════════════════════════════════════════════════════════════════════════════

-- | Generate SVG path 'd' for a spline
generateSplinePath :: [SplineControlPoint] -> Bool -> Text
generateSplinePath [] _ = ""
generateSplinePath [p] _ = "M " <> T.pack (show (vec2X (splineControlPointPos p))) <> "," <> T.pack (show (vec2Y (splineControlPointPos p)))
generateSplinePath cps closed =
  let segs = segmentsFor cps closed
      segmentToC (p0, p1) =
        let h0 = getHandleOut p0
            h1 = getHandleIn p1
            x0 = vec2X (splineControlPointPos p0)
            y0 = vec2Y (splineControlPointPos p0)
            x1 = vec2X (splineControlPointPos p1)
            y1 = vec2Y (splineControlPointPos p1)
            h0x = vec2X h0
            h0y = vec2Y h0
            h1x = vec2X h1
            h1y = vec2Y h1
        in " C " <> T.pack (show h0x) <> "," <> T.pack (show h0y) <> " " <> T.pack (show h1x) <> "," <> T.pack (show h1y) <> " " <> T.pack (show x1) <> "," <> T.pack (show y1)
      start = "M " <> T.pack (show (vec2X (splineControlPointPos (head cps)))) <> "," <> T.pack (show (vec2Y (splineControlPointPos (head cps))))
      middle = mconcat (map (\(_, p0, p1) -> segmentToC (p0, p1)) segs)
      end = if closed then " Z" else ""
  in start <> middle <> end

-- | Generate curve preview path from prev point to new point
generateCurvePreview
  :: SplineControlPoint
  -> Vec2
  -> Vec2
  -> Text
generateCurvePreview prevPoint newPoint dragPos =
  let dx = vec2X dragPos - vec2X newPoint
      dy = vec2Y dragPos - vec2Y newPoint
      (h1x, h1y) = case splineControlPointHandleOut prevPoint of
        Just h -> (vec2X h, vec2Y h)
        Nothing ->
          let dirX = vec2X newPoint - vec2X (splineControlPointPos prevPoint)
              dirY = vec2Y newPoint - vec2Y (splineControlPointPos prevPoint)
          in (vec2X (splineControlPointPos prevPoint) + dirX * 0.33, vec2Y (splineControlPointPos prevPoint) + dirY * 0.33)
      h2x = vec2X newPoint - dx
      h2y = vec2Y newPoint - dy
      x0 = vec2X (splineControlPointPos prevPoint)
      y0 = vec2Y (splineControlPointPos prevPoint)
      x1 = vec2X newPoint
      y1 = vec2Y newPoint
  in "M " <> T.pack (show x0) <> "," <> T.pack (show y0) <> " C " <> T.pack (show h1x) <> "," <> T.pack (show h1y) <> " " <> T.pack (show h2x) <> "," <> T.pack (show h2y) <> " " <> T.pack (show x1) <> "," <> T.pack (show y1)

-- ════════════════════════════════════════════════════════════════════════════
--                                              // coordinate // transformation
-- ════════════════════════════════════════════════════════════════════════════

-- | Transform point from layer space to composition space
transformPointToComp :: Vec2 -> LayerTransformValues -> Vec2
transformPointToComp point transform =
  let pos = layerTransformPosition transform
      scale = layerTransformScale transform
      rot = layerTransformRotation transform
      anchor = layerTransformAnchorPoint transform
      x = vec2X point - vec2X anchor
      y = vec2Y point - vec2Y anchor
      x1 = x * vec2X scale / 100
      y1 = y * vec2Y scale / 100
      rad = (rot * pi) / 180
      cosr = cos rad
      sinr = sin rad
      rx = x1 * cosr - y1 * sinr
      ry = x1 * sinr + y1 * cosr
  in Vec2 (rx + vec2X pos) (ry + vec2Y pos)

-- | Transform point from composition space to layer space (inverse)
transformPointToLayer :: Vec2 -> LayerTransformValues -> Vec2
transformPointToLayer point transform =
  let pos = layerTransformPosition transform
      scale = layerTransformScale transform
      rot = layerTransformRotation transform
      anchor = layerTransformAnchorPoint transform
      x = vec2X point - vec2X pos
      y = vec2Y point - vec2Y pos
      rad = (-rot * pi) / 180
      cosr = cos rad
      sinr = sin rad
      rx = x * cosr - y * sinr
      ry = x * sinr + y * cosr
      x1 = rx / (vec2X scale / 100)
      y1 = ry / (vec2Y scale / 100)
  in Vec2 (x1 + vec2X anchor) (y1 + vec2Y anchor)

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // path // smoothing
-- ════════════════════════════════════════════════════════════════════════════

safeAt :: [a] -> Int -> Maybe a
safeAt [] _ = Nothing
safeAt (x : _) 0 = Just x
safeAt (_ : xs) n | n > 0 = safeAt xs (n - 1)
safeAt _ _ = Nothing

-- | Smooth handles using Catmull-Rom style (tension 0.3 = natural). Returns Nothing if index out of range.
calculateSmoothHandles
  :: [SplineControlPoint]
  -> Int
  -> Double
  -> Maybe (Vec2, Vec2)
calculateSmoothHandles points index tension =
  let n = length points
      prevIdx = if index - 1 >= 0 then index - 1 else n - 1
      nextIdx = (index + 1) `mod` n
  in case (safeAt points prevIdx, safeAt points index, safeAt points nextIdx) of
       (Just prev, Just point, Just next) ->
         let dx = vec2X (splineControlPointPos next) - vec2X (splineControlPointPos prev)
             dy = vec2Y (splineControlPointPos next) - vec2Y (splineControlPointPos prev)
             distToPrev = distance (splineControlPointPos point) (splineControlPointPos prev)
             distToNext = distance (splineControlPointPos next) (splineControlPointPos point)
             handleLenIn = distToPrev * tension
             handleLenOut = distToNext * tension
             len = sqrt (dx * dx + dy * dy)
             (nx, ny) = if len > 0 then (dx / len, dy / len) else (0, 0)
             px = vec2X (splineControlPointPos point)
             py = vec2Y (splineControlPointPos point)
             handleIn = Vec2 (px - nx * handleLenIn) (py - ny * handleLenIn)
             handleOut = Vec2 (px + nx * handleLenOut) (py + ny * handleLenOut)
         in Just (handleIn, handleOut)
       _ -> Nothing

-- | Perpendicular distance from point to line segment
perpendicularDistance :: Vec2 -> Vec2 -> Vec2 -> Double
perpendicularDistance point lineStart lineEnd =
  let dx = vec2X lineEnd - vec2X lineStart
      dy = vec2Y lineEnd - vec2Y lineStart
      len = sqrt (dx * dx + dy * dy)
  in if len == 0
       then distance point lineStart
       else let t = max 0 (min 1 (((vec2X point - vec2X lineStart) * dx + (vec2Y point - vec2Y lineStart) * dy) / (len * len)))
                projX = vec2X lineStart + t * dx
                projY = vec2Y lineStart + t * dy
            in distance point (Vec2 projX projY)

-- | Simplify path using Ramer-Douglas-Peucker (no (!!) or partial head/last)
simplifyPath :: [Vec2] -> Double -> [Vec2]
simplifyPath pts _ | length pts <= 2 = pts
simplifyPath pts tolerance =
  case (pts, reverse pts) of
    (first : _, lastPt : _) ->
      let mid = take (length pts - 2) (drop 1 pts)
          indexed = zip [1 ..] mid
          (maxIndex, maxDist) = foldl (\(mi, md) (i, p) ->
            let d = perpendicularDistance p first lastPt
            in if d > md then (i, d) else (mi, md)) (1, 0) indexed
      in if maxDist > tolerance
           then let left = simplifyPath (take (maxIndex + 1) pts) tolerance
                    right = simplifyPath (drop maxIndex pts) tolerance
                in init left ++ right
           else [first, lastPt]
    _ -> pts
