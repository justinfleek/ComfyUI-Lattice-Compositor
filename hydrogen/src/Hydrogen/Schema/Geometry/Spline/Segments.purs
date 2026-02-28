-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // geometry // spline // segments
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline Segments: Segment counting and extraction.
-- |
-- | Each spline is composed of multiple segments, where each segment
-- | is defined by 4 control points.

module Hydrogen.Schema.Geometry.Spline.Segments
  ( -- * Catmull-Rom Segments
    catmullRomSegmentCount
  , catmullRomSegment
  
    -- * B-Spline Segments
  , bSplineSegmentCount
  , bSplineSegment
  ) where

import Prelude
  ( (+)
  , (-)
  , (<)
  , (>=)
  , (||)
  , show
  )

import Data.Array (length, (!!))
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Spline.Types 
  ( CatmullRomSpline(CatmullRomSpline)
  , BSpline(BSpline)
  )
import Hydrogen.Schema.Geometry.Spline.Helpers (wrapIndex)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // catmull-rom segments
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of segments in Catmull-Rom spline.
-- |
-- | For open spline with n points: n - 3 segments
-- | For closed spline with n points: n segments
catmullRomSegmentCount :: CatmullRomSpline -> Int
catmullRomSegmentCount (CatmullRomSpline s) =
  let n = length s.points
  in if s.closed then n else n - 3

-- | Get the 4 control points for segment i of Catmull-Rom spline.
-- |
-- | Returns Nothing if index out of bounds.
catmullRomSegment :: Int -> CatmullRomSpline -> Maybe { p0 :: Point2D, p1 :: Point2D, p2 :: Point2D, p3 :: Point2D }
catmullRomSegment i (CatmullRomSpline s) =
  let
    n = length s.points
    segCount = if s.closed then n else n - 3
  in
    if i < 0 || i >= segCount then Nothing
    else if s.closed then
      -- Closed: wrap around
      let
        i0 = i
        i1 = wrapIndex (i + 1) n
        i2 = wrapIndex (i + 2) n
        i3 = wrapIndex (i + 3) n
      in
        case { p0: s.points !! i0, p1: s.points !! i1, p2: s.points !! i2, p3: s.points !! i3 } of
          { p0: Just pp0, p1: Just pp1, p2: Just pp2, p3: Just pp3 } ->
            Just { p0: pp0, p1: pp1, p2: pp2, p3: pp3 }
          _ -> Nothing
    else
      -- Open: segment i uses points i, i+1, i+2, i+3
      case { p0: s.points !! i, p1: s.points !! (i+1), p2: s.points !! (i+2), p3: s.points !! (i+3) } of
        { p0: Just pp0, p1: Just pp1, p2: Just pp2, p3: Just pp3 } ->
          Just { p0: pp0, p1: pp1, p2: pp2, p3: pp3 }
        _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // b-spline segments
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of segments in B-spline.
-- |
-- | For open spline with n points: n - 3 segments
-- | For closed spline with n points: n segments
bSplineSegmentCount :: BSpline -> Int
bSplineSegmentCount (BSpline s) =
  let n = length s.points
  in if s.closed then n else n - 3

-- | Get the 4 control points for segment i of B-spline.
bSplineSegment :: Int -> BSpline -> Maybe { p0 :: Point2D, p1 :: Point2D, p2 :: Point2D, p3 :: Point2D }
bSplineSegment i (BSpline s) =
  let
    n = length s.points
    segCount = if s.closed then n else n - 3
  in
    if i < 0 || i >= segCount then Nothing
    else if s.closed then
      let
        i0 = i
        i1 = wrapIndex (i + 1) n
        i2 = wrapIndex (i + 2) n
        i3 = wrapIndex (i + 3) n
      in
        case { p0: s.points !! i0, p1: s.points !! i1, p2: s.points !! i2, p3: s.points !! i3 } of
          { p0: Just pp0, p1: Just pp1, p2: Just pp2, p3: Just pp3 } ->
            Just { p0: pp0, p1: pp1, p2: pp2, p3: pp3 }
          _ -> Nothing
    else
      case { p0: s.points !! i, p1: s.points !! (i+1), p2: s.points !! (i+2), p3: s.points !! (i+3) } of
        { p0: Just pp0, p1: Just pp1, p2: Just pp2, p3: Just pp3 } ->
          Just { p0: pp0, p1: pp1, p2: pp2, p3: pp3 }
        _ -> Nothing
