-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // geometry // path // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal helper functions for path operations.
-- |
-- | Provides distance calculations, arc approximations, and utility functions.

module Hydrogen.Schema.Geometry.Path.Helpers
  ( -- * Distance
    distance
  
    -- * Arc Helpers
  , approximateArcLength
  , arcPointAtT
  
    -- * Math Helpers
  , absNum
  , infinity
  , negInfinity
  , rangeNumbers
  , rangeInts
  , foldMin
  , foldMax
  , ceil
  ) where

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , negate
  , min
  , max
  )

import Data.Array (cons, foldl) as Array
import Data.Number (sqrt)
import Data.Int (toNumber, floor) as Int

import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY)
import Hydrogen.Schema.Geometry.Path.Types (ArcParams)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance between two points.
distance :: Point2D -> Point2D -> Number
distance p1 p2 =
  let
    dx = getX p2 - getX p1
    dy = getY p2 - getY p1
  in
    sqrt (dx * dx + dy * dy)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // arc helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximate arc length by chord + sagitta method.
-- |
-- | Uses the average radius to estimate arc curvature correction.
approximateArcLength :: Point2D -> ArcParams -> Number
approximateArcLength start params =
  -- Approximation: use chord length scaled by ellipse eccentricity factor
  let
    chord = distance start params.end
    avgRadius = (params.rx + params.ry) / 2.0
    -- Eccentricity factor: how much the ellipse deviates from circle
    eccentricityFactor = if avgRadius > 0.0 
      then (params.rx + params.ry) / (2.0 * avgRadius)
      else 1.0
    -- Large arcs traverse more of the ellipse perimeter
    arcFactor = if params.largeArc then 1.57 else 1.1
  in
    chord * arcFactor * eccentricityFactor

-- | Point on elliptical arc at parameter t ∈ [0, 1].
-- |
-- | This is an approximation using linear interpolation of the endpoint parameterization.
-- | For precise arc evaluation, see the SVG arc implementation notes.
arcPointAtT :: Number -> Point2D -> ArcParams -> Point2D
arcPointAtT t start params =
  -- Linear interpolation as approximation (actual arc is more complex)
  let
    x = getX start + t * (getX params.end - getX start)
    y = getY start + t * (getY params.end - getY start)
  in
    point2D x y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // math helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute value of a number.
absNum :: Number -> Number
absNum n = if n < 0.0 then negate n else n

-- | Large positive number (approximation of infinity).
infinity :: Number
infinity = 1.0e308

-- | Large negative number.
negInfinity :: Number
negInfinity = negate 1.0e308

-- | Generate integer range [start, end] as Numbers.
-- |
-- | Used for sampling curves.
rangeNumbers :: Int -> Int -> Array Number
rangeNumbers start end = 
  if start > end then []
  else Array.cons (Int.toNumber start) (rangeNumbers (start + 1) end)

-- | Generate integer range [start, end].
rangeInts :: Int -> Int -> Array Int
rangeInts start end =
  if start > end then []
  else Array.cons start (rangeInts (start + 1) end)

-- | Fold to find minimum.
foldMin :: Number -> Array Number -> Number
foldMin initial arr = Array.foldl min initial arr

-- | Fold to find maximum.
foldMax :: Number -> Array Number -> Number
foldMax initial arr = Array.foldl max initial arr

-- | Ceiling function (round up).
ceil :: Number -> Int
ceil n = 
  let floored = Int.floor n
  in if Int.toNumber floored < n then floored + 1 else floored
