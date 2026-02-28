-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // geometry // path // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path operations: append and flatten.
-- |
-- | Provides path composition and curve-to-line conversion.

module Hydrogen.Schema.Geometry.Path.Operations
  ( -- * Operations
    appendPath
  , flattenPath
  ) where

import Prelude
  ( (*)
  , (/)
  , (>)
  , max
  , map
  , (<>)
  )

import Data.Array (snoc, foldl) as Array
import Data.Int (toNumber, floor) as Int

import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY)
import Hydrogen.Schema.Geometry.Bezier 
  ( QuadBezier
  , CubicBezier
  , quadBezier
  , cubicBezier
  , quadPointAt
  , cubicPointAt
  , quadLength
  , cubicLength
  )
import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(MoveTo, LineTo, HLineTo, VLineTo, QuadTo, SmoothQuadTo, CubicTo, SmoothCurveTo, ArcTo, ClosePath)
  , Path(Path)
  , ArcParams
  )
import Hydrogen.Schema.Geometry.Path.Helpers
  ( approximateArcLength
  , arcPointAtT
  , rangeInts
  , ceil
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Append two paths.
-- |
-- | The second path is appended to the first. If the first path ends with
-- | ClosePath, it is preserved. The second path's initial MoveTo becomes
-- | part of the combined path.
appendPath :: Path -> Path -> Path
appendPath (Path cmds1) (Path cmds2) = Path (cmds1 <> cmds2)

-- | Flatten path to line segments.
-- |
-- | Converts all curves to line segments with specified tolerance.
-- | Tolerance is the maximum distance a line segment can deviate from the curve.
-- |
-- | Lower tolerance = more segments = more accurate
-- | Higher tolerance = fewer segments = more efficient
flattenPath :: Number -> Path -> Path
flattenPath tolerance (Path cmds) =
  let
    result = Array.foldl (flattenStep tolerance) { output: [], currentPos: point2D 0.0 0.0 } cmds
  in
    Path result.output

-- | Flatten one command.
flattenStep 
  :: Number 
  -> { output :: Array PathCommand, currentPos :: Point2D }
  -> PathCommand
  -> { output :: Array PathCommand, currentPos :: Point2D }
flattenStep tolerance acc cmd = case cmd of
  MoveTo p ->
    { output: Array.snoc acc.output (MoveTo p), currentPos: p }
  
  LineTo p ->
    { output: Array.snoc acc.output (LineTo p), currentPos: p }
  
  HLineTo x ->
    let newPos = point2D x (getY acc.currentPos)
    in { output: Array.snoc acc.output (LineTo newPos), currentPos: newPos }
  
  VLineTo y ->
    let newPos = point2D (getX acc.currentPos) y
    in { output: Array.snoc acc.output (LineTo newPos), currentPos: newPos }
  
  QuadTo control end ->
    let
      curve = quadBezier acc.currentPos control end
      segments = flattenQuadBezier tolerance curve
    in
      { output: acc.output <> segments, currentPos: end }
  
  SmoothQuadTo end ->
    -- Flatten smooth quad as line (control point inference not tracked)
    { output: Array.snoc acc.output (LineTo end), currentPos: end }
  
  CubicTo c1 c2 end ->
    let
      curve = cubicBezier acc.currentPos c1 c2 end
      segments = flattenCubicBezier tolerance curve
    in
      { output: acc.output <> segments, currentPos: end }
  
  SmoothCurveTo _ end ->
    -- Flatten smooth curve as line (control point inference not tracked)
    { output: Array.snoc acc.output (LineTo end), currentPos: end }
  
  ArcTo params ->
    let
      segments = flattenArc tolerance acc.currentPos params
    in
      { output: acc.output <> segments, currentPos: params.end }
  
  ClosePath ->
    { output: Array.snoc acc.output ClosePath, currentPos: acc.currentPos }

-- | Flatten quadratic Bezier to line segments.
flattenQuadBezier :: Number -> QuadBezier -> Array PathCommand
flattenQuadBezier tolerance curve =
  let
    -- Adaptive subdivision based on flatness
    numSegments = max 2 (estimateQuadSegments tolerance curve)
    step = 1.0 / Int.toNumber numSegments
    -- Generate points at regular intervals
    points = map (\i -> quadPointAt (Int.toNumber i * step) curve) (rangeInts 1 numSegments)
  in
    map LineTo points

-- | Flatten cubic Bezier to line segments.
flattenCubicBezier :: Number -> CubicBezier -> Array PathCommand
flattenCubicBezier tolerance curve =
  let
    numSegments = max 2 (estimateCubicSegments tolerance curve)
    step = 1.0 / Int.toNumber numSegments
    points = map (\i -> cubicPointAt (Int.toNumber i * step) curve) (rangeInts 1 numSegments)
  in
    map LineTo points

-- | Flatten arc to line segments.
-- |
-- | Uses tolerance to determine segment count — smaller tolerance means
-- | more segments for higher accuracy.
flattenArc :: Number -> Point2D -> ArcParams -> Array PathCommand
flattenArc tolerance start params =
  let
    -- Estimate arc length for segment calculation
    arcLen = approximateArcLength start params
    -- More segments for larger arcs and tighter tolerances
    baseSegments = if params.largeArc then 16 else 8
    -- Scale segments based on arc size and tolerance
    toleranceSegments = if tolerance > 0.0 
      then Int.floor (arcLen / tolerance)
      else baseSegments
    numSegments = max baseSegments toleranceSegments
    step = 1.0 / Int.toNumber numSegments
    points = map (\i -> arcPointAtT (Int.toNumber i * step) start params) (rangeInts 1 numSegments)
  in
    map LineTo points

-- | Estimate number of segments needed for quadratic Bezier.
estimateQuadSegments :: Number -> QuadBezier -> Int
estimateQuadSegments tolerance curve =
  let len = quadLength curve
  in max 2 (ceil (len / (tolerance * 4.0)))

-- | Estimate number of segments needed for cubic Bezier.
estimateCubicSegments :: Number -> CubicBezier -> Int
estimateCubicSegments tolerance curve =
  let len = cubicLength curve
  in max 2 (ceil (len / (tolerance * 3.0)))
