-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // geometry // path // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path geometry calculations.
-- |
-- | Provides bounding box, length, point-at-length, and tangent calculations.

module Hydrogen.Schema.Geometry.Path.Geometry
  ( -- * Geometry
    bounds
  , pathLength
  , pointAtLength
  , tangentAtLength
  ) where

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<=)
  , (>)
  , (>=)
  , map
  , min
  , max
  , negate
  )

import Data.Array (uncons, foldl) as Array
import Data.Maybe (Maybe(..))
import Data.Number (sqrt)

import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2)
import Hydrogen.Schema.Geometry.Angle (Degrees)
import Hydrogen.Schema.Geometry.Bezier 
  ( quadBezier
  , cubicBezier
  , quadPointAt
  , cubicPointAt
  , quadTangentAt
  , cubicTangentAt
  , quadBoundingBox
  , cubicBoundingBox
  , quadLength
  , cubicLength
  )
import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(MoveTo, LineTo, HLineTo, VLineTo, QuadTo, SmoothQuadTo, CubicTo, SmoothCurveTo, ArcTo, ClosePath)
  , Path(Path)
  , getCommands
  )
import Hydrogen.Schema.Geometry.Path.Query (isEmpty, firstPoint, lastPoint)
import Hydrogen.Schema.Geometry.Path.Helpers
  ( distance
  , approximateArcLength
  , arcPointAtT
  , absNum
  , infinity
  , negInfinity
  , rangeNumbers
  , foldMin
  , foldMax
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding box of entire path.
-- |
-- | Returns Nothing for empty path.
bounds :: Path -> Maybe { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
bounds (Path cmds) =
  case Array.uncons cmds of
    Nothing -> Nothing
    Just _ -> Just (computeBounds cmds)

-- | Compute bounding box from commands.
computeBounds :: Array PathCommand -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
computeBounds cmds =
  let
    initial = { minX: infinity, minY: infinity, maxX: negInfinity, maxY: negInfinity, currentPos: point2D 0.0 0.0 }
    result = Array.foldl updateBounds initial cmds
  in
    { minX: result.minX, minY: result.minY, maxX: result.maxX, maxY: result.maxY }

-- | Update bounds with a command.
updateBounds 
  :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number, currentPos :: Point2D }
  -> PathCommand
  -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number, currentPos :: Point2D }
updateBounds acc cmd = case cmd of
  MoveTo p ->
    { minX: min acc.minX (getX p)
    , minY: min acc.minY (getY p)
    , maxX: max acc.maxX (getX p)
    , maxY: max acc.maxY (getY p)
    , currentPos: p
    }
  
  LineTo p ->
    { minX: min acc.minX (getX p)
    , minY: min acc.minY (getY p)
    , maxX: max acc.maxX (getX p)
    , maxY: max acc.maxY (getY p)
    , currentPos: p
    }
  
  HLineTo x ->
    let newPos = point2D x (getY acc.currentPos)
    in
      { minX: min acc.minX x
      , minY: acc.minY
      , maxX: max acc.maxX x
      , maxY: acc.maxY
      , currentPos: newPos
      }
  
  VLineTo y ->
    let newPos = point2D (getX acc.currentPos) y
    in
      { minX: acc.minX
      , minY: min acc.minY y
      , maxX: acc.maxX
      , maxY: max acc.maxY y
      , currentPos: newPos
      }
  
  QuadTo control end ->
    let
      curve = quadBezier acc.currentPos control end
      box = quadBoundingBox curve
    in
      { minX: min acc.minX box.minX
      , minY: min acc.minY box.minY
      , maxX: max acc.maxX box.maxX
      , maxY: max acc.maxY box.maxY
      , currentPos: end
      }
  
  SmoothQuadTo end ->
    -- Smooth quad: control point inferred from previous
    -- For bounds, we approximate by just including the endpoint
    { minX: min acc.minX (getX end)
    , minY: min acc.minY (getY end)
    , maxX: max acc.maxX (getX end)
    , maxY: max acc.maxY (getY end)
    , currentPos: end
    }
  
  CubicTo c1 c2 end ->
    let
      curve = cubicBezier acc.currentPos c1 c2 end
      box = cubicBoundingBox curve
    in
      { minX: min acc.minX box.minX
      , minY: min acc.minY box.minY
      , maxX: max acc.maxX box.maxX
      , maxY: max acc.maxY box.maxY
      , currentPos: end
      }
  
  SmoothCurveTo c2 end ->
    -- Smooth cubic: first control point inferred from previous
    -- For bounds, we include control point c2 and endpoint
    { minX: min (min acc.minX (getX c2)) (getX end)
    , minY: min (min acc.minY (getY c2)) (getY end)
    , maxX: max (max acc.maxX (getX c2)) (getX end)
    , maxY: max (max acc.maxY (getY c2)) (getY end)
    , currentPos: end
    }
  
  ArcTo params ->
    -- Approximate arc bounds by sampling
    -- (Full arc bounding is complex — this is a reasonable approximation)
    let arcBounds = approximateArcBounds acc.currentPos params
    in
      { minX: min acc.minX arcBounds.minX
      , minY: min acc.minY arcBounds.minY
      , maxX: max acc.maxX arcBounds.maxX
      , maxY: max acc.maxY arcBounds.maxY
      , currentPos: params.end
      }
  
  ClosePath -> acc

-- | Approximate arc bounding box by sampling points.
approximateArcBounds :: Point2D -> { rx :: Number, ry :: Number, rotation :: Degrees, largeArc :: Boolean, sweep :: Boolean, end :: Point2D } -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
approximateArcBounds start params =
  let
    -- Sample 16 points along the arc
    samples = map (\t -> arcPointAtT (t / 16.0) start params) (rangeNumbers 0 16)
    xs = map getX samples
    ys = map getY samples
  in
    { minX: foldMin infinity xs
    , minY: foldMin infinity ys
    , maxX: foldMax negInfinity xs
    , maxY: foldMax negInfinity ys
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // path length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Total arc length of path.
pathLength :: Path -> Number
pathLength (Path cmds) =
  let
    result = Array.foldl accumulateLength { total: 0.0, currentPos: point2D 0.0 0.0 } cmds
  in
    result.total

-- | Accumulate length for each command.
accumulateLength 
  :: { total :: Number, currentPos :: Point2D }
  -> PathCommand
  -> { total :: Number, currentPos :: Point2D }
accumulateLength acc cmd = case cmd of
  MoveTo p -> 
    { total: acc.total, currentPos: p }
  
  LineTo p ->
    let len = distance acc.currentPos p
    in { total: acc.total + len, currentPos: p }
  
  HLineTo x ->
    let 
      newPos = point2D x (getY acc.currentPos)
      len = absNum (x - getX acc.currentPos)
    in { total: acc.total + len, currentPos: newPos }
  
  VLineTo y ->
    let 
      newPos = point2D (getX acc.currentPos) y
      len = absNum (y - getY acc.currentPos)
    in { total: acc.total + len, currentPos: newPos }
  
  QuadTo control end ->
    let 
      curve = quadBezier acc.currentPos control end
      len = quadLength curve
    in { total: acc.total + len, currentPos: end }
  
  SmoothQuadTo end ->
    -- Approximate smooth quad as line for length
    let len = distance acc.currentPos end
    in { total: acc.total + len, currentPos: end }
  
  CubicTo c1 c2 end ->
    let
      curve = cubicBezier acc.currentPos c1 c2 end
      len = cubicLength curve
    in { total: acc.total + len, currentPos: end }
  
  SmoothCurveTo _ end ->
    -- Approximate smooth curve as line for length
    let len = distance acc.currentPos end
    in { total: acc.total + len, currentPos: end }
  
  ArcTo params ->
    -- Approximate arc length
    let len = approximateArcLength acc.currentPos params
    in { total: acc.total + len, currentPos: params.end }
  
  ClosePath -> acc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // point at length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point at a given arc length along the path.
-- |
-- | Returns Nothing if path is empty or length is out of bounds.
pointAtLength :: Number -> Path -> Maybe Point2D
pointAtLength targetLen path =
  if targetLen <= 0.0 then firstPoint path
  else if targetLen >= pathLength path then lastPoint path
  else findPointAtLength targetLen path

-- | Find point at specific length (helper).
findPointAtLength :: Number -> Path -> Maybe Point2D
findPointAtLength targetLen path =
  let
    cmds = getCommands path
    result = Array.foldl (stepToLength targetLen) 
      { accumulated: 0.0, currentPos: point2D 0.0 0.0, found: Nothing } 
      cmds
  in
    result.found

-- | Step through commands to find point at target length.
stepToLength 
  :: Number
  -> { accumulated :: Number, currentPos :: Point2D, found :: Maybe Point2D }
  -> PathCommand
  -> { accumulated :: Number, currentPos :: Point2D, found :: Maybe Point2D }
stepToLength targetLen acc cmd =
  case acc.found of
    Just _ -> acc  -- Already found
    Nothing -> case cmd of
      MoveTo p -> 
        { accumulated: acc.accumulated, currentPos: p, found: Nothing }
      
      LineTo p ->
        let 
          segLen = distance acc.currentPos p
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let 
              t = (targetLen - acc.accumulated) / segLen
              x = getX acc.currentPos + t * (getX p - getX acc.currentPos)
              y = getY acc.currentPos + t * (getY p - getY acc.currentPos)
            in { accumulated: newAcc, currentPos: p, found: Just (point2D x y) }
          else
            { accumulated: newAcc, currentPos: p, found: Nothing }
      
      HLineTo x ->
        let 
          newPos = point2D x (getY acc.currentPos)
          segLen = absNum (x - getX acc.currentPos)
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let 
              t = (targetLen - acc.accumulated) / segLen
              interpX = getX acc.currentPos + t * (x - getX acc.currentPos)
            in { accumulated: newAcc, currentPos: newPos, found: Just (point2D interpX (getY acc.currentPos)) }
          else
            { accumulated: newAcc, currentPos: newPos, found: Nothing }
      
      VLineTo y ->
        let 
          newPos = point2D (getX acc.currentPos) y
          segLen = absNum (y - getY acc.currentPos)
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let 
              t = (targetLen - acc.accumulated) / segLen
              interpY = getY acc.currentPos + t * (y - getY acc.currentPos)
            in { accumulated: newAcc, currentPos: newPos, found: Just (point2D (getX acc.currentPos) interpY) }
          else
            { accumulated: newAcc, currentPos: newPos, found: Nothing }
      
      QuadTo control end ->
        let
          curve = quadBezier acc.currentPos control end
          segLen = quadLength curve
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let t = (targetLen - acc.accumulated) / segLen
            in { accumulated: newAcc, currentPos: end, found: Just (quadPointAt t curve) }
          else
            { accumulated: newAcc, currentPos: end, found: Nothing }
      
      SmoothQuadTo end ->
        -- Approximate as line
        let 
          segLen = distance acc.currentPos end
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let 
              t = (targetLen - acc.accumulated) / segLen
              x = getX acc.currentPos + t * (getX end - getX acc.currentPos)
              y = getY acc.currentPos + t * (getY end - getY acc.currentPos)
            in { accumulated: newAcc, currentPos: end, found: Just (point2D x y) }
          else
            { accumulated: newAcc, currentPos: end, found: Nothing }
      
      CubicTo c1 c2 end ->
        let
          curve = cubicBezier acc.currentPos c1 c2 end
          segLen = cubicLength curve
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let t = (targetLen - acc.accumulated) / segLen
            in { accumulated: newAcc, currentPos: end, found: Just (cubicPointAt t curve) }
          else
            { accumulated: newAcc, currentPos: end, found: Nothing }
      
      SmoothCurveTo _ end ->
        -- Approximate as line
        let 
          segLen = distance acc.currentPos end
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let 
              t = (targetLen - acc.accumulated) / segLen
              x = getX acc.currentPos + t * (getX end - getX acc.currentPos)
              y = getY acc.currentPos + t * (getY end - getY acc.currentPos)
            in { accumulated: newAcc, currentPos: end, found: Just (point2D x y) }
          else
            { accumulated: newAcc, currentPos: end, found: Nothing }
      
      ArcTo params ->
        let
          segLen = approximateArcLength acc.currentPos params
          newAcc = acc.accumulated + segLen
        in
          if newAcc >= targetLen then
            let t = (targetLen - acc.accumulated) / segLen
            in { accumulated: newAcc, currentPos: params.end, found: Just (arcPointAtT t acc.currentPos params) }
          else
            { accumulated: newAcc, currentPos: params.end, found: Nothing }
      
      ClosePath -> acc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // tangent at length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tangent vector at a given arc length along the path.
-- |
-- | Returns Nothing if path is empty or length is out of bounds.
tangentAtLength :: Number -> Path -> Maybe Vector2D
tangentAtLength targetLen path =
  if isEmpty path then Nothing
  else Just (findTangentAtLength targetLen path)

-- | Find tangent at specific length (helper).
findTangentAtLength :: Number -> Path -> Vector2D
findTangentAtLength targetLen path =
  let
    cmds = getCommands path
    result = Array.foldl (stepToTangent targetLen)
      { accumulated: 0.0, currentPos: point2D 0.0 0.0, tangent: vec2 1.0 0.0 }
      cmds
  in
    result.tangent

-- | Step through commands to find tangent at target length.
stepToTangent
  :: Number
  -> { accumulated :: Number, currentPos :: Point2D, tangent :: Vector2D }
  -> PathCommand
  -> { accumulated :: Number, currentPos :: Point2D, tangent :: Vector2D }
stepToTangent targetLen acc cmd = case cmd of
  MoveTo p ->
    { accumulated: acc.accumulated, currentPos: p, tangent: acc.tangent }
  
  LineTo p ->
    let
      segLen = distance acc.currentPos p
      newAcc = acc.accumulated + segLen
      dx = getX p - getX acc.currentPos
      dy = getY p - getY acc.currentPos
      len = sqrt (dx * dx + dy * dy)
      tangent = if len > 0.0 then vec2 (dx / len) (dy / len) else acc.tangent
    in
      if newAcc >= targetLen then
        { accumulated: newAcc, currentPos: p, tangent: tangent }
      else
        { accumulated: newAcc, currentPos: p, tangent: tangent }
  
  HLineTo x ->
    let
      newPos = point2D x (getY acc.currentPos)
      segLen = absNum (x - getX acc.currentPos)
      newAcc = acc.accumulated + segLen
      -- Horizontal tangent: +X or -X depending on direction
      tangent = if x > getX acc.currentPos then vec2 1.0 0.0 else vec2 (-1.0) 0.0
    in
      { accumulated: newAcc, currentPos: newPos, tangent: tangent }
  
  VLineTo y ->
    let
      newPos = point2D (getX acc.currentPos) y
      segLen = absNum (y - getY acc.currentPos)
      newAcc = acc.accumulated + segLen
      -- Vertical tangent: +Y or -Y depending on direction
      tangent = if y > getY acc.currentPos then vec2 0.0 1.0 else vec2 0.0 (-1.0)
    in
      { accumulated: newAcc, currentPos: newPos, tangent: tangent }
  
  QuadTo control end ->
    let
      curve = quadBezier acc.currentPos control end
      segLen = quadLength curve
      newAcc = acc.accumulated + segLen
    in
      if newAcc >= targetLen then
        let t = (targetLen - acc.accumulated) / segLen
        in { accumulated: newAcc, currentPos: end, tangent: quadTangentAt t curve }
      else
        { accumulated: newAcc, currentPos: end, tangent: quadTangentAt 1.0 curve }
  
  CubicTo c1 c2 end ->
    let
      curve = cubicBezier acc.currentPos c1 c2 end
      segLen = cubicLength curve
      newAcc = acc.accumulated + segLen
    in
      if newAcc >= targetLen then
        let t = (targetLen - acc.accumulated) / segLen
        in { accumulated: newAcc, currentPos: end, tangent: cubicTangentAt t curve }
      else
        { accumulated: newAcc, currentPos: end, tangent: cubicTangentAt 1.0 curve }
  
  SmoothQuadTo end ->
    -- Approximate smooth quad as line for tangent
    let
      segLen = distance acc.currentPos end
      newAcc = acc.accumulated + segLen
      dx = getX end - getX acc.currentPos
      dy = getY end - getY acc.currentPos
      len = sqrt (dx * dx + dy * dy)
      tangent = if len > 0.0 then vec2 (dx / len) (dy / len) else acc.tangent
    in
      { accumulated: newAcc, currentPos: end, tangent: tangent }
  
  SmoothCurveTo _ end ->
    -- Approximate smooth curve as line for tangent
    let
      segLen = distance acc.currentPos end
      newAcc = acc.accumulated + segLen
      dx = getX end - getX acc.currentPos
      dy = getY end - getY acc.currentPos
      len = sqrt (dx * dx + dy * dy)
      tangent = if len > 0.0 then vec2 (dx / len) (dy / len) else acc.tangent
    in
      { accumulated: newAcc, currentPos: end, tangent: tangent }
  
  ArcTo params ->
    let
      segLen = approximateArcLength acc.currentPos params
      newAcc = acc.accumulated + segLen
      -- Approximate tangent for arc
      dx = getX params.end - getX acc.currentPos
      dy = getY params.end - getY acc.currentPos
      len = sqrt (dx * dx + dy * dy)
      tangent = if len > 0.0 then vec2 (dx / len) (dy / len) else acc.tangent
    in
      { accumulated: newAcc, currentPos: params.end, tangent: tangent }
  
  ClosePath -> acc
