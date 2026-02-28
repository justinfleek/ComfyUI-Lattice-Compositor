-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // geometry // path // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path transformation functions.
-- |
-- | Provides reverse, translate, scale, and rotate operations.

module Hydrogen.Schema.Geometry.Path.Transform
  ( -- * Transformation
    reversePath
  , translatePath
  , scalePath
  , rotatePath
  ) where

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , map
  )

import Data.Array (snoc, uncons, init, last, reverse, foldl) as Array
import Data.Maybe (Maybe(..))
import Data.Number (sin, cos, pi)

import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY)
import Hydrogen.Schema.Geometry.Angle (Degrees, unwrapDegrees)
import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(MoveTo, LineTo, HLineTo, VLineTo, QuadTo, SmoothQuadTo, CubicTo, SmoothCurveTo, ArcTo, ClosePath)
  , Path(Path)
  )
import Hydrogen.Schema.Geometry.Path.Construction (emptyPath, pathFromPoints, closePath)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // transformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reverse the direction of a path.
-- |
-- | The path will traverse in the opposite direction.
-- | ClosePath commands are preserved at the end.
-- |
-- | Note: The first command should be MoveTo, which determines the starting
-- | point. When reversed, the last point becomes the new starting point.
reversePath :: Path -> Path
reversePath (Path cmds) =
  case Array.uncons cmds of
    Nothing -> emptyPath
    Just { head: firstCmd, tail: restCmds } ->
      let
        -- Check if path is closed
        endsWithClose = case Array.last cmds of
          Just ClosePath -> true
          _ -> false
        
        -- Get starting point from first command (should be MoveTo)
        startPoint = case firstCmd of
          MoveTo p -> Just p
          _ -> Nothing
        
        -- Remove ClosePath if present for reversal, and skip first MoveTo
        toReverse = if endsWithClose 
          then case Array.init restCmds of
            Just init' -> init'
            Nothing -> []
          else restCmds
        
        -- Collect all points in order (excluding the MoveTo start)
        points = collectPoints toReverse
        
        -- Add starting point to end if present
        allPoints = case startPoint of
          Just sp -> Array.snoc points sp
          Nothing -> points
        
        -- Reverse the points and rebuild path
        reversedPoints = Array.reverse allPoints
        
        -- Build new path from reversed points
        newPath = pathFromPoints reversedPoints
      in
        if endsWithClose then closePath newPath else newPath

-- | Collect all points from commands in order.
-- |
-- | Note: HLineTo and VLineTo only provide partial coordinates, so they
-- | cannot be included without knowing the current position context.
-- | They are skipped in this simplified collection.
collectPoints :: Array PathCommand -> Array Point2D
collectPoints cmds = Array.foldl addPoint [] cmds
  where
    addPoint acc cmd = case cmd of
      MoveTo p -> Array.snoc acc p
      LineTo p -> Array.snoc acc p
      HLineTo _ -> acc  -- Partial coordinate, skip
      VLineTo _ -> acc  -- Partial coordinate, skip
      QuadTo _ p -> Array.snoc acc p
      SmoothQuadTo p -> Array.snoc acc p
      CubicTo _ _ p -> Array.snoc acc p
      SmoothCurveTo _ p -> Array.snoc acc p
      ArcTo params -> Array.snoc acc params.end
      ClosePath -> acc

-- | Translate path by offset.
translatePath :: Number -> Number -> Path -> Path
translatePath dx dy (Path cmds) = Path (map (translateCommand dx dy) cmds)

-- | Translate a single command.
translateCommand :: Number -> Number -> PathCommand -> PathCommand
translateCommand dx dy cmd = case cmd of
  MoveTo p -> MoveTo (translatePoint dx dy p)
  LineTo p -> LineTo (translatePoint dx dy p)
  HLineTo x -> HLineTo (x + dx)
  VLineTo y -> VLineTo (y + dy)
  QuadTo c e -> QuadTo (translatePoint dx dy c) (translatePoint dx dy e)
  SmoothQuadTo e -> SmoothQuadTo (translatePoint dx dy e)
  CubicTo c1 c2 e -> CubicTo (translatePoint dx dy c1) (translatePoint dx dy c2) (translatePoint dx dy e)
  SmoothCurveTo c2 e -> SmoothCurveTo (translatePoint dx dy c2) (translatePoint dx dy e)
  ArcTo params -> ArcTo (params { end = translatePoint dx dy params.end })
  ClosePath -> ClosePath

-- | Translate a point.
translatePoint :: Number -> Number -> Point2D -> Point2D
translatePoint dx dy p = point2D (getX p + dx) (getY p + dy)

-- | Scale path from origin.
scalePath :: Number -> Number -> Path -> Path
scalePath sx sy (Path cmds) = Path (map (scaleCommand sx sy) cmds)

-- | Scale a single command.
scaleCommand :: Number -> Number -> PathCommand -> PathCommand
scaleCommand sx sy cmd = case cmd of
  MoveTo p -> MoveTo (scalePoint sx sy p)
  LineTo p -> LineTo (scalePoint sx sy p)
  HLineTo x -> HLineTo (x * sx)
  VLineTo y -> VLineTo (y * sy)
  QuadTo c e -> QuadTo (scalePoint sx sy c) (scalePoint sx sy e)
  SmoothQuadTo e -> SmoothQuadTo (scalePoint sx sy e)
  CubicTo c1 c2 e -> CubicTo (scalePoint sx sy c1) (scalePoint sx sy c2) (scalePoint sx sy e)
  SmoothCurveTo c2 e -> SmoothCurveTo (scalePoint sx sy c2) (scalePoint sx sy e)
  ArcTo params -> ArcTo (params 
    { rx = params.rx * sx
    , ry = params.ry * sy
    , end = scalePoint sx sy params.end 
    })
  ClosePath -> ClosePath

-- | Scale a point from origin.
scalePoint :: Number -> Number -> Point2D -> Point2D
scalePoint sx sy p = point2D (getX p * sx) (getY p * sy)

-- | Rotate path around origin by angle.
rotatePath :: Degrees -> Path -> Path
rotatePath angle (Path cmds) = 
  let 
    rad = unwrapDegrees angle * pi / 180.0
    cosA = cos rad
    sinA = sin rad
  in 
    Path (map (rotateCommand cosA sinA) cmds)

-- | Rotate a single command.
-- |
-- | Note: HLineTo and VLineTo are converted to LineTo since rotation
-- | changes their direction (they're no longer purely horizontal/vertical).
rotateCommand :: Number -> Number -> PathCommand -> PathCommand
rotateCommand cosA sinA cmd = case cmd of
  MoveTo p -> MoveTo (rotatePoint cosA sinA p)
  LineTo p -> LineTo (rotatePoint cosA sinA p)
  HLineTo x -> LineTo (rotatePoint cosA sinA (point2D x 0.0))
  VLineTo y -> LineTo (rotatePoint cosA sinA (point2D 0.0 y))
  QuadTo c e -> QuadTo (rotatePoint cosA sinA c) (rotatePoint cosA sinA e)
  SmoothQuadTo e -> SmoothQuadTo (rotatePoint cosA sinA e)
  CubicTo c1 c2 e -> CubicTo (rotatePoint cosA sinA c1) (rotatePoint cosA sinA c2) (rotatePoint cosA sinA e)
  SmoothCurveTo c2 e -> SmoothCurveTo (rotatePoint cosA sinA c2) (rotatePoint cosA sinA e)
  ArcTo params -> ArcTo (params { end = rotatePoint cosA sinA params.end })
  ClosePath -> ClosePath

-- | Rotate a point around origin.
rotatePoint :: Number -> Number -> Point2D -> Point2D
rotatePoint cosA sinA p =
  let
    x = getX p
    y = getY p
  in
    point2D (x * cosA - y * sinA) (x * sinA + y * cosA)
