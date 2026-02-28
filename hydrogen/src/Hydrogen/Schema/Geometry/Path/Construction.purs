-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // geometry // path // construction
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path construction functions.
-- |
-- | Builders for creating and extending SVG paths.

module Hydrogen.Schema.Geometry.Path.Construction
  ( -- * Construction
    emptyPath
  , pathFromCommands
  , pathFromPoints
  , moveTo
  , lineTo
  , hLineTo
  , vLineTo
  , quadTo
  , smoothQuadTo
  , cubicTo
  , smoothCurveTo
  , arcTo
  , closePath
  ) where

import Prelude (map)

import Data.Array (snoc, cons, uncons) as Array
import Data.Maybe (Maybe(..))

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(MoveTo, LineTo, HLineTo, VLineTo, QuadTo, SmoothQuadTo, CubicTo, SmoothCurveTo, ArcTo, ClosePath)
  , Path(Path)
  , ArcParams
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Empty path with no commands.
emptyPath :: Path
emptyPath = Path []

-- | Create path from array of commands.
pathFromCommands :: Array PathCommand -> Path
pathFromCommands = Path

-- | Create path from array of points.
-- |
-- | First point becomes MoveTo, subsequent points become LineTo.
-- | Returns empty path if no points provided.
pathFromPoints :: Array Point2D -> Path
pathFromPoints points =
  case Array.uncons points of
    Nothing -> emptyPath
    Just { head: first, tail: rest } ->
      Path (Array.cons (MoveTo first) (map LineTo rest))

-- | Add MoveTo command to path.
moveTo :: Point2D -> Path -> Path
moveTo p (Path cmds) = Path (Array.snoc cmds (MoveTo p))

-- | Add LineTo command to path.
lineTo :: Point2D -> Path -> Path
lineTo p (Path cmds) = Path (Array.snoc cmds (LineTo p))

-- | Add HLineTo command to path.
-- |
-- | Horizontal line to the specified X coordinate.
-- | Y coordinate remains unchanged from current position.
hLineTo :: Number -> Path -> Path
hLineTo x (Path cmds) = Path (Array.snoc cmds (HLineTo x))

-- | Add VLineTo command to path.
-- |
-- | Vertical line to the specified Y coordinate.
-- | X coordinate remains unchanged from current position.
vLineTo :: Number -> Path -> Path
vLineTo y (Path cmds) = Path (Array.snoc cmds (VLineTo y))

-- | Add QuadTo command to path.
-- |
-- | Parameters: control point, end point.
quadTo :: Point2D -> Point2D -> Path -> Path
quadTo control end (Path cmds) = Path (Array.snoc cmds (QuadTo control end))

-- | Add SmoothQuadTo command to path.
-- |
-- | Smooth quadratic bezier where the control point is inferred as the
-- | reflection of the previous command's control point.
-- |
-- | Parameter: end point.
smoothQuadTo :: Point2D -> Path -> Path
smoothQuadTo end (Path cmds) = Path (Array.snoc cmds (SmoothQuadTo end))

-- | Add CubicTo command to path.
-- |
-- | Parameters: first control point, second control point, end point.
cubicTo :: Point2D -> Point2D -> Point2D -> Path -> Path
cubicTo c1 c2 end (Path cmds) = Path (Array.snoc cmds (CubicTo c1 c2 end))

-- | Add SmoothCurveTo command to path.
-- |
-- | Smooth cubic bezier where the first control point is inferred as the
-- | reflection of the previous command's second control point.
-- |
-- | Parameters: second control point, end point.
smoothCurveTo :: Point2D -> Point2D -> Path -> Path
smoothCurveTo c2 end (Path cmds) = Path (Array.snoc cmds (SmoothCurveTo c2 end))

-- | Add ArcTo command to path.
arcTo :: ArcParams -> Path -> Path
arcTo params (Path cmds) = Path (Array.snoc cmds (ArcTo params))

-- | Add ClosePath command to path.
closePath :: Path -> Path
closePath (Path cmds) = Path (Array.snoc cmds ClosePath)
