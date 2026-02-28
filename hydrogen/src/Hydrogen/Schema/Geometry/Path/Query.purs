-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // geometry // path // query
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path query functions.
-- |
-- | Functions to inspect path state and extract information.

module Hydrogen.Schema.Geometry.Path.Query
  ( -- * Query
    isEmpty
  , commandCount
  , isClosed
  , firstPoint
  , lastPoint
  ) where

import Prelude (($))

import Data.Array (head, last, length, null) as Array
import Data.Maybe (Maybe(..))

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(MoveTo, LineTo, HLineTo, VLineTo, QuadTo, SmoothQuadTo, CubicTo, SmoothCurveTo, ArcTo, ClosePath)
  , Path(Path)
  , getCommands
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // query
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is the path empty (no commands)?
isEmpty :: Path -> Boolean
isEmpty (Path cmds) = Array.null cmds

-- | Number of commands in path.
commandCount :: Path -> Int
commandCount (Path cmds) = Array.length cmds

-- | Does the path end with ClosePath?
isClosed :: Path -> Boolean
isClosed (Path cmds) =
  case Array.last cmds of
    Nothing -> false
    Just ClosePath -> true
    Just _ -> false

-- | Get the first point of the path (from MoveTo).
-- |
-- | Returns Nothing if path is empty or doesn't start with MoveTo.
firstPoint :: Path -> Maybe Point2D
firstPoint (Path cmds) =
  case Array.head cmds of
    Just (MoveTo p) -> Just p
    _ -> Nothing

-- | Get the last point of the path.
-- |
-- | Returns the endpoint of the last drawing command.
-- | Returns Nothing if path is empty or has no drawing commands.
lastPoint :: Path -> Maybe Point2D
lastPoint path = findLastPoint $ getCommands path

-- | Find the last point from commands (helper).
-- |
-- | Note: HLineTo and VLineTo are partial coordinates — they cannot provide
-- | a full Point2D without knowing the current position. In these cases,
-- | we return Nothing (the point requires context to resolve).
findLastPoint :: Array PathCommand -> Maybe Point2D
findLastPoint cmds =
  case Array.last cmds of
    Nothing -> Nothing
    Just (MoveTo p) -> Just p
    Just (LineTo p) -> Just p
    Just (HLineTo _) -> Nothing  -- Partial coordinate, needs context
    Just (VLineTo _) -> Nothing  -- Partial coordinate, needs context
    Just (QuadTo _ p) -> Just p
    Just (SmoothQuadTo p) -> Just p
    Just (CubicTo _ _ p) -> Just p
    Just (SmoothCurveTo _ p) -> Just p
    Just (ArcTo params) -> Just params.end
    Just ClosePath ->
      -- ClosePath returns to first MoveTo — find it
      case Array.head cmds of
        Just (MoveTo p) -> Just p
        _ -> Nothing
