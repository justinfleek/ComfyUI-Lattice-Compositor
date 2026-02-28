-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // geometry // path // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for SVG path commands.
-- |
-- | Defines PathCommand (SVG path commands), Path (array of commands),
-- | and ArcParams (elliptical arc parameters).

module Hydrogen.Schema.Geometry.Path.Types
  ( -- * Types
    PathCommand(..)
  , allPathCommandTags
  , Path(Path)
  , ArcParams
  
    -- * Accessors
  , getCommands
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Angle (Degrees)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // arc params
-- ═════════════════════════════════════════════════════════════════════════════

-- | Arc parameters for elliptical arc command.
type ArcParams =
  { rx :: Number           -- ^ X radius
  , ry :: Number           -- ^ Y radius
  , rotation :: Degrees    -- ^ X-axis rotation
  , largeArc :: Boolean    -- ^ Use large arc (> 180°)
  , sweep :: Boolean       -- ^ Sweep clockwise
  , end :: Point2D         -- ^ End point
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // path command
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG path command.
-- |
-- | Includes both absolute commands and shorthand variants:
-- | - **HLineTo**: Horizontal line (only X coordinate needed)
-- | - **VLineTo**: Vertical line (only Y coordinate needed)
-- | - **SmoothCurveTo**: Smooth cubic bezier (first control point inferred)
-- | - **SmoothQuadTo**: Smooth quadratic bezier (control point inferred)
data PathCommand
  = MoveTo Point2D
  | LineTo Point2D
  | HLineTo Number                     -- ^ Horizontal line to X coordinate
  | VLineTo Number                     -- ^ Vertical line to Y coordinate
  | QuadTo Point2D Point2D
  | SmoothQuadTo Point2D               -- ^ Control point inferred from previous
  | CubicTo Point2D Point2D Point2D
  | SmoothCurveTo Point2D Point2D      -- ^ First control point inferred from previous
  | ArcTo ArcParams
  | ClosePath

derive instance eqPathCommand :: Eq PathCommand

instance showPathCommand :: Show PathCommand where
  show (MoveTo p) = "(MoveTo " <> show p <> ")"
  show (LineTo p) = "(LineTo " <> show p <> ")"
  show (HLineTo x) = "(HLineTo " <> show x <> ")"
  show (VLineTo y) = "(VLineTo " <> show y <> ")"
  show (QuadTo c p) = "(QuadTo " <> show c <> " " <> show p <> ")"
  show (SmoothQuadTo p) = "(SmoothQuadTo " <> show p <> ")"
  show (CubicTo c1 c2 p) = "(CubicTo " <> show c1 <> " " <> show c2 <> " " <> show p <> ")"
  show (SmoothCurveTo c2 p) = "(SmoothCurveTo " <> show c2 <> " " <> show p <> ")"
  show (ArcTo params) = "(ArcTo rx:" <> show params.rx <> " ry:" <> show params.ry <> " end:" <> show params.end <> ")"
  show ClosePath = "ClosePath"

-- | All path command tags for enumeration.
-- |
-- | Note: This lists the constructor names, not actual PathCommand values,
-- | since most constructors require parameters.
allPathCommandTags :: Array String
allPathCommandTags =
  [ "MoveTo"
  , "LineTo"
  , "HLineTo"
  , "VLineTo"
  , "QuadTo"
  , "SmoothQuadTo"
  , "CubicTo"
  , "SmoothCurveTo"
  , "ArcTo"
  , "ClosePath"
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // path
-- ═════════════════════════════════════════════════════════════════════════════

-- | A path is an array of commands.
newtype Path = Path (Array PathCommand)

derive instance eqPath :: Eq Path

instance showPath :: Show Path where
  show (Path cmds) = "(Path " <> show cmds <> ")"

-- | Get the array of commands.
getCommands :: Path -> Array PathCommand
getCommands (Path cmds) = cmds
