-- | Lattice.Schemas.Exports.VACESchema - VACE export format enums and types
-- |
-- | VACE (Video Animation Control Engine) export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/vace-schema.ts

module Lattice.Schemas.Exports.VACESchema
  ( -- Path Follower Shape
    PathFollowerShape(..)
  , pathFollowerShapeFromString
  , pathFollowerShapeToString
    -- Path Follower Easing
  , PathFollowerEasing(..)
  , pathFollowerEasingFromString
  , pathFollowerEasingToString
    -- Loop Mode
  , LoopMode(..)
  , loopModeFromString
  , loopModeToString
    --                                                                 // vace // o
  , VACEOutputFormat(..)
  , vaceOutputFormatFromString
  , vaceOutputFormatToString
    -- Structures
  , SplineControlPoint
  , PathFollowerState
    -- Constants
  , maxControlPoints
  , minClosedPathPoints
  , maxCoordinate
  , maxSize
  , maxStrokeWidth
  , maxRotationOffset
  , maxRotationRadians
  , maxScale
  , maxPathFollowers
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Path Follower Shape
-- ────────────────────────────────────────────────────────────────────────────

-- | Path follower shape options
data PathFollowerShape
  = ShapeCircle
  | ShapeSquare
  | ShapeTriangle
  | ShapeDiamond
  | ShapeArrow
  | ShapeCustom

derive instance Eq PathFollowerShape
derive instance Generic PathFollowerShape _

instance Show PathFollowerShape where
  show = genericShow

pathFollowerShapeFromString :: String -> Maybe PathFollowerShape
pathFollowerShapeFromString = case _ of
  "circle" -> Just ShapeCircle
  "square" -> Just ShapeSquare
  "triangle" -> Just ShapeTriangle
  "diamond" -> Just ShapeDiamond
  "arrow" -> Just ShapeArrow
  "custom" -> Just ShapeCustom
  _ -> Nothing

pathFollowerShapeToString :: PathFollowerShape -> String
pathFollowerShapeToString = case _ of
  ShapeCircle -> "circle"
  ShapeSquare -> "square"
  ShapeTriangle -> "triangle"
  ShapeDiamond -> "diamond"
  ShapeArrow -> "arrow"
  ShapeCustom -> "custom"

-- ────────────────────────────────────────────────────────────────────────────
-- Path Follower Easing
-- ────────────────────────────────────────────────────────────────────────────

-- | Path follower easing options
data PathFollowerEasing
  = EasingLinear
  | EasingEaseIn
  | EasingEaseOut
  | EasingEaseInOut
  | EasingEaseInCubic
  | EasingEaseOutCubic

derive instance Eq PathFollowerEasing
derive instance Generic PathFollowerEasing _

instance Show PathFollowerEasing where
  show = genericShow

pathFollowerEasingFromString :: String -> Maybe PathFollowerEasing
pathFollowerEasingFromString = case _ of
  "linear" -> Just EasingLinear
  "ease-in" -> Just EasingEaseIn
  "ease-out" -> Just EasingEaseOut
  "ease-in-out" -> Just EasingEaseInOut
  "ease-in-cubic" -> Just EasingEaseInCubic
  "ease-out-cubic" -> Just EasingEaseOutCubic
  _ -> Nothing

pathFollowerEasingToString :: PathFollowerEasing -> String
pathFollowerEasingToString = case _ of
  EasingLinear -> "linear"
  EasingEaseIn -> "ease-in"
  EasingEaseOut -> "ease-out"
  EasingEaseInOut -> "ease-in-out"
  EasingEaseInCubic -> "ease-in-cubic"
  EasingEaseOutCubic -> "ease-out-cubic"

-- ────────────────────────────────────────────────────────────────────────────
-- Loop Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Loop mode options
data LoopMode
  = LoopRestart
  | LoopPingPong

derive instance Eq LoopMode
derive instance Generic LoopMode _

instance Show LoopMode where
  show = genericShow

loopModeFromString :: String -> Maybe LoopMode
loopModeFromString = case _ of
  "restart" -> Just LoopRestart
  "pingpong" -> Just LoopPingPong
  _ -> Nothing

loopModeToString :: LoopMode -> String
loopModeToString = case _ of
  LoopRestart -> "restart"
  LoopPingPong -> "pingpong"

-- ────────────────────────────────────────────────────────────────────────────
--                                                                 // vace // o
-- ────────────────────────────────────────────────────────────────────────────

-- | VACE output format options
data VACEOutputFormat
  = VACECanvas
  | VACEWebM
  | VACEFrames

derive instance Eq VACEOutputFormat
derive instance Generic VACEOutputFormat _

instance Show VACEOutputFormat where
  show = genericShow

vaceOutputFormatFromString :: String -> Maybe VACEOutputFormat
vaceOutputFormatFromString = case _ of
  "canvas" -> Just VACECanvas
  "webm" -> Just VACEWebM
  "frames" -> Just VACEFrames
  _ -> Nothing

vaceOutputFormatToString :: VACEOutputFormat -> String
vaceOutputFormatToString = case _ of
  VACECanvas -> "canvas"
  VACEWebM -> "webm"
  VACEFrames -> "frames"

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D/3D control point for splines
type SplineControlPoint =
  { x :: Number
  , y :: Number
  , z :: Maybe Number
  }

-- | Path follower state at a frame
type PathFollowerState =
  { positionX :: Number
  , positionY :: Number
  , rotation :: Number
  , scale :: Number
  , opacity :: Number
  , progress :: Number
  , visible :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxControlPoints :: Int
maxControlPoints = 100000

minClosedPathPoints :: Int
minClosedPathPoints = 3

maxCoordinate :: Number
maxCoordinate = 16384.0

maxSize :: Number
maxSize = 10000.0

maxStrokeWidth :: Number
maxStrokeWidth = 1000.0

maxRotationOffset :: Number
maxRotationOffset = 360.0

maxRotationRadians :: Number
maxRotationRadians = 6.28318

maxScale :: Number
maxScale = 100.0

maxPathFollowers :: Int
maxPathFollowers = 1000
