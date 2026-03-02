{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.VACESchema
Description : VACE export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

VACE (Video Animation Control Engine) export format enums and types.

Source: ui/src/schemas/exports/vace-schema.ts
-}

module Lattice.Schemas.Exports.VACESchema
  ( -- * Path Follower Shape
    PathFollowerShape(..)
  , pathFollowerShapeFromText
  , pathFollowerShapeToText
    -- * Path Follower Easing
  , PathFollowerEasing(..)
  , pathFollowerEasingFromText
  , pathFollowerEasingToText
    -- * Loop Mode
  , LoopMode(..)
  , loopModeFromText
  , loopModeToText
    -- * VACE Output Format
  , VACEOutputFormat(..)
  , vaceOutputFormatFromText
  , vaceOutputFormatToText
    -- * Structures
  , SplineControlPoint(..)
  , PathFollowerState(..)
    -- * Constants
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

import GHC.Generics (Generic)
import Data.Text (Text)

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

pathFollowerShapeFromText :: Text -> Maybe PathFollowerShape
pathFollowerShapeFromText "circle" = Just ShapeCircle
pathFollowerShapeFromText "square" = Just ShapeSquare
pathFollowerShapeFromText "triangle" = Just ShapeTriangle
pathFollowerShapeFromText "diamond" = Just ShapeDiamond
pathFollowerShapeFromText "arrow" = Just ShapeArrow
pathFollowerShapeFromText "custom" = Just ShapeCustom
pathFollowerShapeFromText _ = Nothing

pathFollowerShapeToText :: PathFollowerShape -> Text
pathFollowerShapeToText ShapeCircle = "circle"
pathFollowerShapeToText ShapeSquare = "square"
pathFollowerShapeToText ShapeTriangle = "triangle"
pathFollowerShapeToText ShapeDiamond = "diamond"
pathFollowerShapeToText ShapeArrow = "arrow"
pathFollowerShapeToText ShapeCustom = "custom"

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

pathFollowerEasingFromText :: Text -> Maybe PathFollowerEasing
pathFollowerEasingFromText "linear" = Just EasingLinear
pathFollowerEasingFromText "ease-in" = Just EasingEaseIn
pathFollowerEasingFromText "ease-out" = Just EasingEaseOut
pathFollowerEasingFromText "ease-in-out" = Just EasingEaseInOut
pathFollowerEasingFromText "ease-in-cubic" = Just EasingEaseInCubic
pathFollowerEasingFromText "ease-out-cubic" = Just EasingEaseOutCubic
pathFollowerEasingFromText _ = Nothing

pathFollowerEasingToText :: PathFollowerEasing -> Text
pathFollowerEasingToText EasingLinear = "linear"
pathFollowerEasingToText EasingEaseIn = "ease-in"
pathFollowerEasingToText EasingEaseOut = "ease-out"
pathFollowerEasingToText EasingEaseInOut = "ease-in-out"
pathFollowerEasingToText EasingEaseInCubic = "ease-in-cubic"
pathFollowerEasingToText EasingEaseOutCubic = "ease-out-cubic"

-- ────────────────────────────────────────────────────────────────────────────
-- Loop Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Loop mode options
data LoopMode
  = LoopRestart
  | LoopPingPong
  deriving stock (Eq, Show, Generic, Enum, Bounded)

loopModeFromText :: Text -> Maybe LoopMode
loopModeFromText "restart" = Just LoopRestart
loopModeFromText "pingpong" = Just LoopPingPong
loopModeFromText _ = Nothing

loopModeToText :: LoopMode -> Text
loopModeToText LoopRestart = "restart"
loopModeToText LoopPingPong = "pingpong"

-- ────────────────────────────────────────────────────────────────────────────
--                                                                 // vace // o
-- ────────────────────────────────────────────────────────────────────────────

-- | VACE output format options
data VACEOutputFormat
  = VACECanvas
  | VACEWebM
  | VACEFrames
  deriving stock (Eq, Show, Generic, Enum, Bounded)

vaceOutputFormatFromText :: Text -> Maybe VACEOutputFormat
vaceOutputFormatFromText "canvas" = Just VACECanvas
vaceOutputFormatFromText "webm" = Just VACEWebM
vaceOutputFormatFromText "frames" = Just VACEFrames
vaceOutputFormatFromText _ = Nothing

vaceOutputFormatToText :: VACEOutputFormat -> Text
vaceOutputFormatToText VACECanvas = "canvas"
vaceOutputFormatToText VACEWebM = "webm"
vaceOutputFormatToText VACEFrames = "frames"

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D/3D control point for splines
data SplineControlPoint = SplineControlPoint
  { scpX :: !Double
  , scpY :: !Double
  , scpZ :: !(Maybe Double)
  }
  deriving stock (Eq, Show, Generic)

-- | Path follower state at a frame
data PathFollowerState = PathFollowerState
  { pfsPositionX :: !Double
  , pfsPositionY :: !Double
  , pfsRotation :: !Double
  , pfsScale :: !Double
  , pfsOpacity :: !Double
  , pfsProgress :: !Double
  , pfsVisible :: !Bool
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxControlPoints :: Int
maxControlPoints = 100000

minClosedPathPoints :: Int
minClosedPathPoints = 3

maxCoordinate :: Double
maxCoordinate = 16384.0

maxSize :: Double
maxSize = 10000.0

maxStrokeWidth :: Double
maxStrokeWidth = 1000.0

maxRotationOffset :: Double
maxRotationOffset = 360.0

maxRotationRadians :: Double
maxRotationRadians = 6.28318

maxScale :: Double
maxScale = 100.0

maxPathFollowers :: Int
maxPathFollowers = 1000
