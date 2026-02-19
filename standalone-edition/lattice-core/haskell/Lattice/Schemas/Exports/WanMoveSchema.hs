{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.WanMoveSchema
Description : WanMove trajectory export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

WanMove trajectory export format enums and types.

Source: ui/src/schemas/exports/wanmove-schema.ts
-}

module Lattice.Schemas.Exports.WanMoveSchema
  ( -- * Flow Pattern
    FlowPattern(..)
  , flowPatternFromText
  , flowPatternToText
    -- * Morph Shape Type
  , MorphShapeType(..)
  , morphShapeTypeFromText
  , morphShapeTypeToText
    -- * Morph Easing
  , MorphEasing(..)
  , morphEasingFromText
  , morphEasingToText
    -- * Shape Easing
  , ShapeEasing(..)
  , shapeEasingFromText
  , shapeEasingToText
    -- * Attractor Type
  , AttractorType(..)
  , attractorTypeFromText
  , attractorTypeToText
    -- * Data Mapping
  , DataMapping(..)
  , dataMappingFromText
  , dataMappingToText
    -- * Force Falloff
  , ForceFalloff(..)
  , forceFalloffFromText
  , forceFalloffToText
    -- * Initial Distribution
  , InitialDistribution(..)
  , initialDistributionFromText
  , initialDistributionToText
    -- * Shape Type
  , ShapeType(..)
  , shapeTypeFromText
  , shapeTypeToText
    -- * Constants
  , wanMoveMaxDimension
  , wanMoveMaxPoints
  , wanMoveMaxFrames
  , maxFPS
    -- * Structures
  , Point2D(..)
  , TrackPointTuple
  , RGBColor(..)
  , WanMoveMetadata(..)
  , WanMoveTrajectory(..)
    -- * Validation
  , isValidMetadata
  , isValidRGBColor
  , isValidTrajectory
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V

-- ────────────────────────────────────────────────────────────────────────────
-- Flow Pattern
-- ────────────────────────────────────────────────────────────────────────────

-- | Available flow pattern types
data FlowPattern
  = FlowSpiral
  | FlowWave
  | FlowExplosion
  | FlowVortex
  | FlowDataRiver
  | FlowMorph
  | FlowSwarm
  deriving stock (Eq, Show, Generic, Enum, Bounded)

flowPatternFromText :: Text -> Maybe FlowPattern
flowPatternFromText "spiral" = Just FlowSpiral
flowPatternFromText "wave" = Just FlowWave
flowPatternFromText "explosion" = Just FlowExplosion
flowPatternFromText "vortex" = Just FlowVortex
flowPatternFromText "data-river" = Just FlowDataRiver
flowPatternFromText "morph" = Just FlowMorph
flowPatternFromText "swarm" = Just FlowSwarm
flowPatternFromText _ = Nothing

flowPatternToText :: FlowPattern -> Text
flowPatternToText FlowSpiral = "spiral"
flowPatternToText FlowWave = "wave"
flowPatternToText FlowExplosion = "explosion"
flowPatternToText FlowVortex = "vortex"
flowPatternToText FlowDataRiver = "data-river"
flowPatternToText FlowMorph = "morph"
flowPatternToText FlowSwarm = "swarm"

-- ────────────────────────────────────────────────────────────────────────────
-- Morph Shape Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Morph source/target types
data MorphShapeType
  = MorphCircle
  | MorphGrid
  | MorphText
  | MorphCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

morphShapeTypeFromText :: Text -> Maybe MorphShapeType
morphShapeTypeFromText "circle" = Just MorphCircle
morphShapeTypeFromText "grid" = Just MorphGrid
morphShapeTypeFromText "text" = Just MorphText
morphShapeTypeFromText "custom" = Just MorphCustom
morphShapeTypeFromText _ = Nothing

morphShapeTypeToText :: MorphShapeType -> Text
morphShapeTypeToText MorphCircle = "circle"
morphShapeTypeToText MorphGrid = "grid"
morphShapeTypeToText MorphText = "text"
morphShapeTypeToText MorphCustom = "custom"

-- ────────────────────────────────────────────────────────────────────────────
-- Morph Easing
-- ────────────────────────────────────────────────────────────────────────────

-- | Morph easing types
data MorphEasing
  = MEasingLinear
  | MEasingEaseIn
  | MEasingEaseOut
  | MEasingEaseInOut
  deriving stock (Eq, Show, Generic, Enum, Bounded)

morphEasingFromText :: Text -> Maybe MorphEasing
morphEasingFromText "linear" = Just MEasingLinear
morphEasingFromText "ease-in" = Just MEasingEaseIn
morphEasingFromText "ease-out" = Just MEasingEaseOut
morphEasingFromText "ease-in-out" = Just MEasingEaseInOut
morphEasingFromText _ = Nothing

morphEasingToText :: MorphEasing -> Text
morphEasingToText MEasingLinear = "linear"
morphEasingToText MEasingEaseIn = "ease-in"
morphEasingToText MEasingEaseOut = "ease-out"
morphEasingToText MEasingEaseInOut = "ease-in-out"

-- ────────────────────────────────────────────────────────────────────────────
-- Shape Easing
-- ────────────────────────────────────────────────────────────────────────────

-- | Extended easing types for shape morphing
data ShapeEasing
  = SEasingLinear
  | SEasingEaseIn
  | SEasingEaseOut
  | SEasingEaseInOut
  | SEasingElastic
  | SEasingBounce
  deriving stock (Eq, Show, Generic, Enum, Bounded)

shapeEasingFromText :: Text -> Maybe ShapeEasing
shapeEasingFromText "linear" = Just SEasingLinear
shapeEasingFromText "ease-in" = Just SEasingEaseIn
shapeEasingFromText "ease-out" = Just SEasingEaseOut
shapeEasingFromText "ease-in-out" = Just SEasingEaseInOut
shapeEasingFromText "elastic" = Just SEasingElastic
shapeEasingFromText "bounce" = Just SEasingBounce
shapeEasingFromText _ = Nothing

shapeEasingToText :: ShapeEasing -> Text
shapeEasingToText SEasingLinear = "linear"
shapeEasingToText SEasingEaseIn = "ease-in"
shapeEasingToText SEasingEaseOut = "ease-out"
shapeEasingToText SEasingEaseInOut = "ease-in-out"
shapeEasingToText SEasingElastic = "elastic"
shapeEasingToText SEasingBounce = "bounce"

-- ────────────────────────────────────────────────────────────────────────────
-- Attractor Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Available strange attractor types
data AttractorType
  = AttractorLorenz
  | AttractorRossler
  | AttractorAizawa
  | AttractorThomas
  | AttractorHalvorsen
  deriving stock (Eq, Show, Generic, Enum, Bounded)

attractorTypeFromText :: Text -> Maybe AttractorType
attractorTypeFromText "lorenz" = Just AttractorLorenz
attractorTypeFromText "rossler" = Just AttractorRossler
attractorTypeFromText "aizawa" = Just AttractorAizawa
attractorTypeFromText "thomas" = Just AttractorThomas
attractorTypeFromText "halvorsen" = Just AttractorHalvorsen
attractorTypeFromText _ = Nothing

attractorTypeToText :: AttractorType -> Text
attractorTypeToText AttractorLorenz = "lorenz"
attractorTypeToText AttractorRossler = "rossler"
attractorTypeToText AttractorAizawa = "aizawa"
attractorTypeToText AttractorThomas = "thomas"
attractorTypeToText AttractorHalvorsen = "halvorsen"

-- ────────────────────────────────────────────────────────────────────────────
-- Data Mapping
-- ────────────────────────────────────────────────────────────────────────────

-- | Data mapping types for data-driven flows
data DataMapping
  = MapSpeed
  | MapDirection
  | MapAmplitude
  | MapPhase
  | MapSize
  deriving stock (Eq, Show, Generic, Enum, Bounded)

dataMappingFromText :: Text -> Maybe DataMapping
dataMappingFromText "speed" = Just MapSpeed
dataMappingFromText "direction" = Just MapDirection
dataMappingFromText "amplitude" = Just MapAmplitude
dataMappingFromText "phase" = Just MapPhase
dataMappingFromText "size" = Just MapSize
dataMappingFromText _ = Nothing

dataMappingToText :: DataMapping -> Text
dataMappingToText MapSpeed = "speed"
dataMappingToText MapDirection = "direction"
dataMappingToText MapAmplitude = "amplitude"
dataMappingToText MapPhase = "phase"
dataMappingToText MapSize = "size"

-- ────────────────────────────────────────────────────────────────────────────
-- Force Falloff
-- ────────────────────────────────────────────────────────────────────────────

-- | Falloff types for force points
data ForceFalloff
  = FalloffLinear
  | FalloffQuadratic
  | FalloffNone
  deriving stock (Eq, Show, Generic, Enum, Bounded)

forceFalloffFromText :: Text -> Maybe ForceFalloff
forceFalloffFromText "linear" = Just FalloffLinear
forceFalloffFromText "quadratic" = Just FalloffQuadratic
forceFalloffFromText "none" = Just FalloffNone
forceFalloffFromText _ = Nothing

forceFalloffToText :: ForceFalloff -> Text
forceFalloffToText FalloffLinear = "linear"
forceFalloffToText FalloffQuadratic = "quadratic"
forceFalloffToText FalloffNone = "none"

-- ────────────────────────────────────────────────────────────────────────────
-- Initial Distribution
-- ────────────────────────────────────────────────────────────────────────────

-- | Initial distribution types for force fields
data InitialDistribution
  = DistRandom
  | DistGrid
  | DistEdge
  | DistCenter
  deriving stock (Eq, Show, Generic, Enum, Bounded)

initialDistributionFromText :: Text -> Maybe InitialDistribution
initialDistributionFromText "random" = Just DistRandom
initialDistributionFromText "grid" = Just DistGrid
initialDistributionFromText "edge" = Just DistEdge
initialDistributionFromText "center" = Just DistCenter
initialDistributionFromText _ = Nothing

initialDistributionToText :: InitialDistribution -> Text
initialDistributionToText DistRandom = "random"
initialDistributionToText DistGrid = "grid"
initialDistributionToText DistEdge = "edge"
initialDistributionToText DistCenter = "center"

-- ────────────────────────────────────────────────────────────────────────────
-- Shape Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Shape types for shape morphing
data ShapeType
  = ShapeCircle
  | ShapeGrid
  | ShapeText
  | ShapeHeart
  | ShapeStar
  | ShapeSpiral
  | ShapeRandom
  | ShapeCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

shapeTypeFromText :: Text -> Maybe ShapeType
shapeTypeFromText "circle" = Just ShapeCircle
shapeTypeFromText "grid" = Just ShapeGrid
shapeTypeFromText "text" = Just ShapeText
shapeTypeFromText "heart" = Just ShapeHeart
shapeTypeFromText "star" = Just ShapeStar
shapeTypeFromText "spiral" = Just ShapeSpiral
shapeTypeFromText "random" = Just ShapeRandom
shapeTypeFromText "custom" = Just ShapeCustom
shapeTypeFromText _ = Nothing

shapeTypeToText :: ShapeType -> Text
shapeTypeToText ShapeCircle = "circle"
shapeTypeToText ShapeGrid = "grid"
shapeTypeToText ShapeText = "text"
shapeTypeToText ShapeHeart = "heart"
shapeTypeToText ShapeStar = "star"
shapeTypeToText ShapeSpiral = "spiral"
shapeTypeToText ShapeRandom = "random"
shapeTypeToText ShapeCustom = "custom"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

wanMoveMaxDimension :: Int
wanMoveMaxDimension = 8192

wanMoveMaxPoints :: Int
wanMoveMaxPoints = 10000

wanMoveMaxFrames :: Int
wanMoveMaxFrames = 10000

maxFPS :: Double
maxFPS = 120.0

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D point
data Point2D = Point2D
  { p2dX :: !Double
  , p2dY :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Track point tuple
type TrackPointTuple = (Double, Double)

-- | RGB color (0-255)
data RGBColor = RGBColor
  { rgbR :: !Int
  , rgbG :: !Int
  , rgbB :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | WanMove trajectory metadata
data WanMoveMetadata = WanMoveMetadata
  { wmmNumPoints :: !Int
  , wmmNumFrames :: !Int
  , wmmWidth :: !Int
  , wmmHeight :: !Int
  , wmmFps :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | WanMove trajectory structure
data WanMoveTrajectory = WanMoveTrajectory
  { wmtTracks :: !(Vector (Vector TrackPointTuple))
  , wmtVisibility :: !(Vector (Vector Bool))
  , wmtMetadata :: !WanMoveMetadata
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if metadata is valid
isValidMetadata :: WanMoveMetadata -> Bool
isValidMetadata m =
  wmmNumPoints m > 0 && wmmNumPoints m <= wanMoveMaxPoints &&
  wmmNumFrames m > 0 && wmmNumFrames m <= wanMoveMaxFrames &&
  wmmWidth m > 0 && wmmWidth m <= wanMoveMaxDimension &&
  wmmHeight m > 0 && wmmHeight m <= wanMoveMaxDimension &&
  wmmFps m > 0 && wmmFps m <= maxFPS

-- | Check if RGB color is valid
isValidRGBColor :: RGBColor -> Bool
isValidRGBColor c =
  rgbR c >= 0 && rgbR c <= 255 &&
  rgbG c >= 0 && rgbG c <= 255 &&
  rgbB c >= 0 && rgbB c <= 255

-- | Check if trajectory is valid
isValidTrajectory :: WanMoveTrajectory -> Bool
isValidTrajectory t =
  isValidMetadata (wmtMetadata t) &&
  V.length (wmtTracks t) == wmmNumPoints (wmtMetadata t) &&
  V.length (wmtTracks t) == V.length (wmtVisibility t)
