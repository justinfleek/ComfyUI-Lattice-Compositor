-- | Lattice.Schemas.Exports.WanMoveSchema - WanMove trajectory export format enums and types
-- |
-- | WanMove trajectory export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/wanmove-schema.ts

module Lattice.Schemas.Exports.WanMoveSchema
  ( -- Flow Pattern
    FlowPattern(..)
  , flowPatternFromString
  , flowPatternToString
    -- Morph Shape Type
  , MorphShapeType(..)
  , morphShapeTypeFromString
  , morphShapeTypeToString
    -- Morph Easing
  , MorphEasing(..)
  , morphEasingFromString
  , morphEasingToString
    -- Shape Easing
  , ShapeEasing(..)
  , shapeEasingFromString
  , shapeEasingToString
    -- Attractor Type
  , AttractorType(..)
  , attractorTypeFromString
  , attractorTypeToString
    -- Data Mapping
  , DataMapping(..)
  , dataMappingFromString
  , dataMappingToString
    -- Force Falloff
  , ForceFalloff(..)
  , forceFalloffFromString
  , forceFalloffToString
    -- Initial Distribution
  , InitialDistribution(..)
  , initialDistributionFromString
  , initialDistributionToString
    -- Shape Type
  , ShapeType(..)
  , shapeTypeFromString
  , shapeTypeToString
    -- Constants
  , wanMoveMaxDimension
  , wanMoveMaxPoints
  , wanMoveMaxFrames
  , maxFPS
    -- Structures
  , Point2D
  , TrackPointTuple
  , RGBColor
  , WanMoveMetadata
  , WanMoveTrajectory
    -- Validation
  , isValidMetadata
  , isValidRGBColor
  , isValidTrajectory
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Data.Array (length, all)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Flow Pattern
--------------------------------------------------------------------------------

-- | Available flow pattern types
data FlowPattern
  = FlowSpiral
  | FlowWave
  | FlowExplosion
  | FlowVortex
  | FlowDataRiver
  | FlowMorph
  | FlowSwarm

derive instance Eq FlowPattern
derive instance Generic FlowPattern _

instance Show FlowPattern where
  show = genericShow

flowPatternFromString :: String -> Maybe FlowPattern
flowPatternFromString = case _ of
  "spiral" -> Just FlowSpiral
  "wave" -> Just FlowWave
  "explosion" -> Just FlowExplosion
  "vortex" -> Just FlowVortex
  "data-river" -> Just FlowDataRiver
  "morph" -> Just FlowMorph
  "swarm" -> Just FlowSwarm
  _ -> Nothing

flowPatternToString :: FlowPattern -> String
flowPatternToString = case _ of
  FlowSpiral -> "spiral"
  FlowWave -> "wave"
  FlowExplosion -> "explosion"
  FlowVortex -> "vortex"
  FlowDataRiver -> "data-river"
  FlowMorph -> "morph"
  FlowSwarm -> "swarm"

--------------------------------------------------------------------------------
-- Morph Shape Type
--------------------------------------------------------------------------------

-- | Morph source/target types
data MorphShapeType
  = MorphCircle
  | MorphGrid
  | MorphText
  | MorphCustom

derive instance Eq MorphShapeType
derive instance Generic MorphShapeType _

instance Show MorphShapeType where
  show = genericShow

morphShapeTypeFromString :: String -> Maybe MorphShapeType
morphShapeTypeFromString = case _ of
  "circle" -> Just MorphCircle
  "grid" -> Just MorphGrid
  "text" -> Just MorphText
  "custom" -> Just MorphCustom
  _ -> Nothing

morphShapeTypeToString :: MorphShapeType -> String
morphShapeTypeToString = case _ of
  MorphCircle -> "circle"
  MorphGrid -> "grid"
  MorphText -> "text"
  MorphCustom -> "custom"

--------------------------------------------------------------------------------
-- Morph Easing
--------------------------------------------------------------------------------

-- | Morph easing types
data MorphEasing
  = MEasingLinear
  | MEasingEaseIn
  | MEasingEaseOut
  | MEasingEaseInOut

derive instance Eq MorphEasing
derive instance Generic MorphEasing _

instance Show MorphEasing where
  show = genericShow

morphEasingFromString :: String -> Maybe MorphEasing
morphEasingFromString = case _ of
  "linear" -> Just MEasingLinear
  "ease-in" -> Just MEasingEaseIn
  "ease-out" -> Just MEasingEaseOut
  "ease-in-out" -> Just MEasingEaseInOut
  _ -> Nothing

morphEasingToString :: MorphEasing -> String
morphEasingToString = case _ of
  MEasingLinear -> "linear"
  MEasingEaseIn -> "ease-in"
  MEasingEaseOut -> "ease-out"
  MEasingEaseInOut -> "ease-in-out"

--------------------------------------------------------------------------------
-- Shape Easing
--------------------------------------------------------------------------------

-- | Extended easing types for shape morphing
data ShapeEasing
  = SEasingLinear
  | SEasingEaseIn
  | SEasingEaseOut
  | SEasingEaseInOut
  | SEasingElastic
  | SEasingBounce

derive instance Eq ShapeEasing
derive instance Generic ShapeEasing _

instance Show ShapeEasing where
  show = genericShow

shapeEasingFromString :: String -> Maybe ShapeEasing
shapeEasingFromString = case _ of
  "linear" -> Just SEasingLinear
  "ease-in" -> Just SEasingEaseIn
  "ease-out" -> Just SEasingEaseOut
  "ease-in-out" -> Just SEasingEaseInOut
  "elastic" -> Just SEasingElastic
  "bounce" -> Just SEasingBounce
  _ -> Nothing

shapeEasingToString :: ShapeEasing -> String
shapeEasingToString = case _ of
  SEasingLinear -> "linear"
  SEasingEaseIn -> "ease-in"
  SEasingEaseOut -> "ease-out"
  SEasingEaseInOut -> "ease-in-out"
  SEasingElastic -> "elastic"
  SEasingBounce -> "bounce"

--------------------------------------------------------------------------------
-- Attractor Type
--------------------------------------------------------------------------------

-- | Available strange attractor types
data AttractorType
  = AttractorLorenz
  | AttractorRossler
  | AttractorAizawa
  | AttractorThomas
  | AttractorHalvorsen

derive instance Eq AttractorType
derive instance Generic AttractorType _

instance Show AttractorType where
  show = genericShow

attractorTypeFromString :: String -> Maybe AttractorType
attractorTypeFromString = case _ of
  "lorenz" -> Just AttractorLorenz
  "rossler" -> Just AttractorRossler
  "aizawa" -> Just AttractorAizawa
  "thomas" -> Just AttractorThomas
  "halvorsen" -> Just AttractorHalvorsen
  _ -> Nothing

attractorTypeToString :: AttractorType -> String
attractorTypeToString = case _ of
  AttractorLorenz -> "lorenz"
  AttractorRossler -> "rossler"
  AttractorAizawa -> "aizawa"
  AttractorThomas -> "thomas"
  AttractorHalvorsen -> "halvorsen"

--------------------------------------------------------------------------------
-- Data Mapping
--------------------------------------------------------------------------------

-- | Data mapping types for data-driven flows
data DataMapping
  = MapSpeed
  | MapDirection
  | MapAmplitude
  | MapPhase
  | MapSize

derive instance Eq DataMapping
derive instance Generic DataMapping _

instance Show DataMapping where
  show = genericShow

dataMappingFromString :: String -> Maybe DataMapping
dataMappingFromString = case _ of
  "speed" -> Just MapSpeed
  "direction" -> Just MapDirection
  "amplitude" -> Just MapAmplitude
  "phase" -> Just MapPhase
  "size" -> Just MapSize
  _ -> Nothing

dataMappingToString :: DataMapping -> String
dataMappingToString = case _ of
  MapSpeed -> "speed"
  MapDirection -> "direction"
  MapAmplitude -> "amplitude"
  MapPhase -> "phase"
  MapSize -> "size"

--------------------------------------------------------------------------------
-- Force Falloff
--------------------------------------------------------------------------------

-- | Falloff types for force points
data ForceFalloff
  = FalloffLinear
  | FalloffQuadratic
  | FalloffNone

derive instance Eq ForceFalloff
derive instance Generic ForceFalloff _

instance Show ForceFalloff where
  show = genericShow

forceFalloffFromString :: String -> Maybe ForceFalloff
forceFalloffFromString = case _ of
  "linear" -> Just FalloffLinear
  "quadratic" -> Just FalloffQuadratic
  "none" -> Just FalloffNone
  _ -> Nothing

forceFalloffToString :: ForceFalloff -> String
forceFalloffToString = case _ of
  FalloffLinear -> "linear"
  FalloffQuadratic -> "quadratic"
  FalloffNone -> "none"

--------------------------------------------------------------------------------
-- Initial Distribution
--------------------------------------------------------------------------------

-- | Initial distribution types for force fields
data InitialDistribution
  = DistRandom
  | DistGrid
  | DistEdge
  | DistCenter

derive instance Eq InitialDistribution
derive instance Generic InitialDistribution _

instance Show InitialDistribution where
  show = genericShow

initialDistributionFromString :: String -> Maybe InitialDistribution
initialDistributionFromString = case _ of
  "random" -> Just DistRandom
  "grid" -> Just DistGrid
  "edge" -> Just DistEdge
  "center" -> Just DistCenter
  _ -> Nothing

initialDistributionToString :: InitialDistribution -> String
initialDistributionToString = case _ of
  DistRandom -> "random"
  DistGrid -> "grid"
  DistEdge -> "edge"
  DistCenter -> "center"

--------------------------------------------------------------------------------
-- Shape Type
--------------------------------------------------------------------------------

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

derive instance Eq ShapeType
derive instance Generic ShapeType _

instance Show ShapeType where
  show = genericShow

shapeTypeFromString :: String -> Maybe ShapeType
shapeTypeFromString = case _ of
  "circle" -> Just ShapeCircle
  "grid" -> Just ShapeGrid
  "text" -> Just ShapeText
  "heart" -> Just ShapeHeart
  "star" -> Just ShapeStar
  "spiral" -> Just ShapeSpiral
  "random" -> Just ShapeRandom
  "custom" -> Just ShapeCustom
  _ -> Nothing

shapeTypeToString :: ShapeType -> String
shapeTypeToString = case _ of
  ShapeCircle -> "circle"
  ShapeGrid -> "grid"
  ShapeText -> "text"
  ShapeHeart -> "heart"
  ShapeStar -> "star"
  ShapeSpiral -> "spiral"
  ShapeRandom -> "random"
  ShapeCustom -> "custom"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

wanMoveMaxDimension :: Int
wanMoveMaxDimension = 8192

wanMoveMaxPoints :: Int
wanMoveMaxPoints = 10000

wanMoveMaxFrames :: Int
wanMoveMaxFrames = 10000

maxFPS :: Number
maxFPS = 120.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | 2D point
type Point2D =
  { x :: Number
  , y :: Number
  }

-- | Track point tuple
type TrackPointTuple = Tuple Number Number

-- | RGB color (0-255)
type RGBColor =
  { r :: Int
  , g :: Int
  , b :: Int
  }

-- | WanMove trajectory metadata
type WanMoveMetadata =
  { numPoints :: Int
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , fps :: Number
  }

-- | WanMove trajectory structure
type WanMoveTrajectory =
  { tracks :: Array (Array TrackPointTuple)
  , visibility :: Array (Array Boolean)
  , metadata :: WanMoveMetadata
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if metadata is valid
isValidMetadata :: WanMoveMetadata -> Boolean
isValidMetadata m =
  m.numPoints > 0 && m.numPoints <= wanMoveMaxPoints &&
  m.numFrames > 0 && m.numFrames <= wanMoveMaxFrames &&
  m.width > 0 && m.width <= wanMoveMaxDimension &&
  m.height > 0 && m.height <= wanMoveMaxDimension &&
  m.fps > 0.0 && m.fps <= maxFPS

-- | Check if RGB color is valid
isValidRGBColor :: RGBColor -> Boolean
isValidRGBColor c =
  c.r >= 0 && c.r <= 255 &&
  c.g >= 0 && c.g <= 255 &&
  c.b >= 0 && c.b <= 255

-- | Check if trajectory is valid
isValidTrajectory :: WanMoveTrajectory -> Boolean
isValidTrajectory t =
  isValidMetadata t.metadata &&
  length t.tracks == t.metadata.numPoints &&
  length t.tracks == length t.visibility
