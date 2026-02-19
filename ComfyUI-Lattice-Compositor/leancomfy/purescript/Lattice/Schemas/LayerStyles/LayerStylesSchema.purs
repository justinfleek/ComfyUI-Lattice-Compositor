-- | Lattice.Schemas.LayerStyles.LayerStylesSchema - Layer styles enums
-- |
-- | Layer styles enums (glow, bevel, stroke, gradient overlay, etc.).
-- |
-- | Source: ui/src/schemas/layerStyles/layerStyles-schema.ts

module Lattice.Schemas.LayerStyles.LayerStylesSchema
  ( -- Gradient Type
    GradientType(..)
  , gradientTypeFromString
  , gradientTypeToString
    -- Glow Technique
  , GlowTechnique(..)
  , glowTechniqueFromString
  , glowTechniqueToString
    -- Inner Glow Source
  , InnerGlowSource(..)
  , innerGlowSourceFromString
  , innerGlowSourceToString
    -- Bevel Style
  , BevelStyle(..)
  , bevelStyleFromString
  , bevelStyleToString
    -- Bevel Technique
  , BevelTechnique(..)
  , bevelTechniqueFromString
  , bevelTechniqueToString
    -- Bevel Direction
  , BevelDirection(..)
  , bevelDirectionFromString
  , bevelDirectionToString
    -- Gradient Overlay Type
  , GradientOverlayType(..)
  , gradientOverlayTypeFromString
  , gradientOverlayTypeToString
    -- Stroke Position
  , StrokePosition(..)
  , strokePositionFromString
  , strokePositionToString
    -- Stroke Fill Type
  , StrokeFillType(..)
  , strokeFillTypeFromString
  , strokeFillTypeToString
    -- Constants
  , maxGradientStops
  , minGradientStops
  , maxContourPoints
  , minContourPoints
  , maxRGB
  , minRGB
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Gradient Type
--------------------------------------------------------------------------------

-- | Gradient type options
data GradientType
  = GradientLinear
  | GradientRadial

derive instance Eq GradientType
derive instance Generic GradientType _

instance Show GradientType where
  show = genericShow

gradientTypeFromString :: String -> Maybe GradientType
gradientTypeFromString = case _ of
  "linear" -> Just GradientLinear
  "radial" -> Just GradientRadial
  _ -> Nothing

gradientTypeToString :: GradientType -> String
gradientTypeToString = case _ of
  GradientLinear -> "linear"
  GradientRadial -> "radial"

--------------------------------------------------------------------------------
-- Glow Technique
--------------------------------------------------------------------------------

-- | Glow technique options
data GlowTechnique
  = GlowSofter
  | GlowPrecise

derive instance Eq GlowTechnique
derive instance Generic GlowTechnique _

instance Show GlowTechnique where
  show = genericShow

glowTechniqueFromString :: String -> Maybe GlowTechnique
glowTechniqueFromString = case _ of
  "softer" -> Just GlowSofter
  "precise" -> Just GlowPrecise
  _ -> Nothing

glowTechniqueToString :: GlowTechnique -> String
glowTechniqueToString = case _ of
  GlowSofter -> "softer"
  GlowPrecise -> "precise"

--------------------------------------------------------------------------------
-- Inner Glow Source
--------------------------------------------------------------------------------

-- | Inner glow source options
data InnerGlowSource
  = GlowSourceCenter
  | GlowSourceEdge

derive instance Eq InnerGlowSource
derive instance Generic InnerGlowSource _

instance Show InnerGlowSource where
  show = genericShow

innerGlowSourceFromString :: String -> Maybe InnerGlowSource
innerGlowSourceFromString = case _ of
  "center" -> Just GlowSourceCenter
  "edge" -> Just GlowSourceEdge
  _ -> Nothing

innerGlowSourceToString :: InnerGlowSource -> String
innerGlowSourceToString = case _ of
  GlowSourceCenter -> "center"
  GlowSourceEdge -> "edge"

--------------------------------------------------------------------------------
-- Bevel Style
--------------------------------------------------------------------------------

-- | Bevel style options
data BevelStyle
  = BevelOuterBevel
  | BevelInnerBevel
  | BevelEmboss
  | BevelPillowEmboss
  | BevelStrokeEmboss

derive instance Eq BevelStyle
derive instance Generic BevelStyle _

instance Show BevelStyle where
  show = genericShow

bevelStyleFromString :: String -> Maybe BevelStyle
bevelStyleFromString = case _ of
  "outer-bevel" -> Just BevelOuterBevel
  "inner-bevel" -> Just BevelInnerBevel
  "emboss" -> Just BevelEmboss
  "pillow-emboss" -> Just BevelPillowEmboss
  "stroke-emboss" -> Just BevelStrokeEmboss
  _ -> Nothing

bevelStyleToString :: BevelStyle -> String
bevelStyleToString = case _ of
  BevelOuterBevel -> "outer-bevel"
  BevelInnerBevel -> "inner-bevel"
  BevelEmboss -> "emboss"
  BevelPillowEmboss -> "pillow-emboss"
  BevelStrokeEmboss -> "stroke-emboss"

--------------------------------------------------------------------------------
-- Bevel Technique
--------------------------------------------------------------------------------

-- | Bevel technique options
data BevelTechnique
  = BevelSmooth
  | BevelChiselHard
  | BevelChiselSoft

derive instance Eq BevelTechnique
derive instance Generic BevelTechnique _

instance Show BevelTechnique where
  show = genericShow

bevelTechniqueFromString :: String -> Maybe BevelTechnique
bevelTechniqueFromString = case _ of
  "smooth" -> Just BevelSmooth
  "chisel-hard" -> Just BevelChiselHard
  "chisel-soft" -> Just BevelChiselSoft
  _ -> Nothing

bevelTechniqueToString :: BevelTechnique -> String
bevelTechniqueToString = case _ of
  BevelSmooth -> "smooth"
  BevelChiselHard -> "chisel-hard"
  BevelChiselSoft -> "chisel-soft"

--------------------------------------------------------------------------------
-- Bevel Direction
--------------------------------------------------------------------------------

-- | Bevel direction options
data BevelDirection
  = BevelUp
  | BevelDown

derive instance Eq BevelDirection
derive instance Generic BevelDirection _

instance Show BevelDirection where
  show = genericShow

bevelDirectionFromString :: String -> Maybe BevelDirection
bevelDirectionFromString = case _ of
  "up" -> Just BevelUp
  "down" -> Just BevelDown
  _ -> Nothing

bevelDirectionToString :: BevelDirection -> String
bevelDirectionToString = case _ of
  BevelUp -> "up"
  BevelDown -> "down"

--------------------------------------------------------------------------------
-- Gradient Overlay Type
--------------------------------------------------------------------------------

-- | Gradient overlay type options
data GradientOverlayType
  = OverlayLinear
  | OverlayRadial
  | OverlayAngle
  | OverlayReflected
  | OverlayDiamond

derive instance Eq GradientOverlayType
derive instance Generic GradientOverlayType _

instance Show GradientOverlayType where
  show = genericShow

gradientOverlayTypeFromString :: String -> Maybe GradientOverlayType
gradientOverlayTypeFromString = case _ of
  "linear" -> Just OverlayLinear
  "radial" -> Just OverlayRadial
  "angle" -> Just OverlayAngle
  "reflected" -> Just OverlayReflected
  "diamond" -> Just OverlayDiamond
  _ -> Nothing

gradientOverlayTypeToString :: GradientOverlayType -> String
gradientOverlayTypeToString = case _ of
  OverlayLinear -> "linear"
  OverlayRadial -> "radial"
  OverlayAngle -> "angle"
  OverlayReflected -> "reflected"
  OverlayDiamond -> "diamond"

--------------------------------------------------------------------------------
-- Stroke Position
--------------------------------------------------------------------------------

-- | Stroke position options
data StrokePosition
  = StrokeOutside
  | StrokeInside
  | StrokeCenter

derive instance Eq StrokePosition
derive instance Generic StrokePosition _

instance Show StrokePosition where
  show = genericShow

strokePositionFromString :: String -> Maybe StrokePosition
strokePositionFromString = case _ of
  "outside" -> Just StrokeOutside
  "inside" -> Just StrokeInside
  "center" -> Just StrokeCenter
  _ -> Nothing

strokePositionToString :: StrokePosition -> String
strokePositionToString = case _ of
  StrokeOutside -> "outside"
  StrokeInside -> "inside"
  StrokeCenter -> "center"

--------------------------------------------------------------------------------
-- Stroke Fill Type
--------------------------------------------------------------------------------

-- | Stroke fill type options
data StrokeFillType
  = FillColor
  | FillGradient
  | FillPattern

derive instance Eq StrokeFillType
derive instance Generic StrokeFillType _

instance Show StrokeFillType where
  show = genericShow

strokeFillTypeFromString :: String -> Maybe StrokeFillType
strokeFillTypeFromString = case _ of
  "color" -> Just FillColor
  "gradient" -> Just FillGradient
  "pattern" -> Just FillPattern
  _ -> Nothing

strokeFillTypeToString :: StrokeFillType -> String
strokeFillTypeToString = case _ of
  FillColor -> "color"
  FillGradient -> "gradient"
  FillPattern -> "pattern"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxGradientStops :: Int
maxGradientStops = 100

minGradientStops :: Int
minGradientStops = 2

maxContourPoints :: Int
maxContourPoints = 1000

minContourPoints :: Int
minContourPoints = 2

maxRGB :: Int
maxRGB = 255

minRGB :: Int
minRGB = 0
