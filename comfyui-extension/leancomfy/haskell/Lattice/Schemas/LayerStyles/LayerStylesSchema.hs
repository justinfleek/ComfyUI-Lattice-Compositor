{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.LayerStyles.LayerStylesSchema
Description : Layer styles enums
Copyright   : (c) Lattice, 2026
License     : MIT

Layer styles enums (glow, bevel, stroke, gradient overlay, etc.).

Source: ui/src/schemas/layerStyles/layerStyles-schema.ts
-}

module Lattice.Schemas.LayerStyles.LayerStylesSchema
  ( -- * Gradient Type
    GradientType(..)
  , gradientTypeFromText
  , gradientTypeToText
    -- * Glow Technique
  , GlowTechnique(..)
  , glowTechniqueFromText
  , glowTechniqueToText
    -- * Inner Glow Source
  , InnerGlowSource(..)
  , innerGlowSourceFromText
  , innerGlowSourceToText
    -- * Bevel Style
  , BevelStyle(..)
  , bevelStyleFromText
  , bevelStyleToText
    -- * Bevel Technique
  , BevelTechnique(..)
  , bevelTechniqueFromText
  , bevelTechniqueToText
    -- * Bevel Direction
  , BevelDirection(..)
  , bevelDirectionFromText
  , bevelDirectionToText
    -- * Gradient Overlay Type
  , GradientOverlayType(..)
  , gradientOverlayTypeFromText
  , gradientOverlayTypeToText
    -- * Stroke Position
  , StrokePosition(..)
  , strokePositionFromText
  , strokePositionToText
    -- * Stroke Fill Type
  , StrokeFillType(..)
  , strokeFillTypeFromText
  , strokeFillTypeToText
    -- * Constants
  , maxGradientStops
  , minGradientStops
  , maxContourPoints
  , minContourPoints
  , maxRGB
  , minRGB
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Gradient Type
--------------------------------------------------------------------------------

-- | Gradient type options
data GradientType
  = GradientLinear
  | GradientRadial
  deriving stock (Eq, Show, Generic, Enum, Bounded)

gradientTypeFromText :: Text -> Maybe GradientType
gradientTypeFromText "linear" = Just GradientLinear
gradientTypeFromText "radial" = Just GradientRadial
gradientTypeFromText _ = Nothing

gradientTypeToText :: GradientType -> Text
gradientTypeToText GradientLinear = "linear"
gradientTypeToText GradientRadial = "radial"

--------------------------------------------------------------------------------
-- Glow Technique
--------------------------------------------------------------------------------

-- | Glow technique options
data GlowTechnique
  = GlowSofter
  | GlowPrecise
  deriving stock (Eq, Show, Generic, Enum, Bounded)

glowTechniqueFromText :: Text -> Maybe GlowTechnique
glowTechniqueFromText "softer" = Just GlowSofter
glowTechniqueFromText "precise" = Just GlowPrecise
glowTechniqueFromText _ = Nothing

glowTechniqueToText :: GlowTechnique -> Text
glowTechniqueToText GlowSofter = "softer"
glowTechniqueToText GlowPrecise = "precise"

--------------------------------------------------------------------------------
-- Inner Glow Source
--------------------------------------------------------------------------------

-- | Inner glow source options
data InnerGlowSource
  = GlowSourceCenter
  | GlowSourceEdge
  deriving stock (Eq, Show, Generic, Enum, Bounded)

innerGlowSourceFromText :: Text -> Maybe InnerGlowSource
innerGlowSourceFromText "center" = Just GlowSourceCenter
innerGlowSourceFromText "edge" = Just GlowSourceEdge
innerGlowSourceFromText _ = Nothing

innerGlowSourceToText :: InnerGlowSource -> Text
innerGlowSourceToText GlowSourceCenter = "center"
innerGlowSourceToText GlowSourceEdge = "edge"

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

bevelStyleFromText :: Text -> Maybe BevelStyle
bevelStyleFromText "outer-bevel" = Just BevelOuterBevel
bevelStyleFromText "inner-bevel" = Just BevelInnerBevel
bevelStyleFromText "emboss" = Just BevelEmboss
bevelStyleFromText "pillow-emboss" = Just BevelPillowEmboss
bevelStyleFromText "stroke-emboss" = Just BevelStrokeEmboss
bevelStyleFromText _ = Nothing

bevelStyleToText :: BevelStyle -> Text
bevelStyleToText BevelOuterBevel = "outer-bevel"
bevelStyleToText BevelInnerBevel = "inner-bevel"
bevelStyleToText BevelEmboss = "emboss"
bevelStyleToText BevelPillowEmboss = "pillow-emboss"
bevelStyleToText BevelStrokeEmboss = "stroke-emboss"

--------------------------------------------------------------------------------
-- Bevel Technique
--------------------------------------------------------------------------------

-- | Bevel technique options
data BevelTechnique
  = BevelSmooth
  | BevelChiselHard
  | BevelChiselSoft
  deriving stock (Eq, Show, Generic, Enum, Bounded)

bevelTechniqueFromText :: Text -> Maybe BevelTechnique
bevelTechniqueFromText "smooth" = Just BevelSmooth
bevelTechniqueFromText "chisel-hard" = Just BevelChiselHard
bevelTechniqueFromText "chisel-soft" = Just BevelChiselSoft
bevelTechniqueFromText _ = Nothing

bevelTechniqueToText :: BevelTechnique -> Text
bevelTechniqueToText BevelSmooth = "smooth"
bevelTechniqueToText BevelChiselHard = "chisel-hard"
bevelTechniqueToText BevelChiselSoft = "chisel-soft"

--------------------------------------------------------------------------------
-- Bevel Direction
--------------------------------------------------------------------------------

-- | Bevel direction options
data BevelDirection
  = BevelUp
  | BevelDown
  deriving stock (Eq, Show, Generic, Enum, Bounded)

bevelDirectionFromText :: Text -> Maybe BevelDirection
bevelDirectionFromText "up" = Just BevelUp
bevelDirectionFromText "down" = Just BevelDown
bevelDirectionFromText _ = Nothing

bevelDirectionToText :: BevelDirection -> Text
bevelDirectionToText BevelUp = "up"
bevelDirectionToText BevelDown = "down"

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

gradientOverlayTypeFromText :: Text -> Maybe GradientOverlayType
gradientOverlayTypeFromText "linear" = Just OverlayLinear
gradientOverlayTypeFromText "radial" = Just OverlayRadial
gradientOverlayTypeFromText "angle" = Just OverlayAngle
gradientOverlayTypeFromText "reflected" = Just OverlayReflected
gradientOverlayTypeFromText "diamond" = Just OverlayDiamond
gradientOverlayTypeFromText _ = Nothing

gradientOverlayTypeToText :: GradientOverlayType -> Text
gradientOverlayTypeToText OverlayLinear = "linear"
gradientOverlayTypeToText OverlayRadial = "radial"
gradientOverlayTypeToText OverlayAngle = "angle"
gradientOverlayTypeToText OverlayReflected = "reflected"
gradientOverlayTypeToText OverlayDiamond = "diamond"

--------------------------------------------------------------------------------
-- Stroke Position
--------------------------------------------------------------------------------

-- | Stroke position options
data StrokePosition
  = StrokeOutside
  | StrokeInside
  | StrokeCenter
  deriving stock (Eq, Show, Generic, Enum, Bounded)

strokePositionFromText :: Text -> Maybe StrokePosition
strokePositionFromText "outside" = Just StrokeOutside
strokePositionFromText "inside" = Just StrokeInside
strokePositionFromText "center" = Just StrokeCenter
strokePositionFromText _ = Nothing

strokePositionToText :: StrokePosition -> Text
strokePositionToText StrokeOutside = "outside"
strokePositionToText StrokeInside = "inside"
strokePositionToText StrokeCenter = "center"

--------------------------------------------------------------------------------
-- Stroke Fill Type
--------------------------------------------------------------------------------

-- | Stroke fill type options
data StrokeFillType
  = FillColor
  | FillGradient
  | FillPattern
  deriving stock (Eq, Show, Generic, Enum, Bounded)

strokeFillTypeFromText :: Text -> Maybe StrokeFillType
strokeFillTypeFromText "color" = Just FillColor
strokeFillTypeFromText "gradient" = Just FillGradient
strokeFillTypeFromText "pattern" = Just FillPattern
strokeFillTypeFromText _ = Nothing

strokeFillTypeToText :: StrokeFillType -> Text
strokeFillTypeToText FillColor = "color"
strokeFillTypeToText FillGradient = "gradient"
strokeFillTypeToText FillPattern = "pattern"

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
