{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Layers.PrimitivesSchema
Description : Layer primitive enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Foundational layer data types: blend modes, vectors, colors.

Source: ui/src/schemas/layers/primitives-schema.ts
-}

module Lattice.Schemas.Layers.PrimitivesSchema
  ( -- * Blend Mode
    BlendMode(..)
  , blendModeFromText
  , blendModeToText
    -- * Quality Mode
  , QualityMode(..)
  , qualityModeFromText
  , qualityModeToText
    -- * Structures
  , Vec2(..)
  , Vec3(..)
  , Position2DOr3D(..)
  , RGBAColor(..)
  , RGBA255Color(..)
  , Rect(..)
    -- * Validation
  , isValidVec2
  , isValidVec3
  , isValidPosition2DOr3D
  , isValidRGBAColor
  , isValidRGBA255Color
  , isValidRect
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Blend Mode
--------------------------------------------------------------------------------

-- | Blend modes for layer compositing
data BlendMode
  = BlendNormal
  | BlendMultiply
  | BlendScreen
  | BlendOverlay
  | BlendDarken
  | BlendLighten
  | BlendColorDodge
  | BlendColorBurn
  | BlendHardLight
  | BlendSoftLight
  | BlendDifference
  | BlendExclusion
  | BlendHue
  | BlendSaturation
  | BlendColor
  | BlendLuminosity
  | BlendAdd
  | BlendSubtract
  | BlendDivide
  | BlendClassicColorDodge
  | BlendClassicColorBurn
  | BlendStencilAlpha
  | BlendStencilLuma
  | BlendSilhouetteAlpha
  | BlendSilhouetteLuma
  | BlendBehind
  | BlendAlphaAdd
  | BlendDissolve
  deriving stock (Eq, Show, Generic, Enum, Bounded)

blendModeFromText :: Text -> Maybe BlendMode
blendModeFromText "normal" = Just BlendNormal
blendModeFromText "multiply" = Just BlendMultiply
blendModeFromText "screen" = Just BlendScreen
blendModeFromText "overlay" = Just BlendOverlay
blendModeFromText "darken" = Just BlendDarken
blendModeFromText "lighten" = Just BlendLighten
blendModeFromText "color-dodge" = Just BlendColorDodge
blendModeFromText "color-burn" = Just BlendColorBurn
blendModeFromText "hard-light" = Just BlendHardLight
blendModeFromText "soft-light" = Just BlendSoftLight
blendModeFromText "difference" = Just BlendDifference
blendModeFromText "exclusion" = Just BlendExclusion
blendModeFromText "hue" = Just BlendHue
blendModeFromText "saturation" = Just BlendSaturation
blendModeFromText "color" = Just BlendColor
blendModeFromText "luminosity" = Just BlendLuminosity
blendModeFromText "add" = Just BlendAdd
blendModeFromText "subtract" = Just BlendSubtract
blendModeFromText "divide" = Just BlendDivide
blendModeFromText "classic-color-dodge" = Just BlendClassicColorDodge
blendModeFromText "classic-color-burn" = Just BlendClassicColorBurn
blendModeFromText "stencil-alpha" = Just BlendStencilAlpha
blendModeFromText "stencil-luma" = Just BlendStencilLuma
blendModeFromText "silhouette-alpha" = Just BlendSilhouetteAlpha
blendModeFromText "silhouette-luma" = Just BlendSilhouetteLuma
blendModeFromText "behind" = Just BlendBehind
blendModeFromText "alpha-add" = Just BlendAlphaAdd
blendModeFromText "dissolve" = Just BlendDissolve
blendModeFromText _ = Nothing

blendModeToText :: BlendMode -> Text
blendModeToText BlendNormal = "normal"
blendModeToText BlendMultiply = "multiply"
blendModeToText BlendScreen = "screen"
blendModeToText BlendOverlay = "overlay"
blendModeToText BlendDarken = "darken"
blendModeToText BlendLighten = "lighten"
blendModeToText BlendColorDodge = "color-dodge"
blendModeToText BlendColorBurn = "color-burn"
blendModeToText BlendHardLight = "hard-light"
blendModeToText BlendSoftLight = "soft-light"
blendModeToText BlendDifference = "difference"
blendModeToText BlendExclusion = "exclusion"
blendModeToText BlendHue = "hue"
blendModeToText BlendSaturation = "saturation"
blendModeToText BlendColor = "color"
blendModeToText BlendLuminosity = "luminosity"
blendModeToText BlendAdd = "add"
blendModeToText BlendSubtract = "subtract"
blendModeToText BlendDivide = "divide"
blendModeToText BlendClassicColorDodge = "classic-color-dodge"
blendModeToText BlendClassicColorBurn = "classic-color-burn"
blendModeToText BlendStencilAlpha = "stencil-alpha"
blendModeToText BlendStencilLuma = "stencil-luma"
blendModeToText BlendSilhouetteAlpha = "silhouette-alpha"
blendModeToText BlendSilhouetteLuma = "silhouette-luma"
blendModeToText BlendBehind = "behind"
blendModeToText BlendAlphaAdd = "alpha-add"
blendModeToText BlendDissolve = "dissolve"

--------------------------------------------------------------------------------
-- Quality Mode
--------------------------------------------------------------------------------

-- | Quality modes for rendering
data QualityMode
  = QualityDraft
  | QualityBest
  deriving stock (Eq, Show, Generic, Enum, Bounded)

qualityModeFromText :: Text -> Maybe QualityMode
qualityModeFromText "draft" = Just QualityDraft
qualityModeFromText "best" = Just QualityBest
qualityModeFromText _ = Nothing

qualityModeToText :: QualityMode -> Text
qualityModeToText QualityDraft = "draft"
qualityModeToText QualityBest = "best"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | 2D vector
data Vec2 = Vec2
  { v2X :: !Double
  , v2Y :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | 3D vector
data Vec3 = Vec3
  { v3X :: !Double
  , v3Y :: !Double
  , v3Z :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | 2D or 3D position with optional z
data Position2DOr3D = Position2DOr3D
  { posX :: !Double
  , posY :: !Double
  , posZ :: !(Maybe Double)
  }
  deriving stock (Eq, Show, Generic)

-- | RGBA color with values 0-1
data RGBAColor = RGBAColor
  { rgbaR :: !Double
  , rgbaG :: !Double
  , rgbaB :: !Double
  , rgbaA :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | RGBA color with values 0-255
data RGBA255Color = RGBA255Color
  { rgba255R :: !Int
  , rgba255G :: !Int
  , rgba255B :: !Int
  , rgba255A :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Rectangle with x, y, width, height
data Rect = Rect
  { rectX :: !Double
  , rectY :: !Double
  , rectWidth :: !Double
  , rectHeight :: !Double
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if Vec2 has finite values
isValidVec2 :: Vec2 -> Bool
isValidVec2 v =
  not (isNaN (v2X v) || isInfinite (v2X v)) &&
  not (isNaN (v2Y v) || isInfinite (v2Y v))

-- | Check if Vec3 has finite values
isValidVec3 :: Vec3 -> Bool
isValidVec3 v =
  not (isNaN (v3X v) || isInfinite (v3X v)) &&
  not (isNaN (v3Y v) || isInfinite (v3Y v)) &&
  not (isNaN (v3Z v) || isInfinite (v3Z v))

-- | Check if Position2DOr3D has finite values
isValidPosition2DOr3D :: Position2DOr3D -> Bool
isValidPosition2DOr3D p =
  not (isNaN (posX p) || isInfinite (posX p)) &&
  not (isNaN (posY p) || isInfinite (posY p)) &&
  maybe True (\z -> not (isNaN z || isInfinite z)) (posZ p)

-- | Check if RGBAColor is valid (0-1 range)
isValidRGBAColor :: RGBAColor -> Bool
isValidRGBAColor c =
  rgbaR c >= 0 && rgbaR c <= 1 &&
  rgbaG c >= 0 && rgbaG c <= 1 &&
  rgbaB c >= 0 && rgbaB c <= 1 &&
  rgbaA c >= 0 && rgbaA c <= 1

-- | Check if RGBA255Color is valid (0-255 range)
isValidRGBA255Color :: RGBA255Color -> Bool
isValidRGBA255Color c =
  rgba255R c >= 0 && rgba255R c <= 255 &&
  rgba255G c >= 0 && rgba255G c <= 255 &&
  rgba255B c >= 0 && rgba255B c <= 255 &&
  rgba255A c >= 0 && rgba255A c <= 255

-- | Check if Rect is valid
isValidRect :: Rect -> Bool
isValidRect r =
  not (isNaN (rectX r) || isInfinite (rectX r)) &&
  not (isNaN (rectY r) || isInfinite (rectY r)) &&
  rectWidth r >= 0 && not (isNaN (rectWidth r) || isInfinite (rectWidth r)) &&
  rectHeight r >= 0 && not (isNaN (rectHeight r) || isInfinite (rectHeight r))
