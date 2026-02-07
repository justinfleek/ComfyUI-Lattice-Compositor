-- | Lattice.Schemas.Layers.PrimitivesSchema - Layer primitive enums and types
-- |
-- | Foundational layer data types: blend modes, vectors, colors.
-- |
-- | Source: ui/src/schemas/layers/primitives-schema.ts

module Lattice.Schemas.Layers.PrimitivesSchema
  ( -- Blend Mode
    BlendMode(..)
  , blendModeFromString
  , blendModeToString
    -- Quality Mode
  , QualityMode(..)
  , qualityModeFromString
  , qualityModeToString
    -- Structures
  , Vec2
  , Vec3
  , Position2DOr3D
  , RGBAColor
  , RGBA255Color
  , Rect
    -- Validation
  , isValidVec2
  , isValidVec3
  , isValidPosition2DOr3D
  , isValidRGBAColor
  , isValidRGBA255Color
  , isValidRect
  ) where

import Prelude
import Data.Maybe (Maybe(..), maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Number (isFinite)

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

derive instance Eq BlendMode
derive instance Generic BlendMode _

instance Show BlendMode where
  show = genericShow

blendModeFromString :: String -> Maybe BlendMode
blendModeFromString = case _ of
  "normal" -> Just BlendNormal
  "multiply" -> Just BlendMultiply
  "screen" -> Just BlendScreen
  "overlay" -> Just BlendOverlay
  "darken" -> Just BlendDarken
  "lighten" -> Just BlendLighten
  "color-dodge" -> Just BlendColorDodge
  "color-burn" -> Just BlendColorBurn
  "hard-light" -> Just BlendHardLight
  "soft-light" -> Just BlendSoftLight
  "difference" -> Just BlendDifference
  "exclusion" -> Just BlendExclusion
  "hue" -> Just BlendHue
  "saturation" -> Just BlendSaturation
  "color" -> Just BlendColor
  "luminosity" -> Just BlendLuminosity
  "add" -> Just BlendAdd
  "subtract" -> Just BlendSubtract
  "divide" -> Just BlendDivide
  "classic-color-dodge" -> Just BlendClassicColorDodge
  "classic-color-burn" -> Just BlendClassicColorBurn
  "stencil-alpha" -> Just BlendStencilAlpha
  "stencil-luma" -> Just BlendStencilLuma
  "silhouette-alpha" -> Just BlendSilhouetteAlpha
  "silhouette-luma" -> Just BlendSilhouetteLuma
  "behind" -> Just BlendBehind
  "alpha-add" -> Just BlendAlphaAdd
  "dissolve" -> Just BlendDissolve
  _ -> Nothing

blendModeToString :: BlendMode -> String
blendModeToString = case _ of
  BlendNormal -> "normal"
  BlendMultiply -> "multiply"
  BlendScreen -> "screen"
  BlendOverlay -> "overlay"
  BlendDarken -> "darken"
  BlendLighten -> "lighten"
  BlendColorDodge -> "color-dodge"
  BlendColorBurn -> "color-burn"
  BlendHardLight -> "hard-light"
  BlendSoftLight -> "soft-light"
  BlendDifference -> "difference"
  BlendExclusion -> "exclusion"
  BlendHue -> "hue"
  BlendSaturation -> "saturation"
  BlendColor -> "color"
  BlendLuminosity -> "luminosity"
  BlendAdd -> "add"
  BlendSubtract -> "subtract"
  BlendDivide -> "divide"
  BlendClassicColorDodge -> "classic-color-dodge"
  BlendClassicColorBurn -> "classic-color-burn"
  BlendStencilAlpha -> "stencil-alpha"
  BlendStencilLuma -> "stencil-luma"
  BlendSilhouetteAlpha -> "silhouette-alpha"
  BlendSilhouetteLuma -> "silhouette-luma"
  BlendBehind -> "behind"
  BlendAlphaAdd -> "alpha-add"
  BlendDissolve -> "dissolve"

--------------------------------------------------------------------------------
-- Quality Mode
--------------------------------------------------------------------------------

-- | Quality modes for rendering
data QualityMode
  = QualityDraft
  | QualityBest

derive instance Eq QualityMode
derive instance Generic QualityMode _

instance Show QualityMode where
  show = genericShow

qualityModeFromString :: String -> Maybe QualityMode
qualityModeFromString = case _ of
  "draft" -> Just QualityDraft
  "best" -> Just QualityBest
  _ -> Nothing

qualityModeToString :: QualityMode -> String
qualityModeToString = case _ of
  QualityDraft -> "draft"
  QualityBest -> "best"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | 2D vector
type Vec2 =
  { x :: Number
  , y :: Number
  }

-- | 3D vector
type Vec3 =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | 2D or 3D position with optional z
type Position2DOr3D =
  { x :: Number
  , y :: Number
  , z :: Maybe Number
  }

-- | RGBA color with values 0-1
type RGBAColor =
  { r :: Number
  , g :: Number
  , b :: Number
  , a :: Number
  }

-- | RGBA color with values 0-255
type RGBA255Color =
  { r :: Int
  , g :: Int
  , b :: Int
  , a :: Int
  }

-- | Rectangle with x, y, width, height
type Rect =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if Vec2 has finite values
isValidVec2 :: Vec2 -> Boolean
isValidVec2 v = isFinite v.x && isFinite v.y

-- | Check if Vec3 has finite values
isValidVec3 :: Vec3 -> Boolean
isValidVec3 v = isFinite v.x && isFinite v.y && isFinite v.z

-- | Check if Position2DOr3D has finite values
isValidPosition2DOr3D :: Position2DOr3D -> Boolean
isValidPosition2DOr3D p =
  isFinite p.x && isFinite p.y &&
  maybe true isFinite p.z

-- | Check if RGBAColor is valid (0-1 range)
isValidRGBAColor :: RGBAColor -> Boolean
isValidRGBAColor c =
  c.r >= 0.0 && c.r <= 1.0 &&
  c.g >= 0.0 && c.g <= 1.0 &&
  c.b >= 0.0 && c.b <= 1.0 &&
  c.a >= 0.0 && c.a <= 1.0

-- | Check if RGBA255Color is valid (0-255 range)
isValidRGBA255Color :: RGBA255Color -> Boolean
isValidRGBA255Color c =
  c.r >= 0 && c.r <= 255 &&
  c.g >= 0 && c.g <= 255 &&
  c.b >= 0 && c.b <= 255 &&
  c.a >= 0 && c.a <= 255

-- | Check if Rect is valid
isValidRect :: Rect -> Boolean
isValidRect r =
  isFinite r.x && isFinite r.y &&
  r.width >= 0.0 && isFinite r.width &&
  r.height >= 0.0 && isFinite r.height
