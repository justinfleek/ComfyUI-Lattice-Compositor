-- | Lattice.Schemas.TemplateBuilder.TemplateBuilderSchema - Template builder enums
-- |
-- | Template builder system enums for Essential Graphics panel.
-- |
-- | Source: ui/src/schemas/templateBuilder/templateBuilder-schema.ts

module Lattice.Schemas.TemplateBuilder.TemplateBuilderSchema
  ( -- Expression Control Type
    ExpressionControlType(..)
  , expressionControlTypeFromString
  , expressionControlTypeToString
    -- Display Unit
  , DisplayUnit(..)
  , displayUnitFromString
  , displayUnitToString
    -- Exposed Property Type
  , ExposedPropertyType(..)
  , exposedPropertyTypeFromString
  , exposedPropertyTypeToString
    -- Accepted Media Type
  , AcceptedMediaType(..)
  , acceptedMediaTypeFromString
  , acceptedMediaTypeToString
    -- Poster Quality
  , PosterQuality(..)
  , posterQualityFromString
  , posterQualityToString
    -- Template Asset Type
  , TemplateAssetType(..)
  , templateAssetTypeFromString
  , templateAssetTypeToString
    -- Font Source
  , FontSource(..)
  , fontSourceFromString
  , fontSourceToString
    -- Template Builder Tab
  , TemplateBuilderTab(..)
  , templateBuilderTabFromString
  , templateBuilderTabToString
    -- Constants
  , maxNameLength
  , maxDescriptionLength
  , maxCommentLength
  , maxTagLength
  , maxTagsCount
  , maxPathLength
  , maxIdLength
  , maxMimeTypeLength
  , maxFontFamilyLength
  , maxFontStyleLength
  , maxUrlLength
  , maxBase64Length
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Expression Control Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Expression control types for expression parameters
data ExpressionControlType
  = CtrlSlider
  | CtrlCheckbox
  | CtrlDropdown
  | CtrlColor
  | CtrlPoint
  | CtrlAngle

derive instance Eq ExpressionControlType
derive instance Generic ExpressionControlType _

instance Show ExpressionControlType where
  show = genericShow

expressionControlTypeFromString :: String -> Maybe ExpressionControlType
expressionControlTypeFromString = case _ of
  "slider" -> Just CtrlSlider
  "checkbox" -> Just CtrlCheckbox
  "dropdown" -> Just CtrlDropdown
  "color" -> Just CtrlColor
  "point" -> Just CtrlPoint
  "angle" -> Just CtrlAngle
  _ -> Nothing

expressionControlTypeToString :: ExpressionControlType -> String
expressionControlTypeToString = case _ of
  CtrlSlider -> "slider"
  CtrlCheckbox -> "checkbox"
  CtrlDropdown -> "dropdown"
  CtrlColor -> "color"
  CtrlPoint -> "point"
  CtrlAngle -> "angle"

-- ────────────────────────────────────────────────────────────────────────────
-- Display Unit
-- ────────────────────────────────────────────────────────────────────────────

-- | Display units for angle controls
data DisplayUnit
  = UnitDegrees
  | UnitRadians
  | UnitRotations

derive instance Eq DisplayUnit
derive instance Generic DisplayUnit _

instance Show DisplayUnit where
  show = genericShow

displayUnitFromString :: String -> Maybe DisplayUnit
displayUnitFromString = case _ of
  "degrees" -> Just UnitDegrees
  "radians" -> Just UnitRadians
  "rotations" -> Just UnitRotations
  _ -> Nothing

displayUnitToString :: DisplayUnit -> String
displayUnitToString = case _ of
  UnitDegrees -> "degrees"
  UnitRadians -> "radians"
  UnitRotations -> "rotations"

-- ────────────────────────────────────────────────────────────────────────────
-- Exposed Property Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Exposed property types for template controls
data ExposedPropertyType
  = PropSourceText
  | PropColor
  | PropNumber
  | PropCheckbox
  | PropDropdown
  | PropPoint
  | PropMedia
  | PropFont
  | PropLayer

derive instance Eq ExposedPropertyType
derive instance Generic ExposedPropertyType _

instance Show ExposedPropertyType where
  show = genericShow

exposedPropertyTypeFromString :: String -> Maybe ExposedPropertyType
exposedPropertyTypeFromString = case _ of
  "sourceText" -> Just PropSourceText
  "color" -> Just PropColor
  "number" -> Just PropNumber
  "checkbox" -> Just PropCheckbox
  "dropdown" -> Just PropDropdown
  "point" -> Just PropPoint
  "media" -> Just PropMedia
  "font" -> Just PropFont
  "layer" -> Just PropLayer
  _ -> Nothing

exposedPropertyTypeToString :: ExposedPropertyType -> String
exposedPropertyTypeToString = case _ of
  PropSourceText -> "sourceText"
  PropColor -> "color"
  PropNumber -> "number"
  PropCheckbox -> "checkbox"
  PropDropdown -> "dropdown"
  PropPoint -> "point"
  PropMedia -> "media"
  PropFont -> "font"
  PropLayer -> "layer"

-- ────────────────────────────────────────────────────────────────────────────
-- Accepted Media Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Accepted media types for media controls
data AcceptedMediaType
  = MediaImage
  | MediaVideo

derive instance Eq AcceptedMediaType
derive instance Generic AcceptedMediaType _

instance Show AcceptedMediaType where
  show = genericShow

acceptedMediaTypeFromString :: String -> Maybe AcceptedMediaType
acceptedMediaTypeFromString = case _ of
  "image" -> Just MediaImage
  "video" -> Just MediaVideo
  _ -> Nothing

acceptedMediaTypeToString :: AcceptedMediaType -> String
acceptedMediaTypeToString = case _ of
  MediaImage -> "image"
  MediaVideo -> "video"

-- ────────────────────────────────────────────────────────────────────────────
-- Poster Quality
-- ────────────────────────────────────────────────────────────────────────────

-- | Poster export quality levels
data PosterQuality
  = QualityLow
  | QualityMedium
  | QualityHigh

derive instance Eq PosterQuality
derive instance Generic PosterQuality _

instance Show PosterQuality where
  show = genericShow

posterQualityFromString :: String -> Maybe PosterQuality
posterQualityFromString = case _ of
  "low" -> Just QualityLow
  "medium" -> Just QualityMedium
  "high" -> Just QualityHigh
  _ -> Nothing

posterQualityToString :: PosterQuality -> String
posterQualityToString = case _ of
  QualityLow -> "low"
  QualityMedium -> "medium"
  QualityHigh -> "high"

-- ────────────────────────────────────────────────────────────────────────────
-- Template Asset Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Template asset types
data TemplateAssetType
  = AssetDepthMap
  | AssetImage
  | AssetVideo
  | AssetAudio
  | AssetModel
  | AssetPointcloud
  | AssetTexture
  | AssetMaterial
  | AssetHdri
  | AssetSvg
  | AssetSprite
  | AssetSpritesheet
  | AssetLut

derive instance Eq TemplateAssetType
derive instance Generic TemplateAssetType _

instance Show TemplateAssetType where
  show = genericShow

templateAssetTypeFromString :: String -> Maybe TemplateAssetType
templateAssetTypeFromString = case _ of
  "depth_map" -> Just AssetDepthMap
  "image" -> Just AssetImage
  "video" -> Just AssetVideo
  "audio" -> Just AssetAudio
  "model" -> Just AssetModel
  "pointcloud" -> Just AssetPointcloud
  "texture" -> Just AssetTexture
  "material" -> Just AssetMaterial
  "hdri" -> Just AssetHdri
  "svg" -> Just AssetSvg
  "sprite" -> Just AssetSprite
  "spritesheet" -> Just AssetSpritesheet
  "lut" -> Just AssetLut
  _ -> Nothing

templateAssetTypeToString :: TemplateAssetType -> String
templateAssetTypeToString = case _ of
  AssetDepthMap -> "depth_map"
  AssetImage -> "image"
  AssetVideo -> "video"
  AssetAudio -> "audio"
  AssetModel -> "model"
  AssetPointcloud -> "pointcloud"
  AssetTexture -> "texture"
  AssetMaterial -> "material"
  AssetHdri -> "hdri"
  AssetSvg -> "svg"
  AssetSprite -> "sprite"
  AssetSpritesheet -> "spritesheet"
  AssetLut -> "lut"

-- ────────────────────────────────────────────────────────────────────────────
-- Font Source
-- ────────────────────────────────────────────────────────────────────────────

-- | Font sources for embedded fonts
data FontSource
  = SourceGoogle
  | SourceCloud
  | SourceLocal
  | SourceSystem

derive instance Eq FontSource
derive instance Generic FontSource _

instance Show FontSource where
  show = genericShow

fontSourceFromString :: String -> Maybe FontSource
fontSourceFromString = case _ of
  "google" -> Just SourceGoogle
  "cloud" -> Just SourceCloud
  "local" -> Just SourceLocal
  "system" -> Just SourceSystem
  _ -> Nothing

fontSourceToString :: FontSource -> String
fontSourceToString = case _ of
  SourceGoogle -> "google"
  SourceCloud -> "cloud"
  SourceLocal -> "local"
  SourceSystem -> "system"

-- ────────────────────────────────────────────────────────────────────────────
-- Template Builder Tab
-- ────────────────────────────────────────────────────────────────────────────

-- | Template builder panel tabs
data TemplateBuilderTab
  = TabBrowse
  | TabEdit

derive instance Eq TemplateBuilderTab
derive instance Generic TemplateBuilderTab _

instance Show TemplateBuilderTab where
  show = genericShow

templateBuilderTabFromString :: String -> Maybe TemplateBuilderTab
templateBuilderTabFromString = case _ of
  "browse" -> Just TabBrowse
  "edit" -> Just TabEdit
  _ -> Nothing

templateBuilderTabToString :: TemplateBuilderTab -> String
templateBuilderTabToString = case _ of
  TabBrowse -> "browse"
  TabEdit -> "edit"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxNameLength :: Int
maxNameLength = 200

maxDescriptionLength :: Int
maxDescriptionLength = 2000

maxCommentLength :: Int
maxCommentLength = 5000

maxTagLength :: Int
maxTagLength = 50

maxTagsCount :: Int
maxTagsCount = 50

maxPathLength :: Int
maxPathLength = 500

maxIdLength :: Int
maxIdLength = 200

maxMimeTypeLength :: Int
maxMimeTypeLength = 100

maxFontFamilyLength :: Int
maxFontFamilyLength = 200

maxFontStyleLength :: Int
maxFontStyleLength = 100

maxUrlLength :: Int
maxUrlLength = 2048

maxBase64Length :: Int
maxBase64Length = 50 * 1024 * 1024  -- 50MB
