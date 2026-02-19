{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.TemplateBuilder.TemplateBuilderSchema
Description : Template builder enums
Copyright   : (c) Lattice, 2026
License     : MIT

Template builder system enums for Essential Graphics panel.

Source: ui/src/schemas/templateBuilder/templateBuilder-schema.ts
-}

module Lattice.Schemas.TemplateBuilder.TemplateBuilderSchema
  ( -- * Expression Control Type
    ExpressionControlType(..)
  , expressionControlTypeFromText
  , expressionControlTypeToText
    -- * Display Unit
  , DisplayUnit(..)
  , displayUnitFromText
  , displayUnitToText
    -- * Exposed Property Type
  , ExposedPropertyType(..)
  , exposedPropertyTypeFromText
  , exposedPropertyTypeToText
    -- * Accepted Media Type
  , AcceptedMediaType(..)
  , acceptedMediaTypeFromText
  , acceptedMediaTypeToText
    -- * Poster Quality
  , PosterQuality(..)
  , posterQualityFromText
  , posterQualityToText
    -- * Template Asset Type
  , TemplateAssetType(..)
  , templateAssetTypeFromText
  , templateAssetTypeToText
    -- * Font Source
  , FontSource(..)
  , fontSourceFromText
  , fontSourceToText
    -- * Template Builder Tab
  , TemplateBuilderTab(..)
  , templateBuilderTabFromText
  , templateBuilderTabToText
    -- * Constants
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

import GHC.Generics (Generic)
import Data.Text (Text)

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

expressionControlTypeFromText :: Text -> Maybe ExpressionControlType
expressionControlTypeFromText "slider" = Just CtrlSlider
expressionControlTypeFromText "checkbox" = Just CtrlCheckbox
expressionControlTypeFromText "dropdown" = Just CtrlDropdown
expressionControlTypeFromText "color" = Just CtrlColor
expressionControlTypeFromText "point" = Just CtrlPoint
expressionControlTypeFromText "angle" = Just CtrlAngle
expressionControlTypeFromText _ = Nothing

expressionControlTypeToText :: ExpressionControlType -> Text
expressionControlTypeToText CtrlSlider = "slider"
expressionControlTypeToText CtrlCheckbox = "checkbox"
expressionControlTypeToText CtrlDropdown = "dropdown"
expressionControlTypeToText CtrlColor = "color"
expressionControlTypeToText CtrlPoint = "point"
expressionControlTypeToText CtrlAngle = "angle"

-- ────────────────────────────────────────────────────────────────────────────
-- Display Unit
-- ────────────────────────────────────────────────────────────────────────────

-- | Display units for angle controls
data DisplayUnit
  = UnitDegrees
  | UnitRadians
  | UnitRotations
  deriving stock (Eq, Show, Generic, Enum, Bounded)

displayUnitFromText :: Text -> Maybe DisplayUnit
displayUnitFromText "degrees" = Just UnitDegrees
displayUnitFromText "radians" = Just UnitRadians
displayUnitFromText "rotations" = Just UnitRotations
displayUnitFromText _ = Nothing

displayUnitToText :: DisplayUnit -> Text
displayUnitToText UnitDegrees = "degrees"
displayUnitToText UnitRadians = "radians"
displayUnitToText UnitRotations = "rotations"

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

exposedPropertyTypeFromText :: Text -> Maybe ExposedPropertyType
exposedPropertyTypeFromText "sourceText" = Just PropSourceText
exposedPropertyTypeFromText "color" = Just PropColor
exposedPropertyTypeFromText "number" = Just PropNumber
exposedPropertyTypeFromText "checkbox" = Just PropCheckbox
exposedPropertyTypeFromText "dropdown" = Just PropDropdown
exposedPropertyTypeFromText "point" = Just PropPoint
exposedPropertyTypeFromText "media" = Just PropMedia
exposedPropertyTypeFromText "font" = Just PropFont
exposedPropertyTypeFromText "layer" = Just PropLayer
exposedPropertyTypeFromText _ = Nothing

exposedPropertyTypeToText :: ExposedPropertyType -> Text
exposedPropertyTypeToText PropSourceText = "sourceText"
exposedPropertyTypeToText PropColor = "color"
exposedPropertyTypeToText PropNumber = "number"
exposedPropertyTypeToText PropCheckbox = "checkbox"
exposedPropertyTypeToText PropDropdown = "dropdown"
exposedPropertyTypeToText PropPoint = "point"
exposedPropertyTypeToText PropMedia = "media"
exposedPropertyTypeToText PropFont = "font"
exposedPropertyTypeToText PropLayer = "layer"

-- ────────────────────────────────────────────────────────────────────────────
-- Accepted Media Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Accepted media types for media controls
data AcceptedMediaType
  = MediaImage
  | MediaVideo
  deriving stock (Eq, Show, Generic, Enum, Bounded)

acceptedMediaTypeFromText :: Text -> Maybe AcceptedMediaType
acceptedMediaTypeFromText "image" = Just MediaImage
acceptedMediaTypeFromText "video" = Just MediaVideo
acceptedMediaTypeFromText _ = Nothing

acceptedMediaTypeToText :: AcceptedMediaType -> Text
acceptedMediaTypeToText MediaImage = "image"
acceptedMediaTypeToText MediaVideo = "video"

-- ────────────────────────────────────────────────────────────────────────────
-- Poster Quality
-- ────────────────────────────────────────────────────────────────────────────

-- | Poster export quality levels
data PosterQuality
  = QualityLow
  | QualityMedium
  | QualityHigh
  deriving stock (Eq, Show, Generic, Enum, Bounded)

posterQualityFromText :: Text -> Maybe PosterQuality
posterQualityFromText "low" = Just QualityLow
posterQualityFromText "medium" = Just QualityMedium
posterQualityFromText "high" = Just QualityHigh
posterQualityFromText _ = Nothing

posterQualityToText :: PosterQuality -> Text
posterQualityToText QualityLow = "low"
posterQualityToText QualityMedium = "medium"
posterQualityToText QualityHigh = "high"

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

templateAssetTypeFromText :: Text -> Maybe TemplateAssetType
templateAssetTypeFromText "depth_map" = Just AssetDepthMap
templateAssetTypeFromText "image" = Just AssetImage
templateAssetTypeFromText "video" = Just AssetVideo
templateAssetTypeFromText "audio" = Just AssetAudio
templateAssetTypeFromText "model" = Just AssetModel
templateAssetTypeFromText "pointcloud" = Just AssetPointcloud
templateAssetTypeFromText "texture" = Just AssetTexture
templateAssetTypeFromText "material" = Just AssetMaterial
templateAssetTypeFromText "hdri" = Just AssetHdri
templateAssetTypeFromText "svg" = Just AssetSvg
templateAssetTypeFromText "sprite" = Just AssetSprite
templateAssetTypeFromText "spritesheet" = Just AssetSpritesheet
templateAssetTypeFromText "lut" = Just AssetLut
templateAssetTypeFromText _ = Nothing

templateAssetTypeToText :: TemplateAssetType -> Text
templateAssetTypeToText AssetDepthMap = "depth_map"
templateAssetTypeToText AssetImage = "image"
templateAssetTypeToText AssetVideo = "video"
templateAssetTypeToText AssetAudio = "audio"
templateAssetTypeToText AssetModel = "model"
templateAssetTypeToText AssetPointcloud = "pointcloud"
templateAssetTypeToText AssetTexture = "texture"
templateAssetTypeToText AssetMaterial = "material"
templateAssetTypeToText AssetHdri = "hdri"
templateAssetTypeToText AssetSvg = "svg"
templateAssetTypeToText AssetSprite = "sprite"
templateAssetTypeToText AssetSpritesheet = "spritesheet"
templateAssetTypeToText AssetLut = "lut"

-- ────────────────────────────────────────────────────────────────────────────
-- Font Source
-- ────────────────────────────────────────────────────────────────────────────

-- | Font sources for embedded fonts
data FontSource
  = SourceGoogle
  | SourceCloud
  | SourceLocal
  | SourceSystem
  deriving stock (Eq, Show, Generic, Enum, Bounded)

fontSourceFromText :: Text -> Maybe FontSource
fontSourceFromText "google" = Just SourceGoogle
fontSourceFromText "cloud" = Just SourceCloud
fontSourceFromText "local" = Just SourceLocal
fontSourceFromText "system" = Just SourceSystem
fontSourceFromText _ = Nothing

fontSourceToText :: FontSource -> Text
fontSourceToText SourceGoogle = "google"
fontSourceToText SourceCloud = "cloud"
fontSourceToText SourceLocal = "local"
fontSourceToText SourceSystem = "system"

-- ────────────────────────────────────────────────────────────────────────────
-- Template Builder Tab
-- ────────────────────────────────────────────────────────────────────────────

-- | Template builder panel tabs
data TemplateBuilderTab
  = TabBrowse
  | TabEdit
  deriving stock (Eq, Show, Generic, Enum, Bounded)

templateBuilderTabFromText :: Text -> Maybe TemplateBuilderTab
templateBuilderTabFromText "browse" = Just TabBrowse
templateBuilderTabFromText "edit" = Just TabEdit
templateBuilderTabFromText _ = Nothing

templateBuilderTabToText :: TemplateBuilderTab -> Text
templateBuilderTabToText TabBrowse = "browse"
templateBuilderTabToText TabEdit = "edit"

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
