{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.TemplateBuilder
Description : Template Builder System Types
Copyright   : (c) Lattice, 2026
License     : MIT

Source: lattice-core/lean/Lattice/TemplateBuilder.lean
-}

module Lattice.TemplateBuilder
  ( -- * Enumerations
    ExpressionControlType(..)
  , ExposedPropertyType(..)
  , AngleDisplayUnit(..)
  , PosterQuality(..)
  , MediaType(..)
  , TemplateBuilderTab(..)
  , FontSource(..)
  , TemplateAssetType(..)
    -- * Dropdown
  , DropdownValue(..)
  , DropdownOption(..)
    -- * Expression Control
  , ExpressionControlConfig(..)
  , ExpressionControl(..)
    -- * Exposed Property
  , ExposedPropertyConfig(..)
  , ExposedPropertyDefault(..)
  , ExposedProperty(..)
    -- * Groups and Comments
  , PropertyGroup(..)
  , TemplateComment(..)
    -- * Template Config
  , TemplateExportSettings(..)
  , TemplateConfig(..)
    -- * Assets and Fonts
  , TemplateAsset(..)
  , TemplateFont(..)
    -- * Template
  , SerializedComposition(..)
  , LatticeTemplate(..)
  , SavedTemplate(..)
  , TemplateBuilderState(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data ExpressionControlType
  = ECTSlider | ECTCheckbox | ECTDropdown | ECTColor | ECTPoint | ECTAngle
  deriving stock (Eq, Show, Generic)

data ExposedPropertyType
  = EPTSourceText | EPTColor | EPTNumber | EPTCheckbox | EPTDropdown
  | EPTPoint | EPTMedia | EPTFont | EPTLayer
  deriving stock (Eq, Show, Generic)

data AngleDisplayUnit = ADUDegrees | ADURadians | ADURotations
  deriving stock (Eq, Show, Generic)

data PosterQuality = PQLow | PQMedium | PQHigh
  deriving stock (Eq, Show, Generic)

data MediaType = MTImage | MTVideo
  deriving stock (Eq, Show, Generic)

data TemplateBuilderTab = TBTBrowse | TBTEdit
  deriving stock (Eq, Show, Generic)

data FontSource = FSGoogle | FSCloud | FSLocal | FSSystem
  deriving stock (Eq, Show, Generic)

data TemplateAssetType
  = TATDepthMap | TATImage | TATVideo | TATAudio | TATModel | TATPointcloud
  | TATTexture | TATMaterial | TATHDRI | TATSVG | TATSprite | TATSpritesheet | TATLUT
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Dropdown
--------------------------------------------------------------------------------

data DropdownValue
  = DVString !Text
  | DVNumber !FiniteFloat
  deriving stock (Eq, Show, Generic)

data DropdownOption = DropdownOption
  { doLabel :: !NonEmptyString
  , doValue :: !DropdownValue
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Expression Control
--------------------------------------------------------------------------------

data ExpressionControlConfig = ExpressionControlConfig
  { eccMin          :: !(Maybe FiniteFloat)
  , eccMax          :: !(Maybe FiniteFloat)
  , eccStep         :: !(Maybe PositiveFloat)
  , eccOptions      :: !(Vector DropdownOption)
  , eccIncludeAlpha :: !Bool
  , eccIs3D         :: !Bool
  , eccDisplayUnit  :: !(Maybe AngleDisplayUnit)
  } deriving stock (Eq, Show, Generic)

data ExpressionControl = ExpressionControl
  { ecId              :: !NonEmptyString
  , ecName            :: !NonEmptyString
  , ecControlType     :: !ExpressionControlType
  , ecValuePropertyId :: !NonEmptyString
  , ecConfig          :: !ExpressionControlConfig
  , ecExpanded        :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Exposed Property
--------------------------------------------------------------------------------

data ExposedPropertyConfig = ExposedPropertyConfig
  { epcMin              :: !(Maybe FiniteFloat)
  , epcMax              :: !(Maybe FiniteFloat)
  , epcStep             :: !(Maybe PositiveFloat)
  , epcOptions          :: !(Vector DropdownOption)
  , epcMaxLength        :: !(Maybe Int)
  , epcMultiline        :: !Bool
  , epcAcceptedTypes    :: !(Vector MediaType)
  , epcAspectRatio      :: !(Maybe PositiveFloat)
  , epcAllowFontChange  :: !Bool
  , epcAllowSizeChange  :: !Bool
  , epcAllowColorChange :: !Bool
  } deriving stock (Eq, Show, Generic)

data ExposedPropertyDefault
  = EPDString !Text
  | EPDNumber !FiniteFloat
  | EPDBool !Bool
  | EPDColor !FiniteFloat !FiniteFloat !FiniteFloat !UnitFloat  -- RGBA
  | EPDPoint !FiniteFloat !FiniteFloat
  deriving stock (Eq, Show, Generic)

data ExposedProperty = ExposedProperty
  { epId                :: !NonEmptyString
  , epName              :: !NonEmptyString
  , epPropertyType      :: !ExposedPropertyType
  , epSourceLayerId     :: !NonEmptyString
  , epSourcePropertyPath :: !NonEmptyString
  , epSourceControlId   :: !(Maybe NonEmptyString)
  , epGroupId           :: !(Maybe NonEmptyString)
  , epOrder             :: !Int
  , epConfig            :: !ExposedPropertyConfig
  , epComment           :: !(Maybe Text)
  , epDefaultValue      :: !(Maybe ExposedPropertyDefault)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Groups and Comments
--------------------------------------------------------------------------------

data PropertyGroup = PropertyGroup
  { pgId       :: !NonEmptyString
  , pgName     :: !NonEmptyString
  , pgExpanded :: !Bool
  , pgOrder    :: !Int
  , pgColor    :: !(Maybe HexColor)
  } deriving stock (Eq, Show, Generic)

data TemplateComment = TemplateComment
  { tcId      :: !NonEmptyString
  , tcText    :: !Text
  , tcOrder   :: !Int
  , tcGroupId :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Template Config
--------------------------------------------------------------------------------

data TemplateExportSettings = TemplateExportSettings
  { tesIncludeFonts        :: !Bool
  , tesIncludeMedia        :: !Bool
  , tesAllowDurationChange :: !Bool
  , tesPosterQuality       :: !PosterQuality
  } deriving stock (Eq, Show, Generic)

data TemplateConfig = TemplateConfig
  { tcfgName                :: !NonEmptyString
  , tcfgDescription         :: !(Maybe Text)
  , tcfgAuthor              :: !(Maybe Text)
  , tcfgVersion             :: !(Maybe Text)
  , tcfgTags                :: !(Vector Text)
  , tcfgMasterCompositionId :: !NonEmptyString
  , tcfgExposedProperties   :: !(Vector ExposedProperty)
  , tcfgGroups              :: !(Vector PropertyGroup)
  , tcfgComments            :: !(Vector TemplateComment)
  , tcfgPosterFrame         :: !FrameNumber
  , tcfgExportSettings      :: !TemplateExportSettings
  , tcfgCreated             :: !NonEmptyString  -- ISO 8601
  , tcfgModified            :: !NonEmptyString  -- ISO 8601
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Assets and Fonts
--------------------------------------------------------------------------------

data TemplateAsset = TemplateAsset
  { taId        :: !NonEmptyString
  , taName      :: !NonEmptyString
  , taAssetType :: !TemplateAssetType
  , taData      :: !Text  -- Base64 or URL
  , taMimeType  :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data TemplateFont = TemplateFont
  { tfFamily   :: !NonEmptyString
  , tfStyle    :: !NonEmptyString
  , tfEmbedded :: !Bool
  , tfData     :: !(Maybe Text)  -- Base64 if embedded
  , tfSource   :: !(Maybe FontSource)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Template
--------------------------------------------------------------------------------

data SerializedComposition = SerializedComposition
  { scId                    :: !NonEmptyString
  , scName                  :: !NonEmptyString
  , scCurrentFrame          :: !FrameNumber
  , scIsNestedComp          :: !Bool
  , scParentCompositionId   :: !(Maybe NonEmptyString)
  , scWorkflowId            :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data LatticeTemplate = LatticeTemplate
  { ltFormatVersion  :: !NonEmptyString
  , ltTemplateConfig :: !TemplateConfig
  , ltComposition    :: !SerializedComposition
  , ltAssets         :: !(Vector TemplateAsset)
  , ltFonts          :: !(Vector TemplateFont)
  , ltPosterImage    :: !Text  -- Base64
  } deriving stock (Eq, Show, Generic)

data SavedTemplate = SavedTemplate
  { stId           :: !NonEmptyString
  , stName         :: !NonEmptyString
  , stImportedFrom :: !(Maybe Text)
  , stPosterImage  :: !Text
  , stAuthor       :: !(Maybe Text)
  , stTags         :: !(Vector Text)
  , stImportDate   :: !NonEmptyString  -- ISO 8601
  , stTemplateData :: !(Maybe LatticeTemplate)
  } deriving stock (Eq, Show, Generic)

data TemplateBuilderState = TemplateBuilderState
  { tbsActiveTab             :: !TemplateBuilderTab
  , tbsMasterCompositionId   :: !(Maybe NonEmptyString)
  , tbsSelectedPropertyIds   :: !(Vector NonEmptyString)
  , tbsSelectedGroupId       :: !(Maybe NonEmptyString)
  , tbsSearchQuery           :: !Text
  , tbsFilterTags            :: !(Vector Text)
  , tbsSavedTemplates        :: !(Vector SavedTemplate)
  } deriving stock (Eq, Show, Generic)
