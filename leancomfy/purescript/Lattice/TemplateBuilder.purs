-- | Lattice.TemplateBuilder - Template Builder System Types
-- |
-- | Source: leancomfy/lean/Lattice/TemplateBuilder.lean

module Lattice.TemplateBuilder
  ( ExpressionControlType(..)
  , ExposedPropertyType(..)
  , AngleDisplayUnit(..)
  , PosterQuality(..)
  , MediaType(..)
  , TemplateBuilderTab(..)
  , FontSource(..)
  , TemplateAssetType(..)
  , DropdownValue(..)
  , DropdownOption
  , ExpressionControlConfig
  , ExpressionControl
  , ExposedPropertyConfig
  , ExposedPropertyDefault(..)
  , ExposedProperty
  , PropertyGroup
  , TemplateComment
  , TemplateExportSettings
  , TemplateConfig
  , TemplateAsset
  , TemplateFont
  , SerializedComposition
  , LatticeTemplate
  , SavedTemplate
  , TemplateBuilderState
  , createDefaultTemplateConfig
  , createPropertyGroup
  , createTemplateComment
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data ExpressionControlType
  = ECTSlider | ECTCheckbox | ECTDropdown | ECTColor | ECTPoint | ECTAngle

derive instance Eq ExpressionControlType
derive instance Generic ExpressionControlType _
instance Show ExpressionControlType where show = genericShow

data ExposedPropertyType
  = EPTSourceText | EPTColor | EPTNumber | EPTCheckbox | EPTDropdown
  | EPTPoint | EPTMedia | EPTFont | EPTLayer

derive instance Eq ExposedPropertyType
derive instance Generic ExposedPropertyType _
instance Show ExposedPropertyType where show = genericShow

data AngleDisplayUnit = ADUDegrees | ADURadians | ADURotations

derive instance Eq AngleDisplayUnit
derive instance Generic AngleDisplayUnit _
instance Show AngleDisplayUnit where show = genericShow

data PosterQuality = PQLow | PQMedium | PQHigh

derive instance Eq PosterQuality
derive instance Generic PosterQuality _
instance Show PosterQuality where show = genericShow

data MediaType = MTImage | MTVideo

derive instance Eq MediaType
derive instance Generic MediaType _
instance Show MediaType where show = genericShow

data TemplateBuilderTab = TBTBrowse | TBTEdit

derive instance Eq TemplateBuilderTab
derive instance Generic TemplateBuilderTab _
instance Show TemplateBuilderTab where show = genericShow

data FontSource = FSGoogle | FSCloud | FSLocal | FSSystem

derive instance Eq FontSource
derive instance Generic FontSource _
instance Show FontSource where show = genericShow

data TemplateAssetType
  = TATDepthMap | TATImage | TATVideo | TATAudio | TATModel | TATPointcloud
  | TATTexture | TATMaterial | TATHDRI | TATSVG | TATSprite | TATSpritesheet | TATLUT

derive instance Eq TemplateAssetType
derive instance Generic TemplateAssetType _
instance Show TemplateAssetType where show = genericShow

--------------------------------------------------------------------------------
-- Dropdown
--------------------------------------------------------------------------------

data DropdownValue
  = DVString String
  | DVNumber FiniteFloat

derive instance Eq DropdownValue
derive instance Generic DropdownValue _
instance Show DropdownValue where show = genericShow

type DropdownOption =
  { label :: NonEmptyString
  , value :: DropdownValue
  }

--------------------------------------------------------------------------------
-- Expression Control
--------------------------------------------------------------------------------

type ExpressionControlConfig =
  { min          :: Maybe FiniteFloat
  , max          :: Maybe FiniteFloat
  , step         :: Maybe PositiveFloat
  , options      :: Array DropdownOption
  , includeAlpha :: Boolean
  , is3D         :: Boolean
  , displayUnit  :: Maybe AngleDisplayUnit
  }

type ExpressionControl =
  { id              :: NonEmptyString
  , name            :: NonEmptyString
  , controlType     :: ExpressionControlType
  , valuePropertyId :: NonEmptyString
  , config          :: ExpressionControlConfig
  , expanded        :: Boolean
  }

--------------------------------------------------------------------------------
-- Exposed Property
--------------------------------------------------------------------------------

type ExposedPropertyConfig =
  { min              :: Maybe FiniteFloat
  , max              :: Maybe FiniteFloat
  , step             :: Maybe PositiveFloat
  , options          :: Array DropdownOption
  , maxLength        :: Maybe Int
  , multiline        :: Boolean
  , acceptedTypes    :: Array MediaType
  , aspectRatio      :: Maybe PositiveFloat
  , allowFontChange  :: Boolean
  , allowSizeChange  :: Boolean
  , allowColorChange :: Boolean
  }

data ExposedPropertyDefault
  = EPDString String
  | EPDNumber FiniteFloat
  | EPDBool Boolean
  | EPDColor { r :: FiniteFloat, g :: FiniteFloat, b :: FiniteFloat, a :: UnitFloat }
  | EPDPoint { x :: FiniteFloat, y :: FiniteFloat }

derive instance Eq ExposedPropertyDefault
derive instance Generic ExposedPropertyDefault _
instance Show ExposedPropertyDefault where show = genericShow

type ExposedProperty =
  { id                 :: NonEmptyString
  , name               :: NonEmptyString
  , propertyType       :: ExposedPropertyType
  , sourceLayerId      :: NonEmptyString
  , sourcePropertyPath :: NonEmptyString
  , sourceControlId    :: Maybe NonEmptyString
  , groupId            :: Maybe NonEmptyString
  , order              :: Int
  , config             :: ExposedPropertyConfig
  , comment            :: Maybe String
  , defaultValue       :: Maybe ExposedPropertyDefault
  }

--------------------------------------------------------------------------------
-- Groups and Comments
--------------------------------------------------------------------------------

type PropertyGroup =
  { id       :: NonEmptyString
  , name     :: NonEmptyString
  , expanded :: Boolean
  , order    :: Int
  , color    :: Maybe HexColor
  }

type TemplateComment =
  { id      :: NonEmptyString
  , text    :: String
  , order   :: Int
  , groupId :: Maybe NonEmptyString
  }

--------------------------------------------------------------------------------
-- Template Config
--------------------------------------------------------------------------------

type TemplateExportSettings =
  { includeFonts        :: Boolean
  , includeMedia        :: Boolean
  , allowDurationChange :: Boolean
  , posterQuality       :: PosterQuality
  }

type TemplateConfig =
  { name                :: NonEmptyString
  , description         :: Maybe String
  , author              :: Maybe String
  , version             :: Maybe String
  , tags                :: Array String
  , masterCompositionId :: NonEmptyString
  , exposedProperties   :: Array ExposedProperty
  , groups              :: Array PropertyGroup
  , comments            :: Array TemplateComment
  , posterFrame         :: FrameNumber
  , exportSettings      :: TemplateExportSettings
  , created             :: NonEmptyString
  , modified            :: NonEmptyString
  }

--------------------------------------------------------------------------------
-- Assets and Fonts
--------------------------------------------------------------------------------

type TemplateAsset =
  { id        :: NonEmptyString
  , name      :: NonEmptyString
  , assetType :: TemplateAssetType
  , data      :: String
  , mimeType  :: NonEmptyString
  }

type TemplateFont =
  { family   :: NonEmptyString
  , style    :: NonEmptyString
  , embedded :: Boolean
  , data     :: Maybe String
  , source   :: Maybe FontSource
  }

--------------------------------------------------------------------------------
-- Template
--------------------------------------------------------------------------------

type SerializedComposition =
  { id                    :: NonEmptyString
  , name                  :: NonEmptyString
  , currentFrame          :: FrameNumber
  , isNestedComp          :: Boolean
  , parentCompositionId   :: Maybe NonEmptyString
  , workflowId            :: Maybe NonEmptyString
  }

type LatticeTemplate =
  { formatVersion  :: NonEmptyString
  , templateConfig :: TemplateConfig
  , composition    :: SerializedComposition
  , assets         :: Array TemplateAsset
  , fonts          :: Array TemplateFont
  , posterImage    :: String
  }

type SavedTemplate =
  { id           :: NonEmptyString
  , name         :: NonEmptyString
  , importedFrom :: Maybe String
  , posterImage  :: String
  , author       :: Maybe String
  , tags         :: Array String
  , importDate   :: NonEmptyString
  , templateData :: Maybe LatticeTemplate
  }

type TemplateBuilderState =
  { activeTab             :: TemplateBuilderTab
  , masterCompositionId   :: Maybe NonEmptyString
  , selectedPropertyIds   :: Array NonEmptyString
  , selectedGroupId       :: Maybe NonEmptyString
  , searchQuery           :: String
  , filterTags            :: Array String
  , savedTemplates        :: Array SavedTemplate
  }

--------------------------------------------------------------------------------
-- Factory Functions
--------------------------------------------------------------------------------

-- | Create default template config
createDefaultTemplateConfig :: NonEmptyString -> NonEmptyString -> NonEmptyString -> TemplateConfig
createDefaultTemplateConfig compId compName timestamp =
  { name: compName
  , description: Nothing
  , author: Nothing
  , version: Nothing
  , tags: []
  , masterCompositionId: compId
  , exposedProperties: []
  , groups: []
  , comments: []
  , posterFrame: FrameNumber 0
  , exportSettings:
      { includeFonts: true
      , includeMedia: true
      , allowDurationChange: false
      , posterQuality: PQHigh
      }
  , created: timestamp
  , modified: timestamp
  }

-- | Create a property group
createPropertyGroup :: NonEmptyString -> NonEmptyString -> Int -> PropertyGroup
createPropertyGroup gid name order =
  { id: gid
  , name
  , expanded: true
  , order
  , color: Nothing
  }

-- | Create a template comment
createTemplateComment :: NonEmptyString -> String -> Int -> TemplateComment
createTemplateComment cid text order =
  { id: cid
  , text
  , order
  , groupId: Nothing
  }
