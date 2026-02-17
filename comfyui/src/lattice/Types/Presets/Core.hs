-- |
-- Module      : Lattice.Types.Presets.Core
-- Description : Core types for preset system (particles, effects, animations, etc.)
-- 
-- Migrated from ui/src/types/presets.ts
-- Defines types for saving and loading presets for particles, effects,
-- animations, and other configurable elements.
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Presets.Core
  ( -- Preset category
    PresetCategory (..),
    -- Base preset metadata
    PresetMetadata (..),
    -- Preset types
    ParticlePreset (..),
    ParticlePresetConfig (..),
    EffectPreset (..),
    EffectPresetItem (..),
    PathEffectPreset (..),
    CameraShakePreset (..),
    CameraTrajectoryPreset (..),
    TextStylePreset (..),
    TextStyleConfig (..),
    TextAlign (..),
    ColorPalettePreset (..),
    AnimationPreset (..),
    AnimationPresetKeyframe (..),
    AnimationPresetProperty (..),
    -- Union type
    Preset (..),
    -- Collection
    PresetCollection (..),
  )
where

import Data.Aeson
  ( ToJSON (..),
    FromJSON (..),
    withObject,
    withText,
    object,
    (.=),
    (.:),
    (.:?),
    Value (..),
  )
import Data.Aeson.Key (fromText, toText)
import Data.Aeson.KeyMap (toList)
import Data.Aeson.Types (Parser)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Animation (PropertyValue (..))
import Lattice.Schema.SharedValidation (validateBoundedArray)

-- ============================================================================
-- PRESET CATEGORIES
-- ============================================================================

-- | Preset category
data PresetCategory
  = PresetCategoryParticle
  | PresetCategoryEffect
  | PresetCategoryAnimation
  | PresetCategoryCameraShake
  | PresetCategoryCameraTrajectory
  | PresetCategoryPathEffect
  | PresetCategoryTextStyle
  | PresetCategoryColorPalette
  deriving (Eq, Show, Generic)

instance ToJSON PresetCategory where
  toJSON PresetCategoryParticle = "particle"
  toJSON PresetCategoryEffect = "effect"
  toJSON PresetCategoryAnimation = "animation"
  toJSON PresetCategoryCameraShake = "camera-shake"
  toJSON PresetCategoryCameraTrajectory = "camera-trajectory"
  toJSON PresetCategoryPathEffect = "path-effect"
  toJSON PresetCategoryTextStyle = "text-style"
  toJSON PresetCategoryColorPalette = "color-palette"

instance FromJSON PresetCategory where
  parseJSON = withText "PresetCategory" $ \s ->
    case s of
      t | t == T.pack "particle" -> return PresetCategoryParticle
      t | t == T.pack "effect" -> return PresetCategoryEffect
      t | t == T.pack "animation" -> return PresetCategoryAnimation
      t | t == T.pack "camera-shake" -> return PresetCategoryCameraShake
      t | t == T.pack "camera-trajectory" -> return PresetCategoryCameraTrajectory
      t | t == T.pack "path-effect" -> return PresetCategoryPathEffect
      t | t == T.pack "text-style" -> return PresetCategoryTextStyle
      t | t == T.pack "color-palette" -> return PresetCategoryColorPalette
      _ -> fail "Invalid PresetCategory"

-- ============================================================================
-- BASE PRESET METADATA
-- ============================================================================

-- | Base preset metadata
data PresetMetadata = PresetMetadata
  { presetMetadataId :: Text,
    presetMetadataName :: Text,
    presetMetadataCategory :: PresetCategory,
    presetMetadataDescription :: Maybe Text,
    presetMetadataTags :: Maybe [Text],
    presetMetadataAuthor :: Maybe Text,
    presetMetadataCreatedAt :: Double, -- Unix timestamp (milliseconds)
    presetMetadataUpdatedAt :: Double, -- Unix timestamp (milliseconds)
    presetMetadataThumbnail :: Maybe Text, -- Base64 data URL
    presetMetadataIsBuiltIn :: Maybe Bool,
    presetMetadataVersion :: Maybe Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON PresetMetadata where
  toJSON (PresetMetadata id_ name category description tags author createdAt updatedAt thumbnail isBuiltIn version) =
    object $
      concat
        [ [ "id" .= id_,
            "name" .= name,
            "category" .= category,
            "createdAt" .= createdAt,
            "updatedAt" .= updatedAt
          ],
          maybe [] (\d -> ["description" .= d]) description,
          maybe [] (\t -> ["tags" .= t]) tags,
          maybe [] (\a -> ["author" .= a]) author,
          maybe [] (\th -> ["thumbnail" .= th]) thumbnail,
          maybe [] (\ib -> ["isBuiltIn" .= ib]) isBuiltIn,
          maybe [] (\v -> ["version" .= v]) version
        ]

instance FromJSON PresetMetadata where
  parseJSON = withObject "PresetMetadata" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    category <- o .: "category"
    description <- o .:? "description"
    tags <- o .:? "tags"
    author <- o .:? "author"
    createdAt <- o .: "createdAt"
    updatedAt <- o .: "updatedAt"
    thumbnail <- o .:? "thumbnail"
    isBuiltIn <- o .:? "isBuiltIn"
    version <- o .:? "version"
    return (PresetMetadata id_ name category description tags author createdAt updatedAt thumbnail isBuiltIn version)

-- ============================================================================
-- PARTICLE PRESET
-- ============================================================================

-- | Combined particle preset config (system + emitter settings)
data ParticlePresetConfig = ParticlePresetConfig
  { particlePresetConfigMaxParticles :: Maybe Double, -- System-level settings
    particlePresetConfigGravity :: Maybe Double,
    particlePresetConfigTurbulenceStrength :: Maybe Double,
    particlePresetConfigEmissionRate :: Maybe Double, -- Emitter-level settings
    particlePresetConfigLifespan :: Maybe Double,
    particlePresetConfigStartSize :: Maybe Double,
    particlePresetConfigEndSize :: Maybe Double,
    particlePresetConfigStartColor :: Maybe Text, -- Hex color string
    particlePresetConfigEndColor :: Maybe Text, -- Hex color string
    particlePresetConfigVelocitySpread :: Maybe Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticlePresetConfig where
  toJSON (ParticlePresetConfig maxParticles gravity turbulenceStrength emissionRate lifespan startSize endSize startColor endColor velocitySpread) =
    object $
      concat
        [ maybe [] (\mp -> ["maxParticles" .= mp]) maxParticles,
          maybe [] (\g -> ["gravity" .= g]) gravity,
          maybe [] (\ts -> ["turbulenceStrength" .= ts]) turbulenceStrength,
          maybe [] (\er -> ["emissionRate" .= er]) emissionRate,
          maybe [] (\l -> ["lifespan" .= l]) lifespan,
          maybe [] (\ss -> ["startSize" .= ss]) startSize,
          maybe [] (\es -> ["endSize" .= es]) endSize,
          maybe [] (\sc -> ["startColor" .= sc]) startColor,
          maybe [] (\ec -> ["endColor" .= ec]) endColor,
          maybe [] (\vs -> ["velocitySpread" .= vs]) velocitySpread
        ]

instance FromJSON ParticlePresetConfig where
  parseJSON = withObject "ParticlePresetConfig" $ \o -> do
    maxParticles <- o .:? "maxParticles"
    gravity <- o .:? "gravity"
    turbulenceStrength <- o .:? "turbulenceStrength"
    emissionRate <- o .:? "emissionRate"
    lifespan <- o .:? "lifespan"
    startSize <- o .:? "startSize"
    endSize <- o .:? "endSize"
    startColor <- o .:? "startColor"
    endColor <- o .:? "endColor"
    velocitySpread <- o .:? "velocitySpread"
    return (ParticlePresetConfig maxParticles gravity turbulenceStrength emissionRate lifespan startSize endSize startColor endColor velocitySpread)

-- | Particle preset
data ParticlePreset = ParticlePreset
  { particlePresetMetadata :: PresetMetadata,
    particlePresetConfig :: ParticlePresetConfig
  }
  deriving (Eq, Show, Generic)

instance ToJSON ParticlePreset where
  toJSON (ParticlePreset metadata config) =
    object $
      concat
        [ [ "id" .= presetMetadataId metadata,
            "name" .= presetMetadataName metadata,
            "category" .= ("particle" :: Text),
            "createdAt" .= presetMetadataCreatedAt metadata,
            "updatedAt" .= presetMetadataUpdatedAt metadata,
            "config" .= config
          ],
          maybe [] (\d -> ["description" .= d]) (presetMetadataDescription metadata),
          maybe [] (\t -> ["tags" .= t]) (presetMetadataTags metadata),
          maybe [] (\a -> ["author" .= a]) (presetMetadataAuthor metadata),
          maybe [] (\th -> ["thumbnail" .= th]) (presetMetadataThumbnail metadata),
          maybe [] (\ib -> ["isBuiltIn" .= ib]) (presetMetadataIsBuiltIn metadata),
          maybe [] (\v -> ["version" .= v]) (presetMetadataVersion metadata)
        ]

instance FromJSON ParticlePreset where
  parseJSON = withObject "ParticlePreset" $ \o -> do
    metadata <- parseJSON (Object o)
    config <- o .: "config"
    return (ParticlePreset metadata config)

-- ============================================================================
-- EFFECT PRESET
-- ============================================================================

-- | Effect preset item (single effect in preset)
data EffectPresetItem = EffectPresetItem
  { effectPresetItemType :: Text,
    effectPresetItemParams :: [(Text, PropertyValue)] -- Record<string, PropertyValue>
  }
  deriving (Eq, Show, Generic)

instance ToJSON EffectPresetItem where
  toJSON (EffectPresetItem type_ params) =
    object
      [ "type" .= type_,
        "params" .= object (map (\(k, v) -> fromText k .= v) params)
      ]

instance FromJSON EffectPresetItem where
  parseJSON = withObject "EffectPresetItem" $ \o -> do
    type_ <- o .: "type"
    paramsObj <- o .: "params"
    params <- withObject "params" (\paramsO -> do
      let pairs = toList paramsO
      mapM (\(k, v) -> do
        pv <- parseJSON v :: Parser PropertyValue
        return (toText k, pv)) pairs) paramsObj
    return (EffectPresetItem type_ params)

-- | Effect preset
data EffectPreset = EffectPreset
  { effectPresetMetadata :: PresetMetadata,
    effectPresetEffects :: [EffectPresetItem]
  }
  deriving (Eq, Show, Generic)

instance ToJSON EffectPreset where
  toJSON (EffectPreset metadata effects) =
    object $
      concat
        [ [ "id" .= presetMetadataId metadata,
            "name" .= presetMetadataName metadata,
            "category" .= ("effect" :: Text),
            "createdAt" .= presetMetadataCreatedAt metadata,
            "updatedAt" .= presetMetadataUpdatedAt metadata,
            "effects" .= effects
          ],
          maybe [] (\d -> ["description" .= d]) (presetMetadataDescription metadata),
          maybe [] (\t -> ["tags" .= t]) (presetMetadataTags metadata),
          maybe [] (\a -> ["author" .= a]) (presetMetadataAuthor metadata),
          maybe [] (\th -> ["thumbnail" .= th]) (presetMetadataThumbnail metadata),
          maybe [] (\ib -> ["isBuiltIn" .= ib]) (presetMetadataIsBuiltIn metadata),
          maybe [] (\v -> ["version" .= v]) (presetMetadataVersion metadata)
        ]

instance FromJSON EffectPreset where
  parseJSON = withObject "EffectPreset" $ \o -> do
    metadata <- parseJSON (Object o)
    effectsRaw <- o .: "effects"
    -- Validate max 100 effects per preset
    effects <- case validateBoundedArray 100 effectsRaw of
      Left err -> fail (T.unpack err)
      Right es -> return es
    return (EffectPreset metadata effects)

-- ============================================================================
-- PATH EFFECT PRESET
-- ============================================================================

-- | Path effect preset
-- NOTE: Uses Text placeholder for SplinePathEffectInstance - will be updated when spline types are migrated
data PathEffectPreset = PathEffectPreset
  { pathEffectPresetMetadata :: PresetMetadata,
    pathEffectPresetEffects :: [Text] -- TODO: Use SplinePathEffectInstance when spline.ts is migrated
  }
  deriving (Eq, Show, Generic)

instance ToJSON PathEffectPreset where
  toJSON (PathEffectPreset metadata effects) =
    object $
      concat
        [ [ "id" .= presetMetadataId metadata,
            "name" .= presetMetadataName metadata,
            "category" .= ("path-effect" :: Text),
            "createdAt" .= presetMetadataCreatedAt metadata,
            "updatedAt" .= presetMetadataUpdatedAt metadata,
            "effects" .= effects
          ],
          maybe [] (\d -> ["description" .= d]) (presetMetadataDescription metadata),
          maybe [] (\t -> ["tags" .= t]) (presetMetadataTags metadata),
          maybe [] (\a -> ["author" .= a]) (presetMetadataAuthor metadata),
          maybe [] (\th -> ["thumbnail" .= th]) (presetMetadataThumbnail metadata),
          maybe [] (\ib -> ["isBuiltIn" .= ib]) (presetMetadataIsBuiltIn metadata),
          maybe [] (\v -> ["version" .= v]) (presetMetadataVersion metadata)
        ]

instance FromJSON PathEffectPreset where
  parseJSON = withObject "PathEffectPreset" $ \o -> do
    metadata <- parseJSON (Object o)
    effectsRaw <- o .: "effects"
    -- Validate max 100 path effects per preset
    effects <- case validateBoundedArray 100 effectsRaw of
      Left err -> fail (T.unpack err)
      Right es -> return es
    return (PathEffectPreset metadata effects)

-- ============================================================================
-- CAMERA SHAKE PRESET
-- ============================================================================

-- | Camera shake preset
-- NOTE: Uses Text placeholder for CameraShakeConfig - will be updated when cameraEnhancements service is migrated
data CameraShakePreset = CameraShakePreset
  { cameraShakePresetMetadata :: PresetMetadata,
    cameraShakePresetConfig :: Text -- TODO: Use Partial CameraShakeConfig when cameraEnhancements.ts is migrated
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraShakePreset where
  toJSON (CameraShakePreset metadata config) =
    object $
      concat
        [ [ "id" .= presetMetadataId metadata,
            "name" .= presetMetadataName metadata,
            "category" .= ("camera-shake" :: Text),
            "createdAt" .= presetMetadataCreatedAt metadata,
            "updatedAt" .= presetMetadataUpdatedAt metadata,
            "config" .= config
          ],
          maybe [] (\d -> ["description" .= d]) (presetMetadataDescription metadata),
          maybe [] (\t -> ["tags" .= t]) (presetMetadataTags metadata),
          maybe [] (\a -> ["author" .= a]) (presetMetadataAuthor metadata),
          maybe [] (\th -> ["thumbnail" .= th]) (presetMetadataThumbnail metadata),
          maybe [] (\ib -> ["isBuiltIn" .= ib]) (presetMetadataIsBuiltIn metadata),
          maybe [] (\v -> ["version" .= v]) (presetMetadataVersion metadata)
        ]

instance FromJSON CameraShakePreset where
  parseJSON = withObject "CameraShakePreset" $ \o -> do
    metadata <- parseJSON (Object o)
    config <- o .: "config"
    return (CameraShakePreset metadata config)

-- ============================================================================
-- CAMERA TRAJECTORY PRESET
-- ============================================================================

-- | Camera trajectory preset
-- NOTE: Uses Text placeholder for TrajectoryConfig - will be updated when cameraTrajectory service is migrated
data CameraTrajectoryPreset = CameraTrajectoryPreset
  { cameraTrajectoryPresetMetadata :: PresetMetadata,
    cameraTrajectoryPresetConfig :: Text -- TODO: Use Partial TrajectoryConfig when cameraTrajectory.ts is migrated
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraTrajectoryPreset where
  toJSON (CameraTrajectoryPreset metadata config) =
    object $
      concat
        [ [ "id" .= presetMetadataId metadata,
            "name" .= presetMetadataName metadata,
            "category" .= ("camera-trajectory" :: Text),
            "createdAt" .= presetMetadataCreatedAt metadata,
            "updatedAt" .= presetMetadataUpdatedAt metadata,
            "config" .= config
          ],
          maybe [] (\d -> ["description" .= d]) (presetMetadataDescription metadata),
          maybe [] (\t -> ["tags" .= t]) (presetMetadataTags metadata),
          maybe [] (\a -> ["author" .= a]) (presetMetadataAuthor metadata),
          maybe [] (\th -> ["thumbnail" .= th]) (presetMetadataThumbnail metadata),
          maybe [] (\ib -> ["isBuiltIn" .= ib]) (presetMetadataIsBuiltIn metadata),
          maybe [] (\v -> ["version" .= v]) (presetMetadataVersion metadata)
        ]

instance FromJSON CameraTrajectoryPreset where
  parseJSON = withObject "CameraTrajectoryPreset" $ \o -> do
    metadata <- parseJSON (Object o)
    config <- o .: "config"
    return (CameraTrajectoryPreset metadata config)

-- ============================================================================
-- TEXT STYLE PRESET
-- ============================================================================

-- | Text align
data TextAlign
  = TextAlignLeft
  | TextAlignCenter
  | TextAlignRight
  deriving (Eq, Show, Generic)

instance ToJSON TextAlign where
  toJSON TextAlignLeft = "left"
  toJSON TextAlignCenter = "center"
  toJSON TextAlignRight = "right"

instance FromJSON TextAlign where
  parseJSON = withText "TextAlign" $ \s ->
    case s of
      t | t == T.pack "left" -> return TextAlignLeft
      t | t == T.pack "center" -> return TextAlignCenter
      t | t == T.pack "right" -> return TextAlignRight
      _ -> fail "Invalid TextAlign"

-- | Text style config
data TextStyleConfig = TextStyleConfig
  { textStyleConfigFontFamily :: Maybe Text,
    textStyleConfigFontSize :: Maybe Double,
    textStyleConfigFontWeight :: Maybe Double,
    textStyleConfigFill :: Maybe Text, -- Hex color string
    textStyleConfigStroke :: Maybe Text, -- Hex color string
    textStyleConfigStrokeWidth :: Maybe Double,
    textStyleConfigLetterSpacing :: Maybe Double,
    textStyleConfigLineHeight :: Maybe Double,
    textStyleConfigTextAlign :: Maybe TextAlign
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextStyleConfig where
  toJSON (TextStyleConfig fontFamily fontSize fontWeight fill stroke strokeWidth letterSpacing lineHeight textAlign) =
    object $
      concat
        [ maybe [] (\ff -> ["fontFamily" .= ff]) fontFamily,
          maybe [] (\fs -> ["fontSize" .= fs]) fontSize,
          maybe [] (\fw -> ["fontWeight" .= fw]) fontWeight,
          maybe [] (\f -> ["fill" .= f]) fill,
          maybe [] (\s -> ["stroke" .= s]) stroke,
          maybe [] (\sw -> ["strokeWidth" .= sw]) strokeWidth,
          maybe [] (\ls -> ["letterSpacing" .= ls]) letterSpacing,
          maybe [] (\lh -> ["lineHeight" .= lh]) lineHeight,
          maybe [] (\ta -> ["textAlign" .= ta]) textAlign
        ]

instance FromJSON TextStyleConfig where
  parseJSON = withObject "TextStyleConfig" $ \o -> do
    fontFamily <- o .:? "fontFamily"
    fontSize <- o .:? "fontSize"
    fontWeight <- o .:? "fontWeight"
    fill <- o .:? "fill"
    stroke <- o .:? "stroke"
    strokeWidth <- o .:? "strokeWidth"
    letterSpacing <- o .:? "letterSpacing"
    lineHeight <- o .:? "lineHeight"
    textAlign <- o .:? "textAlign"
    return (TextStyleConfig fontFamily fontSize fontWeight fill stroke strokeWidth letterSpacing lineHeight textAlign)

-- | Text style preset
data TextStylePreset = TextStylePreset
  { textStylePresetMetadata :: PresetMetadata,
    textStylePresetStyle :: TextStyleConfig
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextStylePreset where
  toJSON (TextStylePreset metadata style) =
    object $
      concat
        [ [ "id" .= presetMetadataId metadata,
            "name" .= presetMetadataName metadata,
            "category" .= ("text-style" :: Text),
            "createdAt" .= presetMetadataCreatedAt metadata,
            "updatedAt" .= presetMetadataUpdatedAt metadata,
            "style" .= style
          ],
          maybe [] (\d -> ["description" .= d]) (presetMetadataDescription metadata),
          maybe [] (\t -> ["tags" .= t]) (presetMetadataTags metadata),
          maybe [] (\a -> ["author" .= a]) (presetMetadataAuthor metadata),
          maybe [] (\th -> ["thumbnail" .= th]) (presetMetadataThumbnail metadata),
          maybe [] (\ib -> ["isBuiltIn" .= ib]) (presetMetadataIsBuiltIn metadata),
          maybe [] (\v -> ["version" .= v]) (presetMetadataVersion metadata)
        ]

instance FromJSON TextStylePreset where
  parseJSON = withObject "TextStylePreset" $ \o -> do
    metadata <- parseJSON (Object o)
    style <- o .: "style"
    return (TextStylePreset metadata style)

-- ============================================================================
-- COLOR PALETTE PRESET
-- ============================================================================

-- | Color palette preset
data ColorPalettePreset = ColorPalettePreset
  { colorPalettePresetMetadata :: PresetMetadata,
    colorPalettePresetColors :: [Text] -- Array of hex color strings
  }
  deriving (Eq, Show, Generic)

instance ToJSON ColorPalettePreset where
  toJSON (ColorPalettePreset metadata colors) =
    object $
      concat
        [ [ "id" .= presetMetadataId metadata,
            "name" .= presetMetadataName metadata,
            "category" .= ("color-palette" :: Text),
            "createdAt" .= presetMetadataCreatedAt metadata,
            "updatedAt" .= presetMetadataUpdatedAt metadata,
            "colors" .= colors
          ],
          maybe [] (\d -> ["description" .= d]) (presetMetadataDescription metadata),
          maybe [] (\t -> ["tags" .= t]) (presetMetadataTags metadata),
          maybe [] (\a -> ["author" .= a]) (presetMetadataAuthor metadata),
          maybe [] (\th -> ["thumbnail" .= th]) (presetMetadataThumbnail metadata),
          maybe [] (\ib -> ["isBuiltIn" .= ib]) (presetMetadataIsBuiltIn metadata),
          maybe [] (\v -> ["version" .= v]) (presetMetadataVersion metadata)
        ]

instance FromJSON ColorPalettePreset where
  parseJSON = withObject "ColorPalettePreset" $ \o -> do
    metadata <- parseJSON (Object o)
    colorsRaw <- o .: "colors"
    -- Validate max 1000 colors per palette
    colors <- case validateBoundedArray 1000 colorsRaw of
      Left err -> fail (T.unpack err)
      Right cs -> return cs
    return (ColorPalettePreset metadata colors)

-- ============================================================================
-- ANIMATION PRESET
-- ============================================================================

-- | Animation preset keyframe
data AnimationPresetKeyframe = AnimationPresetKeyframe
  { animationPresetKeyframeFrame :: Double, -- Frame number
    animationPresetKeyframeValue :: PropertyValue,
    animationPresetKeyframeEasing :: Maybe Text -- Easing function name
  }
  deriving (Eq, Show, Generic)

instance ToJSON AnimationPresetKeyframe where
  toJSON (AnimationPresetKeyframe frame value easing) =
    object $
      concat
        [ [ "frame" .= frame,
            "value" .= value
          ],
          maybe [] (\e -> ["easing" .= e]) easing
        ]

instance FromJSON AnimationPresetKeyframe where
  parseJSON = withObject "AnimationPresetKeyframe" $ \o -> do
    frame <- o .: "frame"
    value <- o .: "value"
    easing <- o .:? "easing"
    return (AnimationPresetKeyframe frame value easing)

-- | Animation preset property (keyframes for a single property)
data AnimationPresetProperty = AnimationPresetProperty
  { animationPresetPropertyProperty :: Text, -- Property name
    animationPresetPropertyKeyframes :: [AnimationPresetKeyframe]
  }
  deriving (Eq, Show, Generic)

instance ToJSON AnimationPresetProperty where
  toJSON (AnimationPresetProperty property keyframes) =
    object
      [ "property" .= property,
        "keyframes" .= keyframes
      ]

instance FromJSON AnimationPresetProperty where
  parseJSON = withObject "AnimationPresetProperty" $ \o -> do
    property <- o .: "property"
    keyframesRaw <- o .: "keyframes"
    -- Validate max 10,000 keyframes per property
    keyframes <- case validateBoundedArray 10000 keyframesRaw of
      Left err -> fail (T.unpack err)
      Right kfs -> return kfs
    return (AnimationPresetProperty property keyframes)

-- | Animation preset
data AnimationPreset = AnimationPreset
  { animationPresetMetadata :: PresetMetadata,
    animationPresetKeyframes :: [AnimationPresetProperty],
    animationPresetDuration :: Double -- Duration in frames or seconds
  }
  deriving (Eq, Show, Generic)

instance ToJSON AnimationPreset where
  toJSON (AnimationPreset metadata keyframes duration) =
    object $
      concat
        [ [ "id" .= presetMetadataId metadata,
            "name" .= presetMetadataName metadata,
            "category" .= ("animation" :: Text),
            "createdAt" .= presetMetadataCreatedAt metadata,
            "updatedAt" .= presetMetadataUpdatedAt metadata,
            "keyframes" .= keyframes,
            "duration" .= duration
          ],
          maybe [] (\d -> ["description" .= d]) (presetMetadataDescription metadata),
          maybe [] (\t -> ["tags" .= t]) (presetMetadataTags metadata),
          maybe [] (\a -> ["author" .= a]) (presetMetadataAuthor metadata),
          maybe [] (\th -> ["thumbnail" .= th]) (presetMetadataThumbnail metadata),
          maybe [] (\ib -> ["isBuiltIn" .= ib]) (presetMetadataIsBuiltIn metadata),
          maybe [] (\v -> ["version" .= v]) (presetMetadataVersion metadata)
        ]

instance FromJSON AnimationPreset where
  parseJSON = withObject "AnimationPreset" $ \o -> do
    metadata <- parseJSON (Object o)
    keyframesRaw <- o .: "keyframes"
    duration <- o .: "duration"
    -- Validate max 100 properties per animation preset
    keyframes <- case validateBoundedArray 100 keyframesRaw of
      Left err -> fail (T.unpack err)
      Right kfs -> return kfs
    return (AnimationPreset metadata keyframes duration)

-- ============================================================================
-- PRESET UNION TYPE
-- ============================================================================

-- | Preset union type (all preset types)
data Preset
  = PresetParticle ParticlePreset
  | PresetEffect EffectPreset
  | PresetPathEffect PathEffectPreset
  | PresetCameraShake CameraShakePreset
  | PresetCameraTrajectory CameraTrajectoryPreset
  | PresetTextStyle TextStylePreset
  | PresetColorPalette ColorPalettePreset
  | PresetAnimation AnimationPreset
  deriving (Eq, Show, Generic)

instance ToJSON Preset where
  toJSON (PresetParticle p) = toJSON p
  toJSON (PresetEffect p) = toJSON p
  toJSON (PresetPathEffect p) = toJSON p
  toJSON (PresetCameraShake p) = toJSON p
  toJSON (PresetCameraTrajectory p) = toJSON p
  toJSON (PresetTextStyle p) = toJSON p
  toJSON (PresetColorPalette p) = toJSON p
  toJSON (PresetAnimation p) = toJSON p

instance FromJSON Preset where
  parseJSON = withObject "Preset" $ \o -> do
    category <- (o .: fromText (T.pack "category")) :: Parser Text
    case () of
      _ | category == T.pack "particle" -> PresetParticle <$> parseJSON (Object o)
      _ | category == T.pack "effect" -> PresetEffect <$> parseJSON (Object o)
      _ | category == T.pack "path-effect" -> PresetPathEffect <$> parseJSON (Object o)
      _ | category == T.pack "camera-shake" -> PresetCameraShake <$> parseJSON (Object o)
      _ | category == T.pack "camera-trajectory" -> PresetCameraTrajectory <$> parseJSON (Object o)
      _ | category == T.pack "text-style" -> PresetTextStyle <$> parseJSON (Object o)
      _ | category == T.pack "color-palette" -> PresetColorPalette <$> parseJSON (Object o)
      _ | category == T.pack "animation" -> PresetAnimation <$> parseJSON (Object o)
      _ -> fail ("Invalid Preset category: " ++ T.unpack category)

-- ============================================================================
-- PRESET COLLECTION
-- ============================================================================

-- | Preset collection (for export/import)
data PresetCollection = PresetCollection
  { presetCollectionVersion :: Double,
    presetCollectionPresets :: [Preset],
    presetCollectionExportedAt :: Double -- Unix timestamp (milliseconds)
  }
  deriving (Eq, Show, Generic)

instance ToJSON PresetCollection where
  toJSON (PresetCollection version presets exportedAt) =
    object
      [ "version" .= version,
        "presets" .= presets,
        "exportedAt" .= exportedAt
      ]

instance FromJSON PresetCollection where
  parseJSON = withObject "PresetCollection" $ \o -> do
    version <- o .: "version"
    presetsRaw <- o .: "presets"
    exportedAt <- o .: "exportedAt"
    -- Validate max 10,000 presets per collection
    presets <- case validateBoundedArray 10000 presetsRaw of
      Left err -> fail (T.unpack err)
      Right ps -> return ps
    return (PresetCollection version presets exportedAt)
