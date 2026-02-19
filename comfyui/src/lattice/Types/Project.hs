-- |
-- Module      : Lattice.Types.Project
-- Description : Lattice project root type and composition types
-- 
-- Migrated from ui/src/types/project.ts
-- Core project structure - layer types migrated separately
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Project
  ( -- Project root
    LatticeProject(..)
  , ProjectMeta(..)
  -- Composition types
  , Composition(..)
  , CompositionSettings(..)
  , Marker(..)
  , ColorSettings(..)
  -- Re-export Layer
  , Layer(..)
  -- Asset types
  , AssetReference(..)
  , DataAssetReference(..)
  , AssetType(..)
  , TextureMapType(..)
  -- Workflow types
  , WorkflowInput(..)
  , WorkflowOutput(..)
  -- Re-exports
  , ColorSpace(..)
  , ViewTransform(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  , Value(..)
  )
import Data.Aeson.Types (Parser)
import Data.HashMap.Strict (HashMap)
import Data.Text (Text)
import GHC.Generics (Generic)
import Lattice.Types.Core (ColorSpace(..), ViewTransform(..))
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives (validateFinite, validateNonNegative)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // project // meta
-- ════════════════════════════════════════════════════════════════════════════

-- | Project metadata
data ProjectMeta = ProjectMeta
  { projectMetaName :: Text
  , projectMetaCreated :: Text  -- ISO 8601 date
  , projectMetaModified :: Text  -- ISO 8601 date
  , projectMetaAuthor :: Maybe Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON ProjectMeta where
  toJSON (ProjectMeta name created modified mAuthor) =
    let
      baseFields = ["name" .= name, "created" .= created, "modified" .= modified]
      withAuthor = case mAuthor of
        Just a -> ("author" .= a) : baseFields
        Nothing -> baseFields
    in object withAuthor

instance FromJSON ProjectMeta where
  parseJSON = withObject "ProjectMeta" $ \o -> do
    name <- o .: "name"
    created <- o .: "created"
    modified <- o .: "modified"
    mAuthor <- o .:? "author"
    return (ProjectMeta name created modified mAuthor)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // marker
-- ════════════════════════════════════════════════════════════════════════════

-- | Timeline marker for navigation, beat sync, and annotation
data Marker = Marker
  { markerId :: Text
  , markerFrame :: Double
  , markerLabel :: Text
  , markerColor :: Text  -- Hex color
  , markerDuration :: Maybe Double  -- Optional marker duration (for range markers)
  , markerComment :: Maybe Text  -- Optional comment/note
  }
  deriving (Eq, Show, Generic)

instance ToJSON Marker where
  toJSON (Marker id_ frame label color mDuration mComment) =
    let
      baseFields = ["id" .= id_, "frame" .= frame, "label" .= label, "color" .= color]
      withDuration = case mDuration of Just d -> ("duration" .= d) : baseFields; Nothing -> baseFields
      withComment = case mComment of Just c -> ("comment" .= c) : withDuration; Nothing -> withDuration
    in object withComment

instance FromJSON Marker where
  parseJSON = withObject "Marker" $ \o -> do
    id_ <- o .: "id"
    frame <- o .: "frame"
    label <- o .: "label"
    color <- o .: "color"
    mDuration <- o .:? "duration"
    mComment <- o .:? "comment"
    -- Validate frame is finite
    if validateFinite frame && maybe True validateFinite mDuration
      then return (Marker id_ frame label color mDuration mComment)
      else fail "Marker frame and duration must be finite numbers"

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // color // settings
-- ════════════════════════════════════════════════════════════════════════════

-- | Color management settings
data ColorSettings = ColorSettings
  { colorSettingsWorkingColorSpace :: ColorSpace  -- Working color space for compositing
  , colorSettingsViewTransform :: ViewTransform  -- View transform for preview
  , colorSettingsExportColorSpace :: Either ColorSpace Text  -- Export color space ("source" or ColorSpace)
  , colorSettingsLinearCompositing :: Bool  -- Enable linear RGB compositing
  }
  deriving (Eq, Show, Generic)

instance ToJSON ColorSettings where
  toJSON (ColorSettings working view export_ linear) =
    object
      [ "workingColorSpace" .= working
      , "viewTransform" .= view
      , "exportColorSpace" .= (either toJSON toJSON export_)
      , "linearCompositing" .= linear
      ]

instance FromJSON ColorSettings where
  parseJSON = withObject "ColorSettings" $ \o -> do
    working <- o .: "workingColorSpace"
    view <- o .: "viewTransform"
    exportVal <- o .: "exportColorSpace"
    linear <- o .: "linearCompositing"
    -- Parse exportColorSpace: either "source" string or ColorSpace
    export_ <- case exportVal of
      String "source" -> return (Right "source")
      _ -> Left <$> parseJSON exportVal
    return (ColorSettings working view export_ linear)

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // composition // settings
-- ════════════════════════════════════════════════════════════════════════════

-- | Composition settings (timeline, resolution, etc.)
data CompositionSettings = CompositionSettings
  { compositionSettingsWidth :: Double  -- Must be divisible by 8
  , compositionSettingsHeight :: Double  -- Must be divisible by 8
  , compositionSettingsFrameCount :: Double  -- 81 default, auto-adjusted for video
  , compositionSettingsFps :: Double  -- 16 for Phase 1
  , compositionSettingsDuration :: Double  -- Calculated: frameCount / fps
  , compositionSettingsBackgroundColor :: Text  -- Hex color
  , compositionSettingsAutoResizeToContent :: Bool  -- Resize when video imported
  , compositionSettingsFrameBlendingEnabled :: Bool  -- Frame blending for time-remapped layers
  , compositionSettingsColorSettings :: Maybe ColorSettings  -- Color management (Phase 6)
  , compositionSettingsMotionBlur :: Maybe Bool  -- Enable motion blur globally
  , compositionSettingsShutterAngle :: Maybe Double  -- Shutter angle in degrees (0-720, 180 = standard film)
  , compositionSettingsMotionBlurSamples :: Maybe Double  -- Samples per frame (2-64)
  }
  deriving (Eq, Show, Generic)

instance ToJSON CompositionSettings where
  toJSON (CompositionSettings w h fc fps dur bg autoResize frameBlend mColor mBlur mShutter mSamples) =
    let
      baseFields = ["width" .= w, "height" .= h, "frameCount" .= fc, "fps" .= fps, "duration" .= dur, "backgroundColor" .= bg, "autoResizeToContent" .= autoResize, "frameBlendingEnabled" .= frameBlend]
      withColor = case mColor of Just c -> ("colorSettings" .= c) : baseFields; Nothing -> baseFields
      withBlur = case mBlur of Just b -> ("motionBlur" .= b) : withColor; Nothing -> withColor
      withShutter = case mShutter of Just s -> ("shutterAngle" .= s) : withBlur; Nothing -> withBlur
      withSamples = case mSamples of Just s -> ("motionBlurSamples" .= s) : withShutter; Nothing -> withShutter
    in object withSamples

instance FromJSON CompositionSettings where
  parseJSON = withObject "CompositionSettings" $ \o -> do
    w <- o .: "width"
    h <- o .: "height"
    fc <- o .: "frameCount"
    fps <- o .: "fps"
    dur <- o .: "duration"
    bg <- o .: "backgroundColor"
    autoResize <- o .: "autoResizeToContent"
    frameBlend <- o .: "frameBlendingEnabled"
    mColor <- o .:? "colorSettings"
    mBlur <- o .:? "motionBlur"
    mShutter <- o .:? "shutterAngle"
    mSamples <- o .:? "motionBlurSamples"
    -- Validate dimensions are divisible by 8
    if (round w :: Int) `mod` 8 /= 0 || (round h :: Int) `mod` 8 /= 0
      then fail "CompositionSettings: width and height must be divisible by 8"
      else return ()
    -- Validate finite numbers
    if validateFinite w && validateFinite h && validateFinite fc &&
       validateFinite fps && validateFinite dur &&
       validateNonNegative fc && validateNonNegative fps &&
       maybe True validateFinite mShutter && maybe True validateFinite mSamples
      then return (CompositionSettings w h fc fps dur bg autoResize frameBlend mColor mBlur mShutter mSamples)
      else fail "CompositionSettings: all numeric values must be finite and non-negative where applicable"

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // workflow // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Workflow input mapping
data WorkflowInput = WorkflowInput
  { workflowInputName :: Text
  , workflowInputType :: WorkflowInputType
  , workflowInputNodeId :: Text
  , workflowInputInputName :: Text
  }
  deriving (Eq, Show, Generic)

data WorkflowInputType
  = WorkflowInputImage
  | WorkflowInputVideo
  | WorkflowInputLatent
  | WorkflowInputMask
  | WorkflowInputNumber
  | WorkflowInputString
  deriving (Eq, Show, Generic)

instance ToJSON WorkflowInputType where
  toJSON WorkflowInputImage = "image"
  toJSON WorkflowInputVideo = "video"
  toJSON WorkflowInputLatent = "latent"
  toJSON WorkflowInputMask = "mask"
  toJSON WorkflowInputNumber = "number"
  toJSON WorkflowInputString = "string"

instance FromJSON WorkflowInputType where
  parseJSON (String "image") = return WorkflowInputImage
  parseJSON (String "video") = return WorkflowInputVideo
  parseJSON (String "latent") = return WorkflowInputLatent
  parseJSON (String "mask") = return WorkflowInputMask
  parseJSON (String "number") = return WorkflowInputNumber
  parseJSON (String "string") = return WorkflowInputString
  parseJSON _ = fail "Invalid WorkflowInputType"

instance ToJSON WorkflowInput where
  toJSON (WorkflowInput name typ nodeId inputName) =
    object
      [ "name" .= name
      , "type" .= typ
      , "nodeId" .= nodeId
      , "inputName" .= inputName
      ]

instance FromJSON WorkflowInput where
  parseJSON = withObject "WorkflowInput" $ \o -> do
    name <- o .: "name"
    typ <- o .: "type"
    nodeId <- o .: "nodeId"
    inputName <- o .: "inputName"
    return (WorkflowInput name typ nodeId inputName)

-- | Workflow output mapping
data WorkflowOutput = WorkflowOutput
  { workflowOutputName :: Text
  , workflowOutputType :: WorkflowOutputType
  , workflowOutputNodeId :: Text
  , workflowOutputOutputName :: Text
  }
  deriving (Eq, Show, Generic)

data WorkflowOutputType
  = WorkflowOutputImage
  | WorkflowOutputVideo
  | WorkflowOutputLatent
  deriving (Eq, Show, Generic)

instance ToJSON WorkflowOutputType where
  toJSON WorkflowOutputImage = "image"
  toJSON WorkflowOutputVideo = "video"
  toJSON WorkflowOutputLatent = "latent"

instance FromJSON WorkflowOutputType where
  parseJSON (String "image") = return WorkflowOutputImage
  parseJSON (String "video") = return WorkflowOutputVideo
  parseJSON (String "latent") = return WorkflowOutputLatent
  parseJSON _ = fail "Invalid WorkflowOutputType"

instance ToJSON WorkflowOutput where
  toJSON (WorkflowOutput name typ nodeId outputName) =
    object
      [ "name" .= name
      , "type" .= typ
      , "nodeId" .= nodeId
      , "outputName" .= outputName
      ]

instance FromJSON WorkflowOutput where
  parseJSON = withObject "WorkflowOutput" $ \o -> do
    name <- o .: "name"
    typ <- o .: "type"
    nodeId <- o .: "nodeId"
    outputName <- o .: "outputName"
    return (WorkflowOutput name typ nodeId outputName)

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // asset // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Asset types supported by the compositor
data AssetType
  = AssetTypeDepthMap
  | AssetTypeImage
  | AssetTypeVideo
  | AssetTypeAudio
  | AssetTypeModel
  | AssetTypePointCloud
  | AssetTypeTexture
  | AssetTypeMaterial
  | AssetTypeHDRI
  | AssetTypeSVG
  | AssetTypeSprite
  | AssetTypeSpriteSheet
  | AssetTypeLUT
  deriving (Eq, Show, Generic)

instance ToJSON AssetType where
  toJSON AssetTypeDepthMap = "depth_map"
  toJSON AssetTypeImage = "image"
  toJSON AssetTypeVideo = "video"
  toJSON AssetTypeAudio = "audio"
  toJSON AssetTypeModel = "model"
  toJSON AssetTypePointCloud = "pointcloud"
  toJSON AssetTypeTexture = "texture"
  toJSON AssetTypeMaterial = "material"
  toJSON AssetTypeHDRI = "hdri"
  toJSON AssetTypeSVG = "svg"
  toJSON AssetTypeSprite = "sprite"
  toJSON AssetTypeSpriteSheet = "spritesheet"
  toJSON AssetTypeLUT = "lut"

instance FromJSON AssetType where
  parseJSON (String "depth_map") = return AssetTypeDepthMap
  parseJSON (String "image") = return AssetTypeImage
  parseJSON (String "video") = return AssetTypeVideo
  parseJSON (String "audio") = return AssetTypeAudio
  parseJSON (String "model") = return AssetTypeModel
  parseJSON (String "pointcloud") = return AssetTypePointCloud
  parseJSON (String "texture") = return AssetTypeTexture
  parseJSON (String "material") = return AssetTypeMaterial
  parseJSON (String "hdri") = return AssetTypeHDRI
  parseJSON (String "svg") = return AssetTypeSVG
  parseJSON (String "sprite") = return AssetTypeSprite
  parseJSON (String "spritesheet") = return AssetTypeSpriteSheet
  parseJSON (String "lut") = return AssetTypeLUT
  parseJSON _ = fail "Invalid AssetType"

-- | PBR texture map types
data TextureMapType
  = TextureMapAlbedo
  | TextureMapNormal
  | TextureMapRoughness
  | TextureMapMetalness
  | TextureMapAO
  | TextureMapEmissive
  | TextureMapHeight
  | TextureMapOpacity
  | TextureMapSpecular
  deriving (Eq, Show, Generic)

instance ToJSON TextureMapType where
  toJSON TextureMapAlbedo = "albedo"
  toJSON TextureMapNormal = "normal"
  toJSON TextureMapRoughness = "roughness"
  toJSON TextureMapMetalness = "metalness"
  toJSON TextureMapAO = "ao"
  toJSON TextureMapEmissive = "emissive"
  toJSON TextureMapHeight = "height"
  toJSON TextureMapOpacity = "opacity"
  toJSON TextureMapSpecular = "specular"

instance FromJSON TextureMapType where
  parseJSON (String "albedo") = return TextureMapAlbedo
  parseJSON (String "normal") = return TextureMapNormal
  parseJSON (String "roughness") = return TextureMapRoughness
  parseJSON (String "metalness") = return TextureMapMetalness
  parseJSON (String "ao") = return TextureMapAO
  parseJSON (String "emissive") = return TextureMapEmissive
  parseJSON (String "height") = return TextureMapHeight
  parseJSON (String "opacity") = return TextureMapOpacity
  parseJSON (String "specular") = return TextureMapSpecular
  parseJSON _ = fail "Invalid TextureMapType"

-- | Asset reference (simplified - full AssetReference has many optional fields)
-- Full migration will require separate AssetReference module
data AssetReference = AssetReference
  { assetReferenceId :: Text
  , assetReferenceType :: AssetType
  , assetReferenceSource :: AssetSource
  , assetReferenceNodeId :: Maybe Text
  , assetReferenceWidth :: Double
  , assetReferenceHeight :: Double
  , assetReferenceData :: Text  -- Base64 or URL - always required
  , assetReferenceFilename :: Maybe Text
  }
  deriving (Eq, Show, Generic)

data AssetSource
  = AssetSourceComfyUINode
  | AssetSourceFile
  | AssetSourceGenerated
  | AssetSourceURL
  deriving (Eq, Show, Generic)

instance ToJSON AssetSource where
  toJSON AssetSourceComfyUINode = "comfyui_node"
  toJSON AssetSourceFile = "file"
  toJSON AssetSourceGenerated = "generated"
  toJSON AssetSourceURL = "url"

instance FromJSON AssetSource where
  parseJSON (String "comfyui_node") = return AssetSourceComfyUINode
  parseJSON (String "file") = return AssetSourceFile
  parseJSON (String "generated") = return AssetSourceGenerated
  parseJSON (String "url") = return AssetSourceURL
  parseJSON _ = fail "Invalid AssetSource"

instance ToJSON AssetReference where
  toJSON (AssetReference id_ typ source mNodeId w h data_ mFilename) =
    let
      baseFields = ["id" .= id_, "type" .= typ, "source" .= source, "width" .= w, "height" .= h, "data" .= data_]
      withNodeId = case mNodeId of Just n -> ("nodeId" .= n) : baseFields; Nothing -> baseFields
      withFilename = case mFilename of Just f -> ("filename" .= f) : withNodeId; Nothing -> withNodeId
    in object withFilename

instance FromJSON AssetReference where
  parseJSON = withObject "AssetReference" $ \o -> do
    id_ <- o .: "id"
    typ <- o .: "type"
    source <- o .: "source"
    mNodeId <- o .:? "nodeId"
    w <- o .: "width"
    h <- o .: "height"
    data_ <- o .: "data"
    mFilename <- o .:? "filename"
    -- Validate finite dimensions
    if validateFinite w && validateFinite h && validateNonNegative w && validateNonNegative h
      then return (AssetReference id_ typ source mNodeId w h data_ mFilename)
      else fail "AssetReference: width and height must be finite and non-negative"

-- | Data asset reference (JSON, CSV, TSV) for expressions
data DataAssetReference = DataAssetReference
  { dataAssetReferenceId :: Text
  , dataAssetReferenceName :: Text  -- Original filename
  , dataAssetReferenceType :: DataAssetType
  , dataAssetReferenceRawContent :: Text  -- Original file content
  , dataAssetReferenceLastModified :: Double  -- Timestamp
  , dataAssetReferenceSourceData :: Maybe Value  -- Parsed JSON data (for JSON assets)
  , dataAssetReferenceHeaders :: Maybe [Text]  -- For CSV/TSV
  , dataAssetReferenceRows :: Maybe [[Text]]  -- For CSV/TSV
  , dataAssetReferenceNumRows :: Maybe Double
  , dataAssetReferenceNumColumns :: Maybe Double
  }
  deriving (Eq, Show, Generic)

data DataAssetType
  = DataAssetTypeJSON
  | DataAssetTypeCSV
  | DataAssetTypeTSV
  | DataAssetTypeMGJSON
  deriving (Eq, Show, Generic)

instance ToJSON DataAssetType where
  toJSON DataAssetTypeJSON = "json"
  toJSON DataAssetTypeCSV = "csv"
  toJSON DataAssetTypeTSV = "tsv"
  toJSON DataAssetTypeMGJSON = "mgjson"

instance FromJSON DataAssetType where
  parseJSON (String "json") = return DataAssetTypeJSON
  parseJSON (String "csv") = return DataAssetTypeCSV
  parseJSON (String "tsv") = return DataAssetTypeTSV
  parseJSON (String "mgjson") = return DataAssetTypeMGJSON
  parseJSON _ = fail "Invalid DataAssetType"

instance ToJSON DataAssetReference where
  toJSON (DataAssetReference id_ name typ rawContent lastMod mSourceData mHeaders mRows mNumRows mNumCols) =
    let
      baseFields = ["id" .= id_, "name" .= name, "type" .= typ, "rawContent" .= rawContent, "lastModified" .= lastMod]
      f1 = case mSourceData of Just sd -> ("sourceData" .= sd) : baseFields; Nothing -> baseFields
      f2 = case mHeaders of Just h -> ("headers" .= h) : f1; Nothing -> f1
      f3 = case mRows of Just r -> ("rows" .= r) : f2; Nothing -> f2
      f4 = case mNumRows of Just nr -> ("numRows" .= nr) : f3; Nothing -> f3
      f5 = case mNumCols of Just nc -> ("numColumns" .= nc) : f4; Nothing -> f4
    in object f5

instance FromJSON DataAssetReference where
  parseJSON = withObject "DataAssetReference" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    typ <- o .: "type"
    rawContent <- o .: "rawContent"
    lastMod <- o .: "lastModified"
    mSourceData <- o .:? "sourceData"
    mHeaders <- o .:? "headers"
    mRows <- o .:? "rows"
    mNumRows <- o .:? "numRows"
    mNumCols <- o .:? "numColumns"
    -- Validate timestamp is finite
    if validateFinite lastMod && validateNonNegative lastMod
      then return (DataAssetReference id_ name typ rawContent lastMod mSourceData mHeaders mRows mNumRows mNumCols)
      else fail "DataAssetReference: lastModified must be finite and non-negative"

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // composition
-- ════════════════════════════════════════════════════════════════════════════

-- | Composition - independent timeline with its own layers
data Composition = Composition
  { compositionId :: Text
  , compositionName :: Text
  , compositionSettings :: CompositionSettings
  , compositionLayers :: [Layer]  -- Layers in this composition
  , compositionCurrentFrame :: Double
  , compositionIsNestedComp :: Bool
  , compositionParentCompositionId :: Maybe Text
  , compositionWorkflowId :: Maybe Text  -- ComfyUI sub-graph mapping
  , compositionWorkflowInputs :: Maybe [WorkflowInput]
  , compositionWorkflowOutputs :: Maybe [WorkflowOutput]
  , compositionTemplateConfig :: Maybe Value  -- TODO: Replace with TemplateConfig after migration
  , compositionGlobalLight :: Maybe Value  -- TODO: Replace with GlobalLightSettings after migration
  , compositionMarkers :: Maybe [Marker]
  }
  deriving (Eq, Show, Generic)

instance ToJSON Composition where
  toJSON (Composition id_ name settings layers currentFrame isNested mParent mWorkflowId mInputs mOutputs mTemplate mGlobalLight mMarkers) =
    let
      baseFields = ["id" .= id_, "name" .= name, "settings" .= settings, "layers" .= layers, "currentFrame" .= currentFrame, "isNestedComp" .= isNested]
      f1 = case mParent of Just p -> ("parentCompositionId" .= p) : baseFields; Nothing -> baseFields
      f2 = case mWorkflowId of Just w -> ("workflowId" .= w) : f1; Nothing -> f1
      f3 = case mInputs of Just i -> ("workflowInputs" .= i) : f2; Nothing -> f2
      f4 = case mOutputs of Just o -> ("workflowOutputs" .= o) : f3; Nothing -> f3
      f5 = case mTemplate of Just t -> ("templateConfig" .= t) : f4; Nothing -> f4
      f6 = case mGlobalLight of Just g -> ("globalLight" .= g) : f5; Nothing -> f5
      f7 = case mMarkers of Just m -> ("markers" .= m) : f6; Nothing -> f6
    in object f7

instance FromJSON Composition where
  parseJSON = withObject "Composition" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    settings <- o .: "settings"
    layers <- o .: "layers" :: Parser [Layer]
    currentFrame <- o .: "currentFrame"
    isNested <- o .: "isNestedComp"
    mParent <- o .:? "parentCompositionId"
    mWorkflowId <- o .:? "workflowId"
    mInputs <- o .:? "workflowInputs"
    mOutputs <- o .:? "workflowOutputs"
    mTemplate <- o .:? "templateConfig"
    mGlobalLight <- o .:? "globalLight"
    mMarkers <- o .:? "markers"
    -- Validate currentFrame is finite
    if validateFinite currentFrame && validateNonNegative currentFrame
      then return (Composition id_ name settings layers currentFrame isNested mParent mWorkflowId mInputs mOutputs mTemplate mGlobalLight mMarkers)
      else fail "Composition: currentFrame must be finite and non-negative"

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // lattice // project
-- ════════════════════════════════════════════════════════════════════════════

-- | Lattice project root type
data LatticeProject = LatticeProject
  { latticeProjectVersion :: Text  -- "1.0.0"
  , latticeProjectSchemaVersion :: Maybe Double  -- Schema version for migrations (default: 1)
  , latticeProjectMeta :: ProjectMeta
  , latticeProjectCompositions :: HashMap Text Composition  -- Multi-composition support
  , latticeProjectMainCompositionId :: Text  -- Which comp to export
  , latticeProjectComposition :: CompositionSettings  -- Legacy single-comp alias
  , latticeProjectAssets :: HashMap Text AssetReference
  , latticeProjectDataAssets :: Maybe (HashMap Text DataAssetReference)  -- Data assets for expressions
  , latticeProjectLayers :: [Layer]  -- Legacy layers for main composition
  , latticeProjectCurrentFrame :: Double
  , latticeProjectSnapConfig :: Maybe Value  -- TODO: Replace with SnapConfig after migration
  , latticeProjectExportSettings :: Maybe ExportSettings
  }
  deriving (Eq, Show, Generic)

-- | Export settings (user preferences for export)
data ExportSettings = ExportSettings
  { exportSettingsFormat :: Text  -- Export format (e.g., 'mp4', 'png', 'webm')
  , exportSettingsCodec :: Maybe Text  -- Video codec (e.g., 'h264', 'vp9')
  , exportSettingsQuality :: Maybe Text  -- Quality preset (e.g., 'low', 'medium', 'high')
  , exportSettingsResolution :: Maybe Resolution  -- Export resolution
  , exportSettingsFrameRate :: Maybe Double  -- Export frame rate
  }
  deriving (Eq, Show, Generic)

data Resolution = Resolution
  { resolutionWidth :: Double
  , resolutionHeight :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Resolution where
  toJSON (Resolution w h) = object ["width" .= w, "height" .= h]

instance FromJSON Resolution where
  parseJSON = withObject "Resolution" $ \o -> do
    w <- o .: "width"
    h <- o .: "height"
    if validateFinite w && validateFinite h && validateNonNegative w && validateNonNegative h
      then return (Resolution w h)
      else fail "Resolution: width and height must be finite and non-negative"

instance ToJSON ExportSettings where
  toJSON (ExportSettings format mCodec mQuality mRes mFps) =
    let
      baseFields = ["format" .= format]
      f1 = case mCodec of Just c -> ("codec" .= c) : baseFields; Nothing -> baseFields
      f2 = case mQuality of Just q -> ("quality" .= q) : f1; Nothing -> f1
      f3 = case mRes of Just r -> ("resolution" .= r) : f2; Nothing -> f2
      f4 = case mFps of Just f -> ("frameRate" .= f) : f3; Nothing -> f3
    in object f4

instance FromJSON ExportSettings where
  parseJSON = withObject "ExportSettings" $ \o -> do
    format <- o .: "format"
    mCodec <- o .:? "codec"
    mQuality <- o .:? "quality"
    mRes <- o .:? "resolution"
    mFps <- o .:? "frameRate"
    -- Validate frameRate if present
    case mFps of
      Nothing -> return ()
      Just fps -> if validateFinite fps && validateNonNegative fps
        then return ()
        else fail "ExportSettings: frameRate must be finite and non-negative"
    return (ExportSettings format mCodec mQuality mRes mFps)

instance ToJSON LatticeProject where
  toJSON (LatticeProject version mSchemaVersion meta compositions mainCompId comp assets mDataAssets layers currentFrame mSnap mExport) =
    let
      baseFields = ["version" .= version, "meta" .= meta, "compositions" .= compositions, "mainCompositionId" .= mainCompId, "composition" .= comp, "assets" .= assets, "layers" .= layers, "currentFrame" .= currentFrame]
      f1 = case mSchemaVersion of Just s -> ("schemaVersion" .= s) : baseFields; Nothing -> baseFields
      f2 = case mDataAssets of Just d -> ("dataAssets" .= d) : f1; Nothing -> f1
      f3 = case mSnap of Just s -> ("snapConfig" .= s) : f2; Nothing -> f2
      f4 = case mExport of Just e -> ("exportSettings" .= e) : f3; Nothing -> f3
    in object f4

instance FromJSON LatticeProject where
  parseJSON = withObject "LatticeProject" $ \o -> do
    version <- o .: "version"
    mSchemaVersion <- o .:? "schemaVersion"
    meta <- o .: "meta"
    compositions <- o .: "compositions"
    mainCompId <- o .: "mainCompositionId"
    comp <- o .: "composition"
    assets <- o .: "assets"
    mDataAssets <- o .:? "dataAssets"
    layers <- o .: "layers" :: Parser [Layer]
    currentFrame <- o .: "currentFrame"
    mSnap <- o .:? "snapConfig"
    mExport <- o .:? "exportSettings"
    -- Validate currentFrame is finite
    if validateFinite currentFrame && validateNonNegative currentFrame
      then return (LatticeProject version mSchemaVersion meta compositions mainCompId comp assets mDataAssets layers currentFrame mSnap mExport)
      else fail "LatticeProject: currentFrame must be finite and non-negative"
