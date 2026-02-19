-- |
-- Module      : Lattice.Types.Layer
-- Description : Layer type combining all layer data types
-- 
-- Migrated from ui/src/types/project.ts
-- Combines all layer data types into a unified Layer type
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Layer
  ( -- Main type
    Layer(..)
  , LayerType(..)
  , LayerData(..)
  -- Supporting types
  , AutoOrientMode(..)
  , FollowPathConstraint(..)
  , AudioPathAnimation(..)
  , MotionBlurType(..)
  , LayerMotionBlurSettings(..)
  , LayerMaterialOptions(..)
  , CastsShadows(..)
  , LayerQuality(..)
  , StretchAnchor(..)
  , LayerAudio(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , object
  , (.=)
  , (.:)
  , (.:?)
  , Value(..)
  )
import Data.Aeson.Types (Parser)
import Data.Text (Text)
import GHC.Generics (Generic)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , PropertyValue(..)
  )
import Lattice.Types.Primitives
  ( BlendMode(..)
  , validateFinite
  , validateNonNegative
  , validateNormalized01
  )
import Lattice.Schema.SharedValidation
  ( validateBoundedArray
  )
import qualified Data.Text as T
import Lattice.Types.Transform
  ( LayerTransform(..)
  )
-- Import all layer data types
import Lattice.Types.LayerData
  ( MatteType(..)
  , NullLayerData(..)
  , ControlLayerData(..)
  , EffectLayerData(..)
  , SolidLayerData(..)
  , GroupLayerData(..)
  , LightLayerData(..)
  , PoseLayerData(..)
  , GeneratedLayerData(..)
  , MatteLayerData(..)
  , LegacyParticleLayerData(..)
  )
import Lattice.Types.LayerDataAsset
  ( ImageLayerData(..)
  , VideoData(..)
  , AudioLayerData(..)
  , DepthLayerData(..)
  , NormalLayerData(..)
  , NestedCompData(..)
  )
import Lattice.Types.LayerDataComplex
  ( GeneratedMapData(..)
  , ProceduralMatteData(..)
  , DepthflowLayerData(..)
  )
import Lattice.Types.LayerData3D
  ( ModelLayerData(..)
  , PointCloudLayerData(..)
  , CameraLayerData(..)
  )
import Lattice.Types.LayerDataSpline
  ( SplineData(..)
  , PathLayerData(..)
  )
import Lattice.Types.LayerDataText
  ( TextData(..)
  )
import Lattice.Types.LayerDataParticles
  ( ParticleLayerData(..)
  )
import Lattice.Types.LayerDataShapes
  ( ShapeLayerData(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // supporting // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Layer type
data LayerType
  = LayerTypeDepth
  | LayerTypeNormal
  | LayerTypeSpline
  | LayerTypePath
  | LayerTypeText
  | LayerTypeShape
  | LayerTypeParticle  -- Legacy
  | LayerTypeParticles
  | LayerTypeDepthflow
  | LayerTypeImage
  | LayerTypeVideo
  | LayerTypeAudio
  | LayerTypeGenerated
  | LayerTypeCamera
  | LayerTypeLight
  | LayerTypeSolid
  | LayerTypeControl
  | LayerTypeNull  -- @deprecated Use 'control' instead
  | LayerTypeGroup
  | LayerTypeNestedComp
  | LayerTypeMatte
  | LayerTypeModel
  | LayerTypePointcloud
  | LayerTypePose
  | LayerTypeEffectLayer
  | LayerTypeAdjustment  -- @deprecated Use 'effectLayer' instead
  deriving (Eq, Show, Generic)

instance ToJSON LayerType where
  toJSON LayerTypeDepth = "depth"
  toJSON LayerTypeNormal = "normal"
  toJSON LayerTypeSpline = "spline"
  toJSON LayerTypePath = "path"
  toJSON LayerTypeText = "text"
  toJSON LayerTypeShape = "shape"
  toJSON LayerTypeParticle = "particle"
  toJSON LayerTypeParticles = "particles"
  toJSON LayerTypeDepthflow = "depthflow"
  toJSON LayerTypeImage = "image"
  toJSON LayerTypeVideo = "video"
  toJSON LayerTypeAudio = "audio"
  toJSON LayerTypeGenerated = "generated"
  toJSON LayerTypeCamera = "camera"
  toJSON LayerTypeLight = "light"
  toJSON LayerTypeSolid = "solid"
  toJSON LayerTypeControl = "control"
  toJSON LayerTypeNull = "null"
  toJSON LayerTypeGroup = "group"
  toJSON LayerTypeNestedComp = "nestedComp"
  toJSON LayerTypeMatte = "matte"
  toJSON LayerTypeModel = "model"
  toJSON LayerTypePointcloud = "pointcloud"
  toJSON LayerTypePose = "pose"
  toJSON LayerTypeEffectLayer = "effectLayer"
  toJSON LayerTypeAdjustment = "adjustment"

instance FromJSON LayerType where
  parseJSON = withText "LayerType" $ \s ->
    case s of
      _ | s == T.pack "depth" -> return LayerTypeDepth
      _ | s == T.pack "normal" -> return LayerTypeNormal
      _ | s == T.pack "spline" -> return LayerTypeSpline
      _ | s == T.pack "path" -> return LayerTypePath
      _ | s == T.pack "text" -> return LayerTypeText
      _ | s == T.pack "shape" -> return LayerTypeShape
      _ | s == T.pack "particle" -> return LayerTypeParticle
      _ | s == T.pack "particles" -> return LayerTypeParticles
      _ | s == T.pack "depthflow" -> return LayerTypeDepthflow
      _ | s == T.pack "image" -> return LayerTypeImage
      _ | s == T.pack "video" -> return LayerTypeVideo
      _ | s == T.pack "audio" -> return LayerTypeAudio
      _ | s == T.pack "generated" -> return LayerTypeGenerated
      _ | s == T.pack "camera" -> return LayerTypeCamera
      _ | s == T.pack "light" -> return LayerTypeLight
      _ | s == T.pack "solid" -> return LayerTypeSolid
      _ | s == T.pack "control" -> return LayerTypeControl
      _ | s == T.pack "null" -> return LayerTypeNull
      _ | s == T.pack "group" -> return LayerTypeGroup
      _ | s == T.pack "nestedComp" -> return LayerTypeNestedComp
      _ | s == T.pack "matte" -> return LayerTypeMatte
      _ | s == T.pack "model" -> return LayerTypeModel
      _ | s == T.pack "pointcloud" -> return LayerTypePointcloud
      _ | s == T.pack "pose" -> return LayerTypePose
      _ | s == T.pack "effectLayer" -> return LayerTypeEffectLayer
      _ | s == T.pack "adjustment" -> return LayerTypeAdjustment
      _ -> fail "Invalid LayerType"

-- | Auto-orient mode
data AutoOrientMode
  = AutoOrientModeOff
  | AutoOrientModeToCamera
  | AutoOrientModeAlongPath
  | AutoOrientModeToPointOfInterest
  deriving (Eq, Show, Generic)

instance ToJSON AutoOrientMode where
  toJSON AutoOrientModeOff = "off"
  toJSON AutoOrientModeToCamera = "toCamera"
  toJSON AutoOrientModeAlongPath = "alongPath"
  toJSON AutoOrientModeToPointOfInterest = "toPointOfInterest"

instance FromJSON AutoOrientMode where
  parseJSON = withText "AutoOrientMode" $ \s ->
    case s of
      _ | s == T.pack "off" -> return AutoOrientModeOff
      _ | s == T.pack "toCamera" -> return AutoOrientModeToCamera
      _ | s == T.pack "alongPath" -> return AutoOrientModeAlongPath
      _ | s == T.pack "toPointOfInterest" -> return AutoOrientModeToPointOfInterest
      _ -> fail "Invalid AutoOrientMode"

-- | Follow path constraint (TODO: migrate full type)
data FollowPathConstraint = FollowPathConstraint
  { followPathConstraintPathLayerId :: Text
  , followPathConstraintParameter :: AnimatableProperty Double
  , followPathConstraintLookAhead :: Double
  , followPathConstraintBankingStrength :: Double
  , followPathConstraintOffsetY :: Double
  , followPathConstraintAlignToPath :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON FollowPathConstraint where
  toJSON (FollowPathConstraint pathLayerId parameter lookAhead banking offsetY alignToPath) =
    object
      [ "pathLayerId" .= pathLayerId
      , "parameter" .= parameter
      , "lookAhead" .= lookAhead
      , "bankingStrength" .= banking
      , "offsetY" .= offsetY
      , "alignToPath" .= alignToPath
      ]

instance FromJSON FollowPathConstraint where
  parseJSON = withObject "FollowPathConstraint" $ \o -> do
    pathLayerId <- o .: "pathLayerId"
    parameter <- o .: "parameter"
    lookAhead <- o .: "lookAhead"
    banking <- o .: "bankingStrength"
    offsetY <- o .: "offsetY"
    alignToPath <- o .: "alignToPath"
    if validateFinite lookAhead && validateFinite banking && validateFinite offsetY &&
       validateNormalized01 lookAhead && validateNormalized01 banking
      then return (FollowPathConstraint pathLayerId parameter lookAhead banking offsetY alignToPath)
      else fail "FollowPathConstraint: numeric values must be finite and within valid ranges"

-- | Audio path animation (TODO: migrate full type)
data AudioPathAnimation = AudioPathAnimation
  { audioPathAnimationSourceLayerId :: Text
  , audioPathAnimationFeature :: Text
  , audioPathAnimationMultiplier :: Double
  , audioPathAnimationSmoothing :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON AudioPathAnimation where
  toJSON (AudioPathAnimation sourceLayerId feature multiplier smoothing) =
    object
      [ "sourceLayerId" .= sourceLayerId
      , "feature" .= feature
      , "multiplier" .= multiplier
      , "smoothing" .= smoothing
      ]

instance FromJSON AudioPathAnimation where
  parseJSON = withObject "AudioPathAnimation" $ \o -> do
    sourceLayerId <- o .: "sourceLayerId"
    feature <- o .: "feature"
    multiplier <- o .: "multiplier"
    smoothing <- o .: "smoothing"
    if validateFinite multiplier && validateFinite smoothing &&
       validateNonNegative multiplier && validateNormalized01 smoothing
      then return (AudioPathAnimation sourceLayerId feature multiplier smoothing)
      else fail "AudioPathAnimation: numeric values must be finite and within valid ranges"

-- | Motion blur type
data MotionBlurType
  = MotionBlurTypeStandard
  | MotionBlurTypePixel
  | MotionBlurTypeDirectional
  | MotionBlurTypeRadial
  | MotionBlurTypeVector
  | MotionBlurTypeAdaptive
  deriving (Eq, Show, Generic)

instance ToJSON MotionBlurType where
  toJSON MotionBlurTypeStandard = "standard"
  toJSON MotionBlurTypePixel = "pixel"
  toJSON MotionBlurTypeDirectional = "directional"
  toJSON MotionBlurTypeRadial = "radial"
  toJSON MotionBlurTypeVector = "vector"
  toJSON MotionBlurTypeAdaptive = "adaptive"

instance FromJSON MotionBlurType where
  parseJSON = withText "MotionBlurType" $ \s ->
    case s of
      _ | s == T.pack "standard" -> return MotionBlurTypeStandard
      _ | s == T.pack "pixel" -> return MotionBlurTypePixel
      _ | s == T.pack "directional" -> return MotionBlurTypeDirectional
      _ | s == T.pack "radial" -> return MotionBlurTypeRadial
      _ | s == T.pack "vector" -> return MotionBlurTypeVector
      _ | s == T.pack "adaptive" -> return MotionBlurTypeAdaptive
      _ -> fail "Invalid MotionBlurType"

-- | Layer motion blur settings
data LayerMotionBlurSettings = LayerMotionBlurSettings
  { layerMotionBlurSettingsType :: MotionBlurType
  , layerMotionBlurSettingsShutterAngle :: Double  -- 0-720, 180 = standard film
  , layerMotionBlurSettingsShutterPhase :: Double  -- -180 to 180
  , layerMotionBlurSettingsSamplesPerFrame :: Double  -- 2-64
  , layerMotionBlurSettingsDirection :: Maybe Double  -- For directional blur: angle in degrees
  , layerMotionBlurSettingsBlurLength :: Maybe Double  -- For directional blur: blur length in pixels
  , layerMotionBlurSettingsRadialMode :: Maybe Text  -- For radial blur: 'spin' or 'zoom'
  , layerMotionBlurSettingsRadialCenterX :: Maybe Double  -- For radial blur: center point (0-1 normalized)
  , layerMotionBlurSettingsRadialCenterY :: Maybe Double
  , layerMotionBlurSettingsRadialAmount :: Maybe Double  -- For radial blur: amount (0-100)
  }
  deriving (Eq, Show, Generic)

instance ToJSON LayerMotionBlurSettings where
  toJSON (LayerMotionBlurSettings mType shutterAngle shutterPhase samplesPerFrame mDirection mBlurLength mRadialMode mRadialCenterX mRadialCenterY mRadialAmount) =
    let
      baseFields = ["type" .= mType, "shutterAngle" .= shutterAngle, "shutterPhase" .= shutterPhase, "samplesPerFrame" .= samplesPerFrame]
      withDirection = case mDirection of
        Just d -> ("direction" .= d) : baseFields
        Nothing -> baseFields
      withBlurLength = case mBlurLength of
        Just l -> ("blurLength" .= l) : withDirection
        Nothing -> withDirection
      withRadialMode = case mRadialMode of
        Just m -> ("radialMode" .= m) : withBlurLength
        Nothing -> withBlurLength
      withRadialCenterX = case mRadialCenterX of
        Just x -> ("radialCenterX" .= x) : withRadialMode
        Nothing -> withRadialMode
      withRadialCenterY = case mRadialCenterY of
        Just y -> ("radialCenterY" .= y) : withRadialCenterX
        Nothing -> withRadialCenterX
      withRadialAmount = case mRadialAmount of
        Just a -> ("radialAmount" .= a) : withRadialCenterY
        Nothing -> withRadialCenterY
    in object withRadialAmount

instance FromJSON LayerMotionBlurSettings where
  parseJSON = withObject "LayerMotionBlurSettings" $ \o -> do
    mType <- o .: "type"
    shutterAngle <- o .: "shutterAngle"
    shutterPhase <- o .: "shutterPhase"
    samplesPerFrame <- o .: "samplesPerFrame"
    mDirection <- o .:? "direction"
    mBlurLength <- o .:? "blurLength"
    mRadialMode <- o .:? "radialMode"
    mRadialCenterX <- o .:? "radialCenterX"
    mRadialCenterY <- o .:? "radialCenterY"
    mRadialAmount <- o .:? "radialAmount"
    if validateFinite shutterAngle && validateFinite shutterPhase && validateFinite samplesPerFrame &&
       shutterAngle >= 0 && shutterAngle <= 720 &&
       shutterPhase >= -180 && shutterPhase <= 180 &&
       samplesPerFrame >= 2 && samplesPerFrame <= 64 &&
       maybe True (\d -> validateFinite d) mDirection &&
       maybe True (\l -> validateFinite l && validateNonNegative l) mBlurLength &&
       maybe True (\x -> validateFinite x && validateNormalized01 x) mRadialCenterX &&
       maybe True (\y -> validateFinite y && validateNormalized01 y) mRadialCenterY &&
       maybe True (\a -> validateFinite a && validateNormalized01 (a / 100)) mRadialAmount
      then return (LayerMotionBlurSettings mType shutterAngle shutterPhase samplesPerFrame mDirection mBlurLength mRadialMode mRadialCenterX mRadialCenterY mRadialAmount)
      else fail "LayerMotionBlurSettings: numeric values must be finite and within valid ranges"

-- | Casts shadows
data CastsShadows
  = CastsShadowsOff
  | CastsShadowsOn
  | CastsShadowsOnly
  deriving (Eq, Show, Generic)

instance ToJSON CastsShadows where
  toJSON CastsShadowsOff = "off"
  toJSON CastsShadowsOn = "on"
  toJSON CastsShadowsOnly = "only"

instance FromJSON CastsShadows where
  parseJSON = withText "CastsShadows" $ \s ->
    case s of
      _ | s == T.pack "off" -> return CastsShadowsOff
      _ | s == T.pack "on" -> return CastsShadowsOn
      _ | s == T.pack "only" -> return CastsShadowsOnly
      _ -> fail "Invalid CastsShadows"

-- | Layer material options
data LayerMaterialOptions = LayerMaterialOptions
  { layerMaterialOptionsCastsShadows :: CastsShadows
  , layerMaterialOptionsLightTransmission :: Double  -- 0-100
  , layerMaterialOptionsAcceptsShadows :: Bool
  , layerMaterialOptionsAcceptsLights :: Bool
  , layerMaterialOptionsAmbient :: Double  -- 0-100%
  , layerMaterialOptionsDiffuse :: Double  -- 0-100%
  , layerMaterialOptionsSpecularIntensity :: Double  -- 0-100%
  , layerMaterialOptionsSpecularShininess :: Double  -- 0-100%
  , layerMaterialOptionsMetal :: Double  -- 0-100%
  }
  deriving (Eq, Show, Generic)

instance ToJSON LayerMaterialOptions where
  toJSON (LayerMaterialOptions castsShadows lightTransmission acceptsShadows acceptsLights ambient diffuse specularIntensity specularShininess metal) =
    object
      [ "castsShadows" .= castsShadows
      , "lightTransmission" .= lightTransmission
      , "acceptsShadows" .= acceptsShadows
      , "acceptsLights" .= acceptsLights
      , "ambient" .= ambient
      , "diffuse" .= diffuse
      , "specularIntensity" .= specularIntensity
      , "specularShininess" .= specularShininess
      , "metal" .= metal
      ]

instance FromJSON LayerMaterialOptions where
  parseJSON = withObject "LayerMaterialOptions" $ \o -> do
    castsShadows <- o .: "castsShadows"
    lightTransmission <- o .: "lightTransmission"
    acceptsShadows <- o .: "acceptsShadows"
    acceptsLights <- o .: "acceptsLights"
    ambient <- o .: "ambient"
    diffuse <- o .: "diffuse"
    specularIntensity <- o .: "specularIntensity"
    specularShininess <- o .: "specularShininess"
    metal <- o .: "metal"
    if validateFinite lightTransmission && validateFinite ambient && validateFinite diffuse &&
       validateFinite specularIntensity && validateFinite specularShininess && validateFinite metal &&
       validateNormalized01 (lightTransmission / 100) && validateNormalized01 (ambient / 100) &&
       validateNormalized01 (diffuse / 100) && validateNormalized01 (specularIntensity / 100) &&
       validateNormalized01 (specularShininess / 100) && validateNormalized01 (metal / 100)
      then return (LayerMaterialOptions castsShadows lightTransmission acceptsShadows acceptsLights ambient diffuse specularIntensity specularShininess metal)
      else fail "LayerMaterialOptions: numeric values must be finite and within valid ranges"

-- | Layer quality
data LayerQuality
  = LayerQualityDraft
  | LayerQualityBest
  deriving (Eq, Show, Generic)

instance ToJSON LayerQuality where
  toJSON LayerQualityDraft = "draft"
  toJSON LayerQualityBest = "best"

instance FromJSON LayerQuality where
  parseJSON = withText "LayerQuality" $ \s ->
    case s of
      _ | s == T.pack "draft" -> return LayerQualityDraft
      _ | s == T.pack "best" -> return LayerQualityBest
      _ -> fail "Invalid LayerQuality"

-- | Stretch anchor
data StretchAnchor
  = StretchAnchorStartFrame
  | StretchAnchorEndFrame
  | StretchAnchorCurrentFrame
  deriving (Eq, Show, Generic)

instance ToJSON StretchAnchor where
  toJSON StretchAnchorStartFrame = "startFrame"
  toJSON StretchAnchorEndFrame = "endFrame"
  toJSON StretchAnchorCurrentFrame = "currentFrame"

instance FromJSON StretchAnchor where
  parseJSON = withText "StretchAnchor" $ \s ->
    case s of
      _ | s == T.pack "startFrame" -> return StretchAnchorStartFrame
      _ | s == T.pack "endFrame" -> return StretchAnchorEndFrame
      _ | s == T.pack "currentFrame" -> return StretchAnchorCurrentFrame
      _ -> fail "Invalid StretchAnchor"

-- | Layer audio
data LayerAudio = LayerAudio
  { layerAudioLevel :: AnimatableProperty Double  -- Audio Levels in dB
  }
  deriving (Eq, Show, Generic)

instance ToJSON LayerAudio where
  toJSON (LayerAudio level) =
    object ["level" .= level]

instance FromJSON LayerAudio where
  parseJSON = withObject "LayerAudio" $ \o -> do
    level <- o .: "level"
    return (LayerAudio level)

-- ════════════════════════════════════════════════════════════════════════════
--                                            // layer // data // union // type
-- ════════════════════════════════════════════════════════════════════════════

-- | Union type of all layer data types
data LayerData
  = LayerDataSpline SplineData
  | LayerDataPath PathLayerData
  | LayerDataText TextData
  | LayerDataParticle LegacyParticleLayerData  -- Legacy
  | LayerDataParticles ParticleLayerData
  | LayerDataDepthflow DepthflowLayerData
  | LayerDataGenerated GeneratedMapData
  | LayerDataCamera CameraLayerData
  | LayerDataImage ImageLayerData
  | LayerDataVideo VideoData
  | LayerDataNestedComp NestedCompData
  | LayerDataMatte MatteLayerData
  | LayerDataShape ShapeLayerData
  | LayerDataModel ModelLayerData
  | LayerDataPointcloud PointCloudLayerData
  | LayerDataDepth DepthLayerData
  | LayerDataNormal NormalLayerData
  | LayerDataAudio AudioLayerData
  | LayerDataControl ControlLayerData
  | LayerDataPose PoseLayerData
  | LayerDataLight LightLayerData
  | LayerDataSolid SolidLayerData
  | LayerDataNull NullLayerData
  | LayerDataGroup GroupLayerData
  | LayerDataEffect EffectLayerData
  | LayerDataGeneratedLayer GeneratedLayerData
  | LayerDataProceduralMatte ProceduralMatteData
  | LayerDataNullData  -- null case
  deriving (Eq, Show, Generic)

instance ToJSON LayerData where
  toJSON (LayerDataSpline d) = toJSON d
  toJSON (LayerDataPath d) = toJSON d
  toJSON (LayerDataText d) = toJSON d
  toJSON (LayerDataParticle d) = toJSON d
  toJSON (LayerDataParticles d) = toJSON d
  toJSON (LayerDataDepthflow d) = toJSON d
  toJSON (LayerDataGenerated d) = toJSON d
  toJSON (LayerDataCamera d) = toJSON d
  toJSON (LayerDataImage d) = toJSON d
  toJSON (LayerDataVideo d) = toJSON d
  toJSON (LayerDataNestedComp d) = toJSON d
  toJSON (LayerDataMatte d) = toJSON d
  toJSON (LayerDataShape d) = toJSON d
  toJSON (LayerDataModel d) = toJSON d
  toJSON (LayerDataPointcloud d) = toJSON d
  toJSON (LayerDataDepth d) = toJSON d
  toJSON (LayerDataNormal d) = toJSON d
  toJSON (LayerDataAudio d) = toJSON d
  toJSON (LayerDataControl d) = toJSON d
  toJSON (LayerDataPose d) = toJSON d
  toJSON (LayerDataLight d) = toJSON d
  toJSON (LayerDataSolid d) = toJSON d
  toJSON (LayerDataNull d) = toJSON d
  toJSON (LayerDataGroup d) = toJSON d
  toJSON (LayerDataEffect d) = toJSON d
  toJSON (LayerDataGeneratedLayer d) = toJSON d
  toJSON (LayerDataProceduralMatte d) = toJSON d
  toJSON LayerDataNullData = Null

instance FromJSON LayerData where
  parseJSON Null = return LayerDataNullData
  parseJSON v@(Object o) = do
    -- Try parsing as each type in order until one succeeds
    -- This is not ideal but necessary for union type parsing without a discriminator
    -- In practice, LayerType should be used to determine which parser to use
    -- Try most specific types first (presence-only; type as Value to avoid ambiguity)
    mSystemConfig <- (o .:? "systemConfig" :: Parser (Maybe Value))
    mContents <- (o .:? "contents" :: Parser (Maybe Value))
    mFontFamily <- (o .:? "fontFamily" :: Parser (Maybe Value))
    mCameraId <- (o .:? "cameraId" :: Parser (Maybe Value))
    mShowGuide <- (o .:? "showGuide" :: Parser (Maybe Value))
    mPathData <- (o .:? "pathData" :: Parser (Maybe Value))
    mControlPoints <- (o .:? "controlPoints" :: Parser (Maybe Value))
    mFormat <- (o .:? "format" :: Parser (Maybe Value))
    mAssetId <- (o .:? "assetId" :: Parser (Maybe Value))
    mSize <- (o .:? "size" :: Parser (Maybe Value))
    
    case (mSystemConfig, mContents, mFontFamily, mCameraId, mShowGuide, mPathData, mControlPoints, mFormat, mAssetId, mSize) of
      (Just _, _, _, _, _, _, _, _, _, _) -> do
        p <- parseJSON v
        return (LayerDataParticles p)
      (_, Just _, _, _, _, _, _, _, _, _) -> do
        s <- parseJSON v
        return (LayerDataShape s)
      (_, _, Just _, _, _, _, _, _, _, _) -> do
        t <- parseJSON v
        return (LayerDataText t)
      (_, _, _, Just _, _, _, _, _, _, _) -> do
        c <- parseJSON v
        return (LayerDataCamera c)
      (_, _, _, _, Just _, _, _, _, _, _) -> do
        p <- parseJSON v
        return (LayerDataPath p)
      (_, _, _, _, _, Just _, Just _, _, _, _) -> do
        s <- parseJSON v
        return (LayerDataSpline s)
      (_, _, _, _, _, _, _, Just formatVal, _, _) -> do
        formatStr <- parseJSON formatVal :: Parser Text
        case formatStr of
          _ | formatStr == T.pack "gltf" -> do
            m <- parseJSON v
            return (LayerDataModel m)
          _ | formatStr == T.pack "ply" -> do
            p <- parseJSON v
            return (LayerDataPointcloud p)
          _ -> do
            i <- parseJSON v
            return (LayerDataImage i)
      (_, _, _, _, _, _, _, _, Just _, _) -> do
        i <- parseJSON v
        return (LayerDataImage i)
      (_, _, _, _, _, _, _, _, _, Just _) -> do
        s <- parseJSON v
        return (LayerDataSolid s)
      _ -> return LayerDataNullData
  parseJSON _ = return LayerDataNullData

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // layer // type
-- ════════════════════════════════════════════════════════════════════════════

-- | Layer type
data Layer = Layer
  { layerId :: Text
  , layerName :: Text
  , layerType :: LayerType
  , layerVisible :: Bool
  , layerLocked :: Bool
  , layerIsolate :: Bool  -- Isolate layer (show only this layer)
  , layerMinimized :: Maybe Bool  -- Minimized layer
  , layerThreeD :: Bool  -- 3D Layer Switch
  , layerAutoOrient :: Maybe AutoOrientMode
  , layerFollowPath :: Maybe FollowPathConstraint
  , layerAudioPathAnimation :: Maybe AudioPathAnimation
  , layerMotionBlur :: Bool  -- Motion Blur Switch
  , layerMotionBlurSettings :: Maybe LayerMotionBlurSettings
  , layerFlattenTransform :: Maybe Bool  -- Flatten Transform / Continuously Rasterize
  , layerQuality :: Maybe LayerQuality
  , layerEffectsEnabled :: Maybe Bool
  , layerFrameBlending :: Maybe Bool
  , layerEffectLayer :: Maybe Bool
  , layerAdjustmentLayer :: Maybe Bool  -- @deprecated
  , layerAudioEnabled :: Maybe Bool
  , layerLabelColor :: Maybe Text  -- Layer label color (hex)
  , layerMaterialOptions :: Maybe LayerMaterialOptions
  , layerStartFrame :: Double  -- First visible frame (0-based)
  , layerEndFrame :: Double  -- Last visible frame (0-based)
  , layerInPoint :: Maybe Double  -- @deprecated
  , layerOutPoint :: Maybe Double  -- @deprecated
  , layerTimeStretch :: Maybe Double  -- 100 = normal, 200 = half speed, 50 = double speed, negative = reversed
  , layerStretchAnchor :: Maybe StretchAnchor
  , layerParentId :: Maybe Text
  , layerBlendMode :: BlendMode
  , layerOpacity :: AnimatableProperty Double
  , layerTransform :: LayerTransform
  , layerAudio :: Maybe LayerAudio
  , layerMasks :: Maybe [Value]  -- TODO: migrate LayerMask type
  , layerMatteType :: Maybe MatteType
  , layerMatteLayerId :: Maybe Text
  , layerMatteCompositionId :: Maybe Text
  , layerPreserveTransparency :: Maybe Bool
  , layerTrackMatteType :: Maybe MatteType  -- @deprecated
  , layerTrackMatteLayerId :: Maybe Text  -- @deprecated
  , layerTrackMatteCompositionId :: Maybe Text  -- @deprecated
  , layerProperties :: [AnimatableProperty PropertyValue]
  , layerEffects :: [Value]  -- EffectInstance[] - TODO: migrate EffectInstance type
  , layerLayerStyles :: Maybe Value  -- LayerStyles - TODO: migrate LayerStyles type
  , layerData :: Maybe LayerData  -- All layer data types union
  }
  deriving (Eq, Show, Generic)

instance ToJSON Layer where
  toJSON (Layer id_ name layerType visible locked isolate mMinimized threeD mAutoOrient mFollowPath mAudioPathAnimation motionBlur mMotionBlurSettings mFlattenTransform mQuality mEffectsEnabled mFrameBlending mEffectLayer mAdjustmentLayer mAudioEnabled mLabelColor mMaterialOptions startFrame endFrame mInPoint mOutPoint mTimeStretch mStretchAnchor mParentId blendMode opacity transform mAudio mMasks mMatteType mMatteLayerId mMatteCompositionId mPreserveTransparency mTrackMatteType mTrackMatteLayerId mTrackMatteCompositionId properties effects mLayerStyles mData) =
    let
      baseFields = ["id" .= id_, "name" .= name, "type" .= layerType, "visible" .= visible, "locked" .= locked, "isolate" .= isolate, "threeD" .= threeD, "motionBlur" .= motionBlur, "startFrame" .= startFrame, "endFrame" .= endFrame, "blendMode" .= blendMode, "opacity" .= opacity, "transform" .= transform, "properties" .= properties, "effects" .= effects]
      f1 = case mMinimized of Just m -> ("minimized" .= m) : baseFields; Nothing -> baseFields
      f2 = case mAutoOrient of Just a -> ("autoOrient" .= a) : f1; Nothing -> f1
      f3 = case mFollowPath of Just f -> ("followPath" .= f) : f2; Nothing -> f2
      f4 = case mAudioPathAnimation of Just a -> ("audioPathAnimation" .= a) : f3; Nothing -> f3
      f5 = case mMotionBlurSettings of Just s -> ("motionBlurSettings" .= s) : f4; Nothing -> f4
      f6 = case mFlattenTransform of Just f -> ("flattenTransform" .= f) : f5; Nothing -> f5
      f7 = case mQuality of Just q -> ("quality" .= q) : f6; Nothing -> f6
      f8 = case mEffectsEnabled of Just e -> ("effectsEnabled" .= e) : f7; Nothing -> f7
      f9 = case mFrameBlending of Just f -> ("frameBlending" .= f) : f8; Nothing -> f8
      f10 = case mEffectLayer of Just e -> ("effectLayer" .= e) : f9; Nothing -> f9
      f11 = case mAdjustmentLayer of Just a -> ("adjustmentLayer" .= a) : f10; Nothing -> f10
      f12 = case mAudioEnabled of Just a -> ("audioEnabled" .= a) : f11; Nothing -> f11
      f13 = case mLabelColor of Just l -> ("labelColor" .= l) : f12; Nothing -> f12
      f14 = case mMaterialOptions of Just m -> ("materialOptions" .= m) : f13; Nothing -> f13
      f15 = case mInPoint of Just i -> ("inPoint" .= i) : f14; Nothing -> f14
      f16 = case mOutPoint of Just o -> ("outPoint" .= o) : f15; Nothing -> f15
      f17 = case mTimeStretch of Just t -> ("timeStretch" .= t) : f16; Nothing -> f16
      f18 = case mStretchAnchor of Just a -> ("stretchAnchor" .= a) : f17; Nothing -> f17
      f19 = case mParentId of Just p -> ("parentId" .= p) : f18; Nothing -> f18
      f20 = case mAudio of Just a -> ("audio" .= a) : f19; Nothing -> f19
      f21 = case mMasks of Just m -> ("masks" .= m) : f20; Nothing -> f20
      f22 = case mMatteType of Just t -> ("matteType" .= t) : f21; Nothing -> f21
      f23 = case mMatteLayerId of Just l -> ("matteLayerId" .= l) : f22; Nothing -> f22
      f24 = case mMatteCompositionId of Just c -> ("matteCompositionId" .= c) : f23; Nothing -> f23
      f25 = case mPreserveTransparency of Just p -> ("preserveTransparency" .= p) : f24; Nothing -> f24
      f26 = case mTrackMatteType of Just t -> ("trackMatteType" .= t) : f25; Nothing -> f25
      f27 = case mTrackMatteLayerId of Just l -> ("trackMatteLayerId" .= l) : f26; Nothing -> f26
      f28 = case mTrackMatteCompositionId of Just c -> ("trackMatteCompositionId" .= c) : f27; Nothing -> f27
      f29 = case mLayerStyles of Just s -> ("layerStyles" .= s) : f28; Nothing -> f28
      f30 = case mData of Just d -> ("data" .= d) : f29; Nothing -> f29
    in object f30

instance FromJSON Layer where
  parseJSON = withObject "Layer" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    layerType <- o .: "type"
    visible <- o .: "visible"
    locked <- o .: "locked"
    isolate <- o .: "isolate"
    mMinimized <- o .:? "minimized"
    threeD <- o .: "threeD"
    mAutoOrient <- o .:? "autoOrient"
    mFollowPath <- o .:? "followPath"
    mAudioPathAnimation <- o .:? "audioPathAnimation"
    motionBlur <- o .: "motionBlur"
    mMotionBlurSettings <- o .:? "motionBlurSettings"
    mFlattenTransform <- o .:? "flattenTransform"
    mQuality <- o .:? "quality"
    mEffectsEnabled <- o .:? "effectsEnabled"
    mFrameBlending <- o .:? "frameBlending"
    mEffectLayer <- o .:? "effectLayer"
    mAdjustmentLayer <- o .:? "adjustmentLayer"
    mAudioEnabled <- o .:? "audioEnabled"
    mLabelColor <- o .:? "labelColor"
    mMaterialOptions <- o .:? "materialOptions"
    startFrame <- o .: "startFrame"
    endFrame <- o .: "endFrame"
    mInPoint <- o .:? "inPoint"
    mOutPoint <- o .:? "outPoint"
    mTimeStretch <- o .:? "timeStretch"
    mStretchAnchor <- o .:? "stretchAnchor"
    mParentId <- o .:? "parentId"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    transform <- o .: "transform"
    mAudio <- o .:? "audio"
    mMasks <- o .:? "masks"
    mMatteType <- o .:? "matteType"
    mMatteLayerId <- o .:? "matteLayerId"
    mMatteCompositionId <- o .:? "matteCompositionId"
    mPreserveTransparency <- o .:? "preserveTransparency"
    mTrackMatteType <- o .:? "trackMatteType"
    mTrackMatteLayerId <- o .:? "trackMatteLayerId"
    mTrackMatteCompositionId <- o .:? "trackMatteCompositionId"
    propertiesParsed <- o .: "properties"
    effectsRaw <- o .: "effects"
    mLayerStyles <- o .:? "layerStyles"
    mDataObj <- o .:? "data"
    -- Validate max 10,000 properties per layer (matches Zod schema)
    properties <- case validateBoundedArray 10000 propertiesParsed of
      Left err -> fail (T.unpack err)
      Right props -> return props
    -- Validate max 1,000 effects per layer (matches Zod schema)
    effects <- case validateBoundedArray 1000 effectsRaw of
      Left err -> fail (T.unpack err)
      Right effs -> return effs
    -- Parse layer data based on layerType
    mData <- case mDataObj of
      Nothing -> return Nothing
      Just Null -> return (Just LayerDataNullData)
      Just d -> do
        -- Use layerType to determine which parser to use
        case layerType of
          LayerTypeSpline -> do
            s <- parseJSON d
            return (Just (LayerDataSpline s))
          LayerTypePath -> do
            p <- parseJSON d
            return (Just (LayerDataPath p))
          LayerTypeText -> do
            t <- parseJSON d
            return (Just (LayerDataText t))
          LayerTypeParticle -> do
            p <- parseJSON d
            return (Just (LayerDataParticle p))
          LayerTypeParticles -> do
            p <- parseJSON d
            return (Just (LayerDataParticles p))
          LayerTypeDepthflow -> do
            d' <- parseJSON d
            return (Just (LayerDataDepthflow d'))
          LayerTypeGenerated -> do
            g <- parseJSON d
            return (Just (LayerDataGenerated g))
          LayerTypeCamera -> do
            c <- parseJSON d
            return (Just (LayerDataCamera c))
          LayerTypeImage -> do
            i <- parseJSON d
            return (Just (LayerDataImage i))
          LayerTypeVideo -> do
            v <- parseJSON d
            return (Just (LayerDataVideo v))
          LayerTypeNestedComp -> do
            n <- parseJSON d
            return (Just (LayerDataNestedComp n))
          LayerTypeMatte -> do
            m <- parseJSON d
            return (Just (LayerDataMatte m))
          LayerTypeShape -> do
            s <- parseJSON d
            return (Just (LayerDataShape s))
          LayerTypeModel -> do
            m <- parseJSON d
            return (Just (LayerDataModel m))
          LayerTypePointcloud -> do
            p <- parseJSON d
            return (Just (LayerDataPointcloud p))
          LayerTypeDepth -> do
            d' <- parseJSON d
            return (Just (LayerDataDepth d'))
          LayerTypeNormal -> do
            n <- parseJSON d
            return (Just (LayerDataNormal n))
          LayerTypeAudio -> do
            a <- parseJSON d
            return (Just (LayerDataAudio a))
          LayerTypeControl -> do
            c <- parseJSON d
            return (Just (LayerDataControl c))
          LayerTypePose -> do
            p <- parseJSON d
            return (Just (LayerDataPose p))
          LayerTypeLight -> do
            l <- parseJSON d
            return (Just (LayerDataLight l))
          LayerTypeSolid -> do
            s <- parseJSON d
            return (Just (LayerDataSolid s))
          LayerTypeNull -> do
            n <- parseJSON d
            return (Just (LayerDataNull n))
          LayerTypeGroup -> do
            g <- parseJSON d
            return (Just (LayerDataGroup g))
          LayerTypeEffectLayer -> do
            e <- parseJSON d
            return (Just (LayerDataEffect e))
          LayerTypeAdjustment -> do
            e <- parseJSON d
            return (Just (LayerDataEffect e))
          -- All LayerType cases are explicitly handled above
          -- No catch-all needed - compiler will warn if new cases are added
    -- Validate max 100 masks per layer (matches Zod schema)
    mMasksValidated <- case mMasks of
      Nothing -> return Nothing
      Just masksRaw -> case validateBoundedArray 100 masksRaw of
        Left err -> fail (T.unpack err)
        Right masks -> return (Just masks)
    -- Validate numeric values
    if validateFinite startFrame && validateFinite endFrame &&
       validateNonNegative startFrame && validateNonNegative endFrame &&
       endFrame >= startFrame &&  -- Matches Zod schema refinement: endFrame must be >= startFrame
       maybe True (\t -> validateFinite t && t /= 0) mTimeStretch &&
       maybe True (\i -> validateFinite i && validateNonNegative i) mInPoint &&
       maybe True (\outVal -> validateFinite outVal && validateNonNegative outVal) mOutPoint
      then return (Layer id_ name layerType visible locked isolate mMinimized threeD mAutoOrient mFollowPath mAudioPathAnimation motionBlur mMotionBlurSettings mFlattenTransform mQuality mEffectsEnabled mFrameBlending mEffectLayer mAdjustmentLayer mAudioEnabled mLabelColor mMaterialOptions startFrame endFrame mInPoint mOutPoint mTimeStretch mStretchAnchor mParentId blendMode opacity transform mAudio mMasksValidated mMatteType mMatteLayerId mMatteCompositionId mPreserveTransparency mTrackMatteType mTrackMatteLayerId mTrackMatteCompositionId properties effects mLayerStyles mData)
      else fail "Layer: numeric values must be finite and within valid ranges, and endFrame must be >= startFrame"
