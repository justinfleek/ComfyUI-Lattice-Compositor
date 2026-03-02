-- |
-- Module      : Lattice.Types.LayerData
-- Description : Simple layer data types with minimal dependencies
-- 
-- Migrated from ui/src/types/project.ts
-- Starting with simplest layer data types (Null, Control, Effect, Solid, Group)
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.LayerData
  ( -- Null layer
    NullLayerData(..)
  , createDefaultNullLayerData
  -- Control layer
  , ControlLayerData(..)
  , IconShape(..)
  -- Effect layer
  , EffectLayerData(..)
  , createDefaultEffectLayerData
  -- Solid layer
  , SolidLayerData(..)
  , MotionPathConfig(..)
  , MotionPathKeyframe(..)
  , SpeedGraphKeyframe(..)
  , createDefaultSolidLayerData
  -- Group layer
  , GroupLayerData(..)
  -- Light layer
  , LightLayerData(..)
  , LightType(..)
  , FalloffType(..)
  , createDefaultLightLayerData
  -- Pose layer
  , PoseLayerData(..)
  , Pose(..)
  , PoseKeypoint(..)
  , PoseFormat(..)
  -- Generated layer
  , GeneratedLayerData(..)
  , GenerationType(..)
  , GenerationStatus(..)
  -- Matte layer
  , MatteLayerData(..)
  , MatteType(..)
  , MattePreviewMode(..)
  -- Legacy particle layer
  , LegacyParticleLayerData(..)
  , LegacyEmitterType(..)
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
import Data.Text (Text)
import GHC.Generics (Generic)
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , validateFinite
  , validateNonNegative
  , validateNormalized01
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // null // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Null layer data - invisible transform controller
data NullLayerData = NullLayerData
  { nullLayerDataSize :: Double  -- Visual size of null icon in editor
  }
  deriving (Eq, Show, Generic)

instance ToJSON NullLayerData where
  toJSON (NullLayerData size) = object ["size" .= size]

instance FromJSON NullLayerData where
  parseJSON = withObject "NullLayerData" $ \o -> do
    size <- o .: "size"
    if validateFinite size && validateNonNegative size
      then return (NullLayerData size)
      else fail "NullLayerData: size must be finite and non-negative"

-- | Create default null layer data
createDefaultNullLayerData :: NullLayerData
createDefaultNullLayerData = NullLayerData { nullLayerDataSize = 40.0 }

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // control // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Control layer data - null object / transform controller
data ControlLayerData = ControlLayerData
  { controlLayerDataSize :: Double  -- Visual size of control icon in editor
  , controlLayerDataShowAxes :: Bool  -- Show XYZ axis indicators
  , controlLayerDataShowIcon :: Bool  -- Show control layer icon/gizmo
  , controlLayerDataIconShape :: IconShape  -- Icon shape
  , controlLayerDataIconColor :: Text  -- Icon color (hex)
  }
  deriving (Eq, Show, Generic)

-- | Icon shape for control layer
data IconShape
  = IconShapeCrosshair
  | IconShapeDiamond
  | IconShapeCircle
  | IconShapeSquare
  deriving (Eq, Show, Generic)

instance ToJSON IconShape where
  toJSON IconShapeCrosshair = "crosshair"
  toJSON IconShapeDiamond = "diamond"
  toJSON IconShapeCircle = "circle"
  toJSON IconShapeSquare = "square"

instance FromJSON IconShape where
  parseJSON = withText "IconShape" $ \s ->
    case s of
      "crosshair" -> return IconShapeCrosshair
      "diamond" -> return IconShapeDiamond
      "circle" -> return IconShapeCircle
      "square" -> return IconShapeSquare
      _ -> fail "Invalid IconShape"

instance ToJSON ControlLayerData where
  toJSON (ControlLayerData size showAxes showIcon shape color) =
    object
      [ "size" .= size
      , "showAxes" .= showAxes
      , "showIcon" .= showIcon
      , "iconShape" .= shape
      , "iconColor" .= color
      ]

instance FromJSON ControlLayerData where
  parseJSON = withObject "ControlLayerData" $ \o -> do
    size <- o .: "size"
    showAxes <- o .: "showAxes"
    showIcon <- o .: "showIcon"
    shape <- o .: "iconShape"
    color <- o .: "iconColor"
    if validateFinite size && validateNonNegative size
      then return (ControlLayerData size showAxes showIcon shape color)
      else fail "ControlLayerData: size must be finite and non-negative"

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // effect // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Effect layer data - effects apply to layers below
-- (Previously called Adjustment Layer - renamed for trade dress)
data EffectLayerData = EffectLayerData
  { effectLayerDataEffectLayer :: Bool  -- Effect layer flag (always true for effect layers)
  , effectLayerDataAdjustmentLayer :: Bool  -- @deprecated Use effectLayer - backwards compatibility
  , effectLayerDataColor :: Text  -- Layer label color for organization (hex)
  }
  deriving (Eq, Show, Generic)

instance ToJSON EffectLayerData where
  toJSON (EffectLayerData effectLayer adjustmentLayer color) =
    object
      [ "effectLayer" .= effectLayer
      , "adjustmentLayer" .= adjustmentLayer
      , "color" .= color
      ]

instance FromJSON EffectLayerData where
  parseJSON = withObject "EffectLayerData" $ \o -> do
    effectLayer <- o .: "effectLayer"
    adjustmentLayer <- o .: "adjustmentLayer"
    color <- o .: "color"
    return (EffectLayerData effectLayer adjustmentLayer color)

-- | Create default effect layer data
createDefaultEffectLayerData :: EffectLayerData
createDefaultEffectLayerData =
  EffectLayerData
    { effectLayerDataEffectLayer = True
    , effectLayerDataAdjustmentLayer = True  -- Backwards compatibility
    , effectLayerDataColor = "#FF6B6B"  -- Default red color for effect layers
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // solid // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Motion path keyframe for solid layer
data MotionPathKeyframe = MotionPathKeyframe
  { motionPathKeyframeFrame :: Double
  , motionPathKeyframeProgress :: Double  -- Progress (0-100)
  }
  deriving (Eq, Show, Generic)

instance ToJSON MotionPathKeyframe where
  toJSON (MotionPathKeyframe frame progress) =
    object ["frame" .= frame, "progress" .= progress]

instance FromJSON MotionPathKeyframe where
  parseJSON = withObject "MotionPathKeyframe" $ \o -> do
    frame <- o .: "frame"
    progress <- o .: "progress"
    if validateFinite frame && validateFinite progress &&
       validateNonNegative frame && progress >= 0 && progress <= 100
      then return (MotionPathKeyframe frame progress)
      else fail "MotionPathKeyframe: frame must be finite and non-negative, progress must be 0-100"

-- | Speed graph keyframe for variable speed along path
data SpeedGraphKeyframe = SpeedGraphKeyframe
  { speedGraphKeyframeFrame :: Double
  , speedGraphKeyframeSpeed :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON SpeedGraphKeyframe where
  toJSON (SpeedGraphKeyframe frame speed) =
    object ["frame" .= frame, "speed" .= speed]

instance FromJSON SpeedGraphKeyframe where
  parseJSON = withObject "SpeedGraphKeyframe" $ \o -> do
    frame <- o .: "frame"
    speed <- o .: "speed"
    if validateFinite frame && validateFinite speed && validateNonNegative frame
      then return (SpeedGraphKeyframe frame speed)
      else fail "SpeedGraphKeyframe: frame must be finite and non-negative, speed must be finite"

-- | Motion path configuration for layer position animation
data MotionPathConfig = MotionPathConfig
  { motionPathConfigEnabled :: Bool
  , motionPathConfigPath :: [Vec2]  -- Inline path points
  , motionPathConfigOrientToPath :: Maybe Bool  -- Auto-orient rotation to path tangent
  , motionPathConfigKeyframes :: Maybe [MotionPathKeyframe]  -- Progress keyframes (0-100)
  , motionPathConfigSpeedGraph :: Maybe [SpeedGraphKeyframe]  -- Speed keyframes for variable speed along path
  }
  deriving (Eq, Show, Generic)

instance ToJSON MotionPathConfig where
  toJSON (MotionPathConfig enabled path orient keyframes speedGraph) =
    let
      baseFields = ["enabled" .= enabled, "path" .= path]
      withOrient = case orient of Just o -> ("orientToPath" .= o) : baseFields; Nothing -> baseFields
      withKeyframes = case keyframes of Just k -> ("keyframes" .= k) : withOrient; Nothing -> withOrient
      withSpeedGraph = case speedGraph of Just s -> ("speedGraph" .= s) : withKeyframes; Nothing -> withKeyframes
    in object withSpeedGraph

instance FromJSON MotionPathConfig where
  parseJSON = withObject "MotionPathConfig" $ \o -> do
    enabled <- o .: "enabled"
    path <- o .: "path"
    orient <- o .:? "orientToPath"
    keyframes <- o .:? "keyframes"
    speedGraph <- o .:? "speedGraph"
    return (MotionPathConfig enabled path orient keyframes speedGraph)

-- | Solid layer data - solid color rectangle
data SolidLayerData = SolidLayerData
  { solidLayerDataColor :: Text  -- Fill color (hex)
  , solidLayerDataWidth :: Double  -- Width (defaults to composition width)
  , solidLayerDataHeight :: Double  -- Height (defaults to composition height)
  , solidLayerDataShadowCatcher :: Maybe Bool  -- Shadow catcher mode - renders only shadows, not the solid color
  , solidLayerDataShadowOpacity :: Maybe Double  -- Shadow opacity (0-100) when in shadow catcher mode
  , solidLayerDataShadowColor :: Maybe Text  -- Shadow color (defaults to black)
  , solidLayerDataReceiveShadow :: Maybe Bool  -- Receive shadows from lights
  , solidLayerDataMotionPath :: Maybe MotionPathConfig  -- Motion path for position animation along inline path points
  }
  deriving (Eq, Show, Generic)

instance ToJSON SolidLayerData where
  toJSON (SolidLayerData color width height shadowCatcher shadowOpacity shadowColor receiveShadow motionPath) =
    let
      baseFields = ["color" .= color, "width" .= width, "height" .= height]
      f1 = case shadowCatcher of Just s -> ("shadowCatcher" .= s) : baseFields; Nothing -> baseFields
      f2 = case shadowOpacity of Just o -> ("shadowOpacity" .= o) : f1; Nothing -> f1
      f3 = case shadowColor of Just c -> ("shadowColor" .= c) : f2; Nothing -> f2
      f4 = case receiveShadow of Just r -> ("receiveShadow" .= r) : f3; Nothing -> f3
      f5 = case motionPath of Just m -> ("motionPath" .= m) : f4; Nothing -> f4
    in object f5

instance FromJSON SolidLayerData where
  parseJSON = withObject "SolidLayerData" $ \o -> do
    color <- o .: "color"
    width <- o .: "width"
    height <- o .: "height"
    shadowCatcher <- o .:? "shadowCatcher"
    shadowOpacity <- o .:? "shadowOpacity"
    receiveShadow <- o .:? "receiveShadow"
    shadowColor <- o .:? "shadowColor"
    motionPath <- o .:? "motionPath"
    -- Validate dimensions
    if validateFinite width && validateFinite height &&
       validateNonNegative width && validateNonNegative height
      then do
        -- Validate shadowOpacity if present
        case shadowOpacity of
          Nothing -> return ()
          Just op -> if validateFinite op && op >= 0 && op <= 100
            then return ()
            else fail "SolidLayerData: shadowOpacity must be 0-100"
        return (SolidLayerData color width height shadowCatcher shadowOpacity shadowColor receiveShadow motionPath)
      else fail "SolidLayerData: width and height must be finite and non-negative"

-- | Create default solid layer data
createDefaultSolidLayerData :: Double -> Double -> SolidLayerData
createDefaultSolidLayerData width height =
  SolidLayerData
    { solidLayerDataColor = "#808080"
    , solidLayerDataWidth = width
    , solidLayerDataHeight = height
    , solidLayerDataShadowCatcher = Nothing
    , solidLayerDataShadowOpacity = Nothing
    , solidLayerDataShadowColor = Nothing
    , solidLayerDataReceiveShadow = Nothing
    , solidLayerDataMotionPath = Nothing
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // group // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Group layer data - layer folder/group
data GroupLayerData = GroupLayerData
  { groupLayerDataCollapsed :: Bool  -- Collapsed state in timeline
  , groupLayerDataColor :: Maybe Text  -- Group color label (hex, null if none)
  , groupLayerDataPassThrough :: Bool  -- Pass-through mode (group doesn't create intermediate composite)
  , groupLayerDataIsolate :: Bool  -- Isolate group (only show group contents when selected)
  }
  deriving (Eq, Show, Generic)

instance ToJSON GroupLayerData where
  toJSON (GroupLayerData collapsed mColor passThrough isolate) =
    let
      baseFields = ["collapsed" .= collapsed, "passThrough" .= passThrough, "isolate" .= isolate]
      withColor = case mColor of Just c -> ("color" .= c) : baseFields; Nothing -> baseFields
    in object withColor

instance FromJSON GroupLayerData where
  parseJSON = withObject "GroupLayerData" $ \o -> do
    collapsed <- o .: "collapsed"
    mColor <- o .:? "color"
    passThrough <- o .: "passThrough"
    isolate <- o .: "isolate"
    return (GroupLayerData collapsed mColor passThrough isolate)

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // light // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Light type
data LightType
  = LightTypePoint
  | LightTypeSpot
  | LightTypeDirectional
  | LightTypeAmbient
  deriving (Eq, Show, Generic)

instance ToJSON LightType where
  toJSON LightTypePoint = "point"
  toJSON LightTypeSpot = "spot"
  toJSON LightTypeDirectional = "directional"
  toJSON LightTypeAmbient = "ambient"

instance FromJSON LightType where
  parseJSON = withText "LightType" $ \s ->
    case s of
      "point" -> return LightTypePoint
      "spot" -> return LightTypeSpot
      "directional" -> return LightTypeDirectional
      "ambient" -> return LightTypeAmbient
      _ -> fail "Invalid LightType"

-- | Falloff type
data FalloffType
  = FalloffNone
  | FalloffLinear
  | FalloffQuadratic
  | FalloffSmooth
  deriving (Eq, Show, Generic)

instance ToJSON FalloffType where
  toJSON FalloffNone = "none"
  toJSON FalloffLinear = "linear"
  toJSON FalloffQuadratic = "quadratic"
  toJSON FalloffSmooth = "smooth"

instance FromJSON FalloffType where
  parseJSON = withText "FalloffType" $ \s ->
    case s of
      "none" -> return FalloffNone
      "linear" -> return FalloffLinear
      "quadratic" -> return FalloffQuadratic
      "smooth" -> return FalloffSmooth
      _ -> fail "Invalid FalloffType"

-- | Light layer data - point, spot, directional, ambient lights
data LightLayerData = LightLayerData
  { lightLayerDataLightType :: LightType  -- Light type
  , lightLayerDataColor :: Text  -- Light color (hex)
  , lightLayerDataIntensity :: Double  -- Light intensity (0-100+)
  , lightLayerDataRadius :: Double  -- Light radius (for point/spot lights)
  , lightLayerDataFalloff :: FalloffType  -- Falloff type
  , lightLayerDataFalloffDistance :: Double  -- Falloff distance
  , lightLayerDataCastShadows :: Bool  -- Cast shadows
  , lightLayerDataShadowDarkness :: Double  -- Shadow darkness (0-100)
  , lightLayerDataShadowDiffusion :: Double  -- Shadow diffusion/softness
  , lightLayerDataConeAngle :: Maybe Double  -- Cone angle for spot lights (degrees)
  , lightLayerDataConeFeather :: Maybe Double  -- Cone feather for spot light soft edge (0-100)
  , lightLayerDataTarget :: Maybe Vec3  -- Target position for spot/directional lights
  }
  deriving (Eq, Show, Generic)

instance ToJSON LightLayerData where
  toJSON (LightLayerData lightType color intensity radius falloff falloffDist castShadows shadowDark shadowDiff mConeAngle mConeFeather mTarget) =
    let
      baseFields = ["lightType" .= lightType, "color" .= color, "intensity" .= intensity, "radius" .= radius, "falloff" .= falloff, "falloffDistance" .= falloffDist, "castShadows" .= castShadows, "shadowDarkness" .= shadowDark, "shadowDiffusion" .= shadowDiff]
      withConeAngle = case mConeAngle of Just a -> ("coneAngle" .= a) : baseFields; Nothing -> baseFields
      withConeFeather = case mConeFeather of Just f -> ("coneFeather" .= f) : withConeAngle; Nothing -> withConeAngle
      withTarget = case mTarget of Just t -> ("target" .= t) : withConeFeather; Nothing -> withConeFeather
    in object withTarget

instance FromJSON LightLayerData where
  parseJSON = withObject "LightLayerData" $ \o -> do
    lightType <- o .: "lightType"
    color <- o .: "color"
    intensity <- o .: "intensity"
    radius <- o .: "radius"
    falloff <- o .: "falloff"
    falloffDist <- o .: "falloffDistance"
    castShadows <- o .: "castShadows"
    shadowDark <- o .: "shadowDarkness"
    shadowDiff <- o .: "shadowDiffusion"
    mConeAngle <- o .:? "coneAngle"
    mConeFeather <- o .:? "coneFeather"
    mTarget <- o .:? "target"
    -- Validate numeric values
    if validateFinite intensity && validateFinite radius &&
       validateFinite falloffDist && validateFinite shadowDark &&
       validateFinite shadowDiff &&
       validateNonNegative intensity && validateNonNegative radius &&
       validateNonNegative falloffDist && shadowDark >= 0 && shadowDark <= 100 &&
       validateNonNegative shadowDiff &&
       maybe True (\a -> validateFinite a && validateNonNegative a) mConeAngle &&
       maybe True (\f -> validateFinite f && f >= 0 && f <= 100) mConeFeather
      then return (LightLayerData lightType color intensity radius falloff falloffDist castShadows shadowDark shadowDiff mConeAngle mConeFeather mTarget)
      else fail "LightLayerData: numeric values must be finite and within valid ranges"

-- | Create default light layer data
createDefaultLightLayerData :: LightLayerData
createDefaultLightLayerData =
  LightLayerData
    { lightLayerDataLightType = LightTypePoint
    , lightLayerDataColor = "#ffffff"
    , lightLayerDataIntensity = 100.0
    , lightLayerDataRadius = 500.0
    , lightLayerDataFalloff = FalloffNone
    , lightLayerDataFalloffDistance = 500.0
    , lightLayerDataCastShadows = False
    , lightLayerDataShadowDarkness = 100.0
    , lightLayerDataShadowDiffusion = 0.0
    , lightLayerDataConeAngle = Nothing
    , lightLayerDataConeFeather = Nothing
    , lightLayerDataTarget = Nothing
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // pose // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Pose format
data PoseFormat
  = PoseFormatCOCO18
  | PoseFormatBody25
  | PoseFormatCustom
  deriving (Eq, Show, Generic)

instance ToJSON PoseFormat where
  toJSON PoseFormatCOCO18 = "coco18"
  toJSON PoseFormatBody25 = "body25"
  toJSON PoseFormatCustom = "custom"

instance FromJSON PoseFormat where
  parseJSON = withText "PoseFormat" $ \s ->
    case s of
      "coco18" -> return PoseFormatCOCO18
      "body25" -> return PoseFormatBody25
      "custom" -> return PoseFormatCustom
      _ -> fail "Invalid PoseFormat"

-- | Pose keypoint
data PoseKeypoint = PoseKeypoint
  { poseKeypointX :: Double  -- X position (0-1 normalized)
  , poseKeypointY :: Double  -- Y position (0-1 normalized)
  , poseKeypointConfidence :: Double  -- Confidence/visibility (0-1, 0 = invisible)
  }
  deriving (Eq, Show, Generic)

instance ToJSON PoseKeypoint where
  toJSON (PoseKeypoint x y conf) =
    object ["x" .= x, "y" .= y, "confidence" .= conf]

instance FromJSON PoseKeypoint where
  parseJSON = withObject "PoseKeypoint" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    conf <- o .: "confidence"
    if validateNormalized01 x && validateNormalized01 y &&
       validateNormalized01 conf
      then return (PoseKeypoint x y conf)
      else fail "PoseKeypoint: x, y, and confidence must be in range [0, 1]"

-- | Pose
data Pose = Pose
  { poseId :: Text  -- Unique ID for this pose
  , poseKeypoints :: [PoseKeypoint]  -- Array of keypoints (length depends on format)
  , poseFormat :: PoseFormat  -- Pose format
  }
  deriving (Eq, Show, Generic)

instance ToJSON Pose where
  toJSON (Pose id_ keypoints format) =
    object ["id" .= id_, "keypoints" .= keypoints, "format" .= format]

instance FromJSON Pose where
  parseJSON = withObject "Pose" $ \o -> do
    id_ <- o .: "id"
    keypoints <- o .: "keypoints"
    format <- o .: "format"
    return (Pose id_ keypoints format)

-- | Pose layer data - OpenPose skeleton for ControlNet conditioning
data PoseLayerData = PoseLayerData
  { poseLayerDataPoses :: [Pose]  -- All poses in this layer
  , poseLayerDataFormat :: PoseFormat  -- Pose format
  , poseLayerDataNormalized :: Bool  -- Whether keypoints are normalized (0-1)
  , poseLayerDataBoneWidth :: Double  -- Bone line width
  , poseLayerDataKeypointRadius :: Double  -- Keypoint circle radius
  , poseLayerDataShowKeypoints :: Bool  -- Show keypoint circles
  , poseLayerDataShowBones :: Bool  -- Show bone connections
  , poseLayerDataShowLabels :: Bool  -- Show keypoint labels
  , poseLayerDataUseDefaultColors :: Bool  -- Use OpenPose standard colors
  , poseLayerDataCustomBoneColor :: Text  -- Custom bone color (when not using defaults)
  , poseLayerDataCustomKeypointColor :: Text  -- Custom keypoint color (when not using defaults)
  , poseLayerDataSelectedKeypoint :: Int  -- Selected keypoint index for editing (-1 = none)
  , poseLayerDataSelectedPose :: Int  -- Selected pose index for editing (-1 = none)
  }
  deriving (Eq, Show, Generic)

instance ToJSON PoseLayerData where
  toJSON (PoseLayerData poses format normalized boneWidth keypointRadius showKeypoints showBones showLabels useDefaultColors customBoneColor customKeypointColor selectedKeypoint selectedPose) =
    object
      [ "poses" .= poses
      , "format" .= format
      , "normalized" .= normalized
      , "boneWidth" .= boneWidth
      , "keypointRadius" .= keypointRadius
      , "showKeypoints" .= showKeypoints
      , "showBones" .= showBones
      , "showLabels" .= showLabels
      , "useDefaultColors" .= useDefaultColors
      , "customBoneColor" .= customBoneColor
      , "customKeypointColor" .= customKeypointColor
      , "selectedKeypoint" .= selectedKeypoint
      , "selectedPose" .= selectedPose
      ]

instance FromJSON PoseLayerData where
  parseJSON = withObject "PoseLayerData" $ \o -> do
    poses <- o .: "poses"
    format <- o .: "format"
    normalized <- o .: "normalized"
    boneWidth <- o .: "boneWidth"
    keypointRadius <- o .: "keypointRadius"
    showKeypoints <- o .: "showKeypoints"
    showBones <- o .: "showBones"
    showLabels <- o .: "showLabels"
    useDefaultColors <- o .: "useDefaultColors"
    customBoneColor <- o .: "customBoneColor"
    customKeypointColor <- o .: "customKeypointColor"
    selectedKeypoint <- o .: "selectedKeypoint"
    selectedPose <- o .: "selectedPose"
    -- Validate numeric values
    if validateFinite boneWidth && validateFinite keypointRadius &&
       validateNonNegative boneWidth && validateNonNegative keypointRadius
      then return (PoseLayerData poses format normalized boneWidth keypointRadius showKeypoints showBones showLabels useDefaultColors customBoneColor customKeypointColor selectedKeypoint selectedPose)
      else fail "PoseLayerData: boneWidth and keypointRadius must be finite and non-negative"

-- ════════════════════════════════════════════════════════════════════════════
--                                                // generated // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Generation type
data GenerationType
  = GenerationTypeDepth
  | GenerationTypeNormal
  | GenerationTypeEdge
  | GenerationTypeSegment
  | GenerationTypeInpaint
  | GenerationTypeCustom
  deriving (Eq, Show, Generic)

instance ToJSON GenerationType where
  toJSON GenerationTypeDepth = "depth"
  toJSON GenerationTypeNormal = "normal"
  toJSON GenerationTypeEdge = "edge"
  toJSON GenerationTypeSegment = "segment"
  toJSON GenerationTypeInpaint = "inpaint"
  toJSON GenerationTypeCustom = "custom"

instance FromJSON GenerationType where
  parseJSON = withText "GenerationType" $ \s ->
    case s of
      "depth" -> return GenerationTypeDepth
      "normal" -> return GenerationTypeNormal
      "edge" -> return GenerationTypeEdge
      "segment" -> return GenerationTypeSegment
      "inpaint" -> return GenerationTypeInpaint
      "custom" -> return GenerationTypeCustom
      _ -> fail "Invalid GenerationType"

-- | Generation status
data GenerationStatus
  = GenerationStatusPending
  | GenerationStatusGenerating
  | GenerationStatusComplete
  | GenerationStatusError
  deriving (Eq, Show, Generic)

instance ToJSON GenerationStatus where
  toJSON GenerationStatusPending = "pending"
  toJSON GenerationStatusGenerating = "generating"
  toJSON GenerationStatusComplete = "complete"
  toJSON GenerationStatusError = "error"

instance FromJSON GenerationStatus where
  parseJSON = withText "GenerationStatus" $ \s ->
    case s of
      "pending" -> return GenerationStatusPending
      "generating" -> return GenerationStatusGenerating
      "complete" -> return GenerationStatusComplete
      "error" -> return GenerationStatusError
      _ -> fail "Invalid GenerationStatus"

-- | Generated layer data - AI-generated content
data GeneratedLayerData = GeneratedLayerData
  { generatedLayerDataGenerationType :: GenerationType  -- Generated content type
  , generatedLayerDataSourceLayerId :: Maybe Text  -- Source layer ID (input to generation)
  , generatedLayerDataModel :: Text  -- Model used for generation
  , generatedLayerDataParameters :: Value  -- Generation parameters (model-specific) - JSON object
  , generatedLayerDataGeneratedAssetId :: Maybe Text  -- Generated asset ID (output)
  , generatedLayerDataStatus :: GenerationStatus  -- Generation status
  , generatedLayerDataErrorMessage :: Maybe Text  -- Error message if status is error
  , generatedLayerDataAutoRegenerate :: Bool  -- Auto-regenerate when source changes
  , generatedLayerDataLastGenerated :: Maybe Text  -- Last generation timestamp (ISO string)
  }
  deriving (Eq, Show, Generic)

instance ToJSON GeneratedLayerData where
  toJSON (GeneratedLayerData genType mSourceLayerId model params mGeneratedAssetId status mErrorMsg autoRegen mLastGen) =
    let
      baseFields = ["generationType" .= genType, "model" .= model, "parameters" .= params, "status" .= status, "autoRegenerate" .= autoRegen]
      f1 = case mSourceLayerId of Just s -> ("sourceLayerId" .= s) : baseFields; Nothing -> baseFields
      f2 = case mGeneratedAssetId of Just a -> ("generatedAssetId" .= a) : f1; Nothing -> f1
      f3 = case mErrorMsg of Just e -> ("errorMessage" .= e) : f2; Nothing -> f2
      f4 = case mLastGen of Just l -> ("lastGenerated" .= l) : f3; Nothing -> f3
    in object f4

instance FromJSON GeneratedLayerData where
  parseJSON = withObject "GeneratedLayerData" $ \o -> do
    genType <- o .: "generationType"
    mSourceLayerId <- o .:? "sourceLayerId"
    model <- o .: "model"
    params <- o .: "parameters"
    mGeneratedAssetId <- o .:? "generatedAssetId"
    status <- o .: "status"
    mErrorMsg <- o .:? "errorMessage"
    autoRegen <- o .: "autoRegenerate"
    mLastGen <- o .:? "lastGenerated"
    return (GeneratedLayerData genType mSourceLayerId model params mGeneratedAssetId status mErrorMsg autoRegen mLastGen)

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // matte // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Matte extraction method
data MatteType
  = MatteTypeLuminance
  | MatteTypeAlpha
  | MatteTypeRed
  | MatteTypeGreen
  | MatteTypeBlue
  | MatteTypeHue
  | MatteTypeSaturation
  deriving (Eq, Show, Generic)

instance ToJSON MatteType where
  toJSON MatteTypeLuminance = "luminance"
  toJSON MatteTypeAlpha = "alpha"
  toJSON MatteTypeRed = "red"
  toJSON MatteTypeGreen = "green"
  toJSON MatteTypeBlue = "blue"
  toJSON MatteTypeHue = "hue"
  toJSON MatteTypeSaturation = "saturation"

instance FromJSON MatteType where
  parseJSON = withText "MatteType" $ \s ->
    case s of
      "luminance" -> return MatteTypeLuminance
      "alpha" -> return MatteTypeAlpha
      "red" -> return MatteTypeRed
      "green" -> return MatteTypeGreen
      "blue" -> return MatteTypeBlue
      "hue" -> return MatteTypeHue
      "saturation" -> return MatteTypeSaturation
      _ -> fail "Invalid MatteType"

-- | Matte preview mode
data MattePreviewMode
  = MattePreviewMatte
  | MattePreviewComposite
  | MattePreviewOverlay
  deriving (Eq, Show, Generic)

instance ToJSON MattePreviewMode where
  toJSON MattePreviewMatte = "matte"
  toJSON MattePreviewComposite = "composite"
  toJSON MattePreviewOverlay = "overlay"

instance FromJSON MattePreviewMode where
  parseJSON = withText "MattePreviewMode" $ \s ->
    case s of
      "matte" -> return MattePreviewMatte
      "composite" -> return MattePreviewComposite
      "overlay" -> return MattePreviewOverlay
      _ -> fail "Invalid MattePreviewMode"

-- | Matte layer data - procedural matte/mask generation
data MatteLayerData = MatteLayerData
  { matteLayerDataMatteType :: MatteType  -- Matte extraction method
  , matteLayerDataInvert :: Bool  -- Invert the matte
  , matteLayerDataThreshold :: Double  -- Threshold for matte cutoff
  , matteLayerDataFeather :: Double  -- Feather/blur amount
  , matteLayerDataExpansion :: Double  -- Expand/contract matte edges
  , matteLayerDataSourceLayerId :: Maybe Text  -- Source layer ID (if extracting matte from another layer)
  , matteLayerDataPreviewMode :: MattePreviewMode  -- Preview mode
  }
  deriving (Eq, Show, Generic)

instance ToJSON MatteLayerData where
  toJSON (MatteLayerData matteType invert threshold feather expansion mSourceLayerId previewMode) =
    let
      baseFields = ["matteType" .= matteType, "invert" .= invert, "threshold" .= threshold, "feather" .= feather, "expansion" .= expansion, "previewMode" .= previewMode]
      withSourceLayerId = case mSourceLayerId of Just s -> ("sourceLayerId" .= s) : baseFields; Nothing -> baseFields
    in object withSourceLayerId

instance FromJSON MatteLayerData where
  parseJSON = withObject "MatteLayerData" $ \o -> do
    matteType <- o .: "matteType"
    invert <- o .: "invert"
    threshold <- o .: "threshold"
    feather <- o .: "feather"
    expansion <- o .: "expansion"
    mSourceLayerId <- o .:? "sourceLayerId"
    previewMode <- o .: "previewMode"
    -- Validate numeric values
    if validateFinite threshold && validateFinite feather &&
       validateFinite expansion && validateNonNegative feather &&
       validateNonNegative expansion
      then return (MatteLayerData matteType invert threshold feather expansion mSourceLayerId previewMode)
      else fail "MatteLayerData: numeric values must be finite, feather and expansion must be non-negative"

-- ════════════════════════════════════════════════════════════════════════════
--                                       // legacy // particle // layer // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Legacy emitter type
data LegacyEmitterType
  = LegacyEmitterPoint
  | LegacyEmitterLine
  | LegacyEmitterCircle
  | LegacyEmitterBox
  deriving (Eq, Show, Generic)

instance ToJSON LegacyEmitterType where
  toJSON LegacyEmitterPoint = "point"
  toJSON LegacyEmitterLine = "line"
  toJSON LegacyEmitterCircle = "circle"
  toJSON LegacyEmitterBox = "box"

instance FromJSON LegacyEmitterType where
  parseJSON = withText "LegacyEmitterType" $ \s ->
    case s of
      "point" -> return LegacyEmitterPoint
      "line" -> return LegacyEmitterLine
      "circle" -> return LegacyEmitterCircle
      "box" -> return LegacyEmitterBox
      _ -> fail "Invalid LegacyEmitterType"

-- | Legacy particle layer data (for backwards compatibility)
-- @deprecated Use ParticleLayerData with 'particles' type instead
data LegacyParticleLayerData = LegacyParticleLayerData
  { legacyParticleLayerDataEmitterType :: LegacyEmitterType  -- @deprecated Use ParticleLayerData with 'particles' type instead
  , legacyParticleLayerDataParticleCount :: Double
  , legacyParticleLayerDataLifetime :: Double
  , legacyParticleLayerDataSpeed :: Double
  , legacyParticleLayerDataSpread :: Double
  , legacyParticleLayerDataGravity :: Double
  , legacyParticleLayerDataColor :: Text  -- Hex color
  , legacyParticleLayerDataSize :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON LegacyParticleLayerData where
  toJSON (LegacyParticleLayerData emitterType particleCount lifetime speed spread gravity color size) =
    object
      [ "emitterType" .= emitterType
      , "particleCount" .= particleCount
      , "lifetime" .= lifetime
      , "speed" .= speed
      , "spread" .= spread
      , "gravity" .= gravity
      , "color" .= color
      , "size" .= size
      ]

instance FromJSON LegacyParticleLayerData where
  parseJSON = withObject "LegacyParticleLayerData" $ \o -> do
    emitterType <- o .: "emitterType"
    particleCount <- o .: "particleCount"
    lifetime <- o .: "lifetime"
    speed <- o .: "speed"
    spread <- o .: "spread"
    gravity <- o .: "gravity"
    color <- o .: "color"
    size <- o .: "size"
    -- Validate numeric values
    if validateFinite particleCount && validateFinite lifetime &&
       validateFinite speed && validateFinite spread &&
       validateFinite gravity && validateFinite size &&
       validateNonNegative particleCount && validateNonNegative lifetime &&
       validateNonNegative size
      then return (LegacyParticleLayerData emitterType particleCount lifetime speed spread gravity color size)
      else fail "LegacyParticleLayerData: numeric values must be finite, particleCount, lifetime, and size must be non-negative"
