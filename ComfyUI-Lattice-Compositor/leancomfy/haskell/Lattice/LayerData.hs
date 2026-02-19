{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.LayerData
Description : Layer-specific data interfaces
Copyright   : (c) Lattice, 2026
License     : MIT

Each layer type has its own data structure defining type-specific properties.

Source: ui/src/types/layerData.ts (565 lines)
-}

module Lattice.LayerData
  ( -- * Image Layer
    ImageFit(..)
  , ImageSourceType(..)
  , CropRect(..)
  , ImageLayerData(..)
    -- * Depth Layer
  , DepthVisualizationMode(..)
  , DepthColorMap(..)
  , DepthLayerData(..)
    -- * Normal Layer
  , NormalVisualizationMode(..)
  , NormalMapFormat(..)
  , NormalLayerData(..)
    -- * Audio Layer
  , AudioLayerData(..)
    -- * Video Data
  , FrameBlendingMode(..)
  , TimewarpMethod(..)
  , VideoData(..)
    -- * Nested Comp
  , NestedCompData(..)
    -- * Generated Layer
  , GeneratedMapType(..)
  , GenerationStatus(..)
  , GenerationType(..)
  , GeneratedLayerData(..)
    -- * Matte Layer
  , MatteType(..)
  , MattePreviewMode(..)
  , MatteLayerData(..)
    -- * Control Layer
  , ControlIconShape(..)
  , ControlLayerData(..)
    -- * Solid Layer
  , SolidLayerData(..)
    -- * Group Layer
  , GroupLayerData(..)
    -- * Effect Layer
  , EffectLayerData(..)
    -- * Model Layer
  , ModelInstanceData(..)
  , ModelLayerData(..)
    -- * Point Cloud Layer
  , PointCloudColorMode(..)
  , PointCloudLayerData(..)
    -- * Pose Layer
  , PoseFormat(..)
  , PoseKeypoint(..)
  , PoseLayerData(..)
    -- * OpenPose Constants
  , openposeConnections
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Lattice.Primitives
import Lattice.DataAsset (JSONValue)

--------------------------------------------------------------------------------
-- Image Layer
--------------------------------------------------------------------------------

data ImageFit = FitNone | FitContain | FitCover | FitFill
  deriving stock (Eq, Show, Generic)

data ImageSourceType = ISFile | ISGenerated | ISSegmented | ISInline
  deriving stock (Eq, Show, Generic)

data CropRect = CropRect
  { cropX      :: !FiniteFloat
  , cropY      :: !FiniteFloat
  , cropWidth  :: !PositiveFloat
  , cropHeight :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

data ImageLayerData = ImageLayerData
  { imgAssetId           :: !Text
  , imgSource            :: !Text
  , imgFit               :: !ImageFit
  , imgCropEnabled       :: !Bool
  , imgCropRect          :: !CropRect
  , imgSourceType        :: !ImageSourceType
  , imgSegmentationMaskId :: !Text
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Depth Layer
--------------------------------------------------------------------------------

data DepthVisualizationMode
  = DVMGrayscale | DVMColormap | DVMContour | DVMMesh3D
  deriving stock (Eq, Show, Generic)

data DepthColorMap
  = DCMTurbo | DCMViridis | DCMPlasma | DCMInferno | DCMMagma | DCMGrayscale
  deriving stock (Eq, Show, Generic)

data DepthLayerData = DepthLayerData
  { depthAssetId                  :: !(Maybe NonEmptyString)
  , depthVisualizationMode        :: !DepthVisualizationMode
  , depthColorMap                 :: !DepthColorMap
  , depthInvert                   :: !Bool
  , depthMinDepth                 :: !FiniteFloat
  , depthMaxDepth                 :: !FiniteFloat
  , depthAutoNormalize            :: !Bool
  , depthContourLevels            :: !Int
  , depthContourColor             :: !HexColor
  , depthContourWidth             :: !PositiveFloat
  , depthMeshDisplacementPropId   :: !NonEmptyString
  , depthMeshResolution           :: !Int  -- > 0
  , depthWireframe                :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Normal Layer
--------------------------------------------------------------------------------

data NormalVisualizationMode
  = NVMRgb | NVMHemisphere | NVMArrows | NVMLit
  deriving stock (Eq, Show, Generic)

data NormalMapFormat = NMFOpenGL | NMFDirectX
  deriving stock (Eq, Show, Generic)

data NormalLayerData = NormalLayerData
  { normalAssetId            :: !(Maybe NonEmptyString)
  , normalVisualizationMode  :: !NormalVisualizationMode
  , normalFormat             :: !NormalMapFormat
  , normalFlipX              :: !Bool
  , normalFlipY              :: !Bool
  , normalFlipZ              :: !Bool
  , normalArrowDensity       :: !PositiveFloat
  , normalArrowScale         :: !PositiveFloat
  , normalArrowColor         :: !HexColor
  , normalLightDirX          :: !FiniteFloat
  , normalLightDirY          :: !FiniteFloat
  , normalLightDirZ          :: !FiniteFloat
  , normalLightIntensity     :: !NonNegativeFloat
  , normalAmbientIntensity   :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Audio Layer
--------------------------------------------------------------------------------

data AudioLayerData = AudioLayerData
  { audioAssetId        :: !(Maybe NonEmptyString)
  , audioLevelPropId    :: !NonEmptyString
  , audioMuted          :: !Bool
  , audioSolo           :: !Bool
  , audioPanPropId      :: !NonEmptyString
  , audioStartTime      :: !NonNegativeFloat
  , audioLoop           :: !Bool
  , audioSpeed          :: !PositiveFloat
  , audioShowWaveform   :: !Bool
  , audioWaveformColor  :: !HexColor
  , audioExposeFeatures :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Video Data
--------------------------------------------------------------------------------

data FrameBlendingMode = FBMNone | FBMFrameMix | FBMPixelMotion
  deriving stock (Eq, Show, Generic)

data TimewarpMethod = TWMWholeFrames | TWMFrameMix | TWMPixelMotion
  deriving stock (Eq, Show, Generic)

data VideoData = VideoData
  { videoAssetId             :: !(Maybe NonEmptyString)
  , videoLoop                :: !Bool
  , videoPingPong            :: !Bool
  , videoStartTime           :: !NonNegativeFloat
  , videoEndTime             :: !(Maybe FiniteFloat)
  , videoSpeed               :: !PositiveFloat
  , videoSpeedMapEnabled     :: !Bool
  , videoSpeedMapPropId      :: !(Maybe NonEmptyString)
  , videoTimewarpEnabled     :: !Bool
  , videoTimewarpSpeedPropId :: !(Maybe NonEmptyString)
  , videoTimewarpMethod      :: !(Maybe TimewarpMethod)
  , videoFrameBlending       :: !FrameBlendingMode
  , videoAudioEnabled        :: !Bool
  , videoAudioLevel          :: !Percentage
  , videoPosterFrame         :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Nested Comp Data
--------------------------------------------------------------------------------

data NestedCompData = NestedCompData
  { nestedCompId              :: !NonEmptyString
  , nestedSpeedMapEnabled     :: !Bool
  , nestedSpeedMapPropId      :: !(Maybe NonEmptyString)
  , nestedTimewarpEnabled     :: !Bool
  , nestedTimewarpSpeedPropId :: !(Maybe NonEmptyString)
  , nestedTimewarpMethod      :: !(Maybe TimewarpMethod)
  , nestedFlattenTransform    :: !Bool
  , nestedOverrideFrameRate   :: !Bool
  , nestedFrameRate           :: !(Maybe PositiveFloat)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Generated Layer
--------------------------------------------------------------------------------

data GeneratedMapType
  = GMTDepth | GMTNormal | GMTEdge | GMTPose | GMTSegment | GMTLineart | GMTSoftedge
  deriving stock (Eq, Show, Generic)

data GenerationStatus
  = GSPending | GSGenerating | GSComplete | GSError
  deriving stock (Eq, Show, Generic)

data GenerationType
  = GTDepth | GTNormal | GTEdge | GTSegment | GTInpaint | GTCustom
  deriving stock (Eq, Show, Generic)

data GeneratedLayerData = GeneratedLayerData
  { genType            :: !GenerationType
  , genSourceLayerId   :: !(Maybe NonEmptyString)
  , genModel           :: !NonEmptyString
  , genParameters      :: !(Vector (Text, JSONValue))
  , genGeneratedAssetId :: !(Maybe NonEmptyString)
  , genStatus          :: !GenerationStatus
  , genErrorMessage    :: !(Maybe Text)
  , genAutoRegenerate  :: !Bool
  , genLastGenerated   :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Matte Layer
--------------------------------------------------------------------------------

data MatteType
  = MTLuminance | MTAlpha | MTRed | MTGreen | MTBlue | MTHue | MTSaturation
  deriving stock (Eq, Show, Generic)

data MattePreviewMode = MPMMatte | MPMComposite | MPMOverlay
  deriving stock (Eq, Show, Generic)

data MatteLayerData = MatteLayerData
  { matteType         :: !MatteType
  , matteInvert       :: !Bool
  , matteThreshold    :: !UnitFloat
  , matteFeather      :: !NonNegativeFloat
  , matteExpansion    :: !FiniteFloat
  , matteSourceLayerId :: !(Maybe NonEmptyString)
  , mattePreviewMode  :: !MattePreviewMode
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Control Layer
--------------------------------------------------------------------------------

data ControlIconShape = CISCrosshair | CISDiamond | CISCircle | CISSquare
  deriving stock (Eq, Show, Generic)

data ControlLayerData = ControlLayerData
  { ctrlSize      :: !PositiveFloat
  , ctrlShowAxes  :: !Bool
  , ctrlShowIcon  :: !Bool
  , ctrlIconShape :: !ControlIconShape
  , ctrlIconColor :: !HexColor
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Solid Layer
--------------------------------------------------------------------------------

data SolidLayerData = SolidLayerData
  { solidColor         :: !HexColor
  , solidWidth         :: !Int  -- > 0
  , solidHeight        :: !Int  -- > 0
  , solidShadowCatcher :: !Bool
  , solidShadowOpacity :: !(Maybe UnitFloat)
  , solidShadowColor   :: !(Maybe HexColor)
  , solidReceiveShadow :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Group Layer
--------------------------------------------------------------------------------

data GroupLayerData = GroupLayerData
  { groupCollapsed   :: !Bool
  , groupColor       :: !(Maybe HexColor)
  , groupPassThrough :: !Bool
  , groupIsolate     :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Effect Layer
--------------------------------------------------------------------------------

data EffectLayerData = EffectLayerData
  { effectLayerFlag     :: !Bool
  , effectAdjustmentFlag :: !Bool  -- Deprecated
  , effectColor         :: !HexColor
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Model Layer
--------------------------------------------------------------------------------

data ModelInstanceData = ModelInstanceData
  { instPosX   :: !FiniteFloat
  , instPosY   :: !FiniteFloat
  , instPosZ   :: !FiniteFloat
  , instRotX   :: !FiniteFloat
  , instRotY   :: !FiniteFloat
  , instRotZ   :: !FiniteFloat
  , instScaleX :: !FiniteFloat
  , instScaleY :: !FiniteFloat
  , instScaleZ :: !FiniteFloat
  , instColor  :: !(Maybe HexColor)
  } deriving stock (Eq, Show, Generic)

data ModelLayerData = ModelLayerData
  { modelAssetId                :: !(Maybe NonEmptyString)
  , modelAnimationClip          :: !(Maybe NonEmptyString)
  , modelAnimationSpeed         :: !FiniteFloat
  , modelAnimationLoop          :: !Bool
  , modelAnimationTimePropId    :: !NonEmptyString
  , modelMatAlbedoAssetId       :: !(Maybe NonEmptyString)
  , modelMatNormalAssetId       :: !(Maybe NonEmptyString)
  , modelMatRoughnessAssetId    :: !(Maybe NonEmptyString)
  , modelMatMetalnessAssetId    :: !(Maybe NonEmptyString)
  , modelMatEmissiveAssetId     :: !(Maybe NonEmptyString)
  , modelMatEmissiveIntensity   :: !(Maybe NonNegativeFloat)
  , modelCastShadows            :: !Bool
  , modelReceiveShadows         :: !Bool
  , modelWireframe              :: !Bool
  , modelLodBias                :: !FiniteFloat
  , modelInstanceCount          :: !(Maybe Int)
  , modelInstanceData           :: !(Vector ModelInstanceData)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Point Cloud Layer
--------------------------------------------------------------------------------

data PointCloudColorMode = PCCMVertex | PCCMHeight | PCCMIntensity | PCCMSolid
  deriving stock (Eq, Show, Generic)

data PointCloudLayerData = PointCloudLayerData
  { pcAssetId         :: !(Maybe NonEmptyString)
  , pcPointSizePropId :: !NonEmptyString
  , pcSizeAttenuation :: !Bool
  , pcColorMode       :: !PointCloudColorMode
  , pcSolidColor      :: !(Maybe HexColor)
  , pcHeightColormap  :: !(Maybe DepthColorMap)
  , pcHeightMin       :: !(Maybe FiniteFloat)
  , pcHeightMax       :: !(Maybe FiniteFloat)
  , pcIntensityMin    :: !(Maybe FiniteFloat)
  , pcIntensityMax    :: !(Maybe FiniteFloat)
  , pcDecimation      :: !Int  -- > 0
  , pcClipEnabled     :: !Bool
  , pcClipMinX        :: !(Maybe FiniteFloat)
  , pcClipMaxX        :: !(Maybe FiniteFloat)
  , pcClipMinY        :: !(Maybe FiniteFloat)
  , pcClipMaxY        :: !(Maybe FiniteFloat)
  , pcClipMinZ        :: !(Maybe FiniteFloat)
  , pcClipMaxZ        :: !(Maybe FiniteFloat)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Pose Layer
--------------------------------------------------------------------------------

data PoseFormat = PFOpenpose | PFCoco | PFDwpose
  deriving stock (Eq, Show, Generic)

data PoseKeypoint = PoseKeypoint
  { poseX          :: !UnitFloat      -- Normalized 0-1
  , poseY          :: !UnitFloat      -- Normalized 0-1
  , poseConfidence :: !UnitFloat      -- 0-1
  } deriving stock (Eq, Show, Generic)

data PoseLayerData = PoseLayerData
  { poseKeypoints      :: !(Vector PoseKeypoint)
  , poseFormat         :: !PoseFormat
  , poseLineWidth      :: !PositiveFloat
  , poseJointRadius    :: !PositiveFloat
  , poseLineColor      :: !HexColor
  , poseJointColor     :: !HexColor
  , poseShowConfidence :: !Bool
  , poseMirror         :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- OpenPose Constants
--------------------------------------------------------------------------------

-- | OpenPose skeleton connections
openposeConnections :: Vector (Int, Int)
openposeConnections = V.fromList
  [ (0, 1), (1, 2), (2, 3), (3, 4), (1, 5), (5, 6), (6, 7)
  , (1, 8), (8, 9), (9, 10), (1, 11), (11, 12), (12, 13)
  , (0, 14), (14, 16), (0, 15), (15, 17)
  ]
