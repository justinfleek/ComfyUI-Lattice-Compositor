-- | Lattice.LayerData - Layer-specific data interfaces
-- |
-- | Source: ui/src/types/layerData.ts (565 lines)
-- |
-- | Each layer type has its own data structure defining type-specific properties.

module Lattice.LayerData
  ( ImageFit(..)
  , ImageSourceType(..)
  , CropRect
  , ImageLayerData
  , DepthVisualizationMode(..)
  , DepthColorMap(..)
  , DepthLayerData
  , NormalVisualizationMode(..)
  , NormalMapFormat(..)
  , NormalLayerData
  , AudioLayerData
  , FrameBlendingMode(..)
  , TimewarpMethod(..)
  , VideoData
  , NestedCompData
  , GeneratedMapType(..)
  , GenerationStatus(..)
  , GenerationType(..)
  , GeneratedLayerData
  , MatteType(..)
  , MattePreviewMode(..)
  , MatteLayerData
  , ControlIconShape(..)
  , ControlLayerData
  , SolidLayerData
  , GroupLayerData
  , EffectLayerData
  , ModelInstanceData
  , ModelLayerData
  , PointCloudColorMode(..)
  , PointCloudLayerData
  , PoseFormat(..)
  , PoseKeypoint
  , PoseLayerData
  , openposeConnections
  , createDefaultPoseKeypoints
  , LightType(..)
  , FalloffType(..)
  , LightLayerData
  , NullLayerData
  , createDefaultEffectLayerData
  , createDefaultSolidLayerData
  , createDefaultNullLayerData
  , createDefaultLightLayerData
  , createDefaultPoseLayerData
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives
import Lattice.DataAsset (JSONValue)

-- ────────────────────────────────────────────────────────────────────────────
-- Image Layer
-- ────────────────────────────────────────────────────────────────────────────

data ImageFit = FitNone | FitContain | FitCover | FitFill

derive instance Eq ImageFit
derive instance Generic ImageFit _
instance Show ImageFit where show = genericShow

data ImageSourceType = ISFile | ISGenerated | ISSegmented | ISInline

derive instance Eq ImageSourceType
derive instance Generic ImageSourceType _
instance Show ImageSourceType where show = genericShow

type CropRect =
  { x      :: FiniteFloat
  , y      :: FiniteFloat
  , width  :: PositiveFloat
  , height :: PositiveFloat
  }

type ImageLayerData =
  { assetId           :: String
  , source            :: String
  , fit               :: ImageFit
  , cropEnabled       :: Boolean
  , cropRect          :: CropRect
  , sourceType        :: ImageSourceType
  , segmentationMaskId :: String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Depth Layer
-- ────────────────────────────────────────────────────────────────────────────

data DepthVisualizationMode
  = DVMGrayscale | DVMColormap | DVMContour | DVMMesh3D

derive instance Eq DepthVisualizationMode
derive instance Generic DepthVisualizationMode _
instance Show DepthVisualizationMode where show = genericShow

data DepthColorMap
  = DCMTurbo | DCMViridis | DCMPlasma | DCMInferno | DCMMagma | DCMGrayscale

derive instance Eq DepthColorMap
derive instance Generic DepthColorMap _
instance Show DepthColorMap where show = genericShow

type DepthLayerData =
  { assetId                  :: Maybe NonEmptyString
  , visualizationMode        :: DepthVisualizationMode
  , colorMap                 :: DepthColorMap
  , invert                   :: Boolean
  , minDepth                 :: FiniteFloat
  , maxDepth                 :: FiniteFloat
  , autoNormalize            :: Boolean
  , contourLevels            :: Int
  , contourColor             :: HexColor
  , contourWidth             :: PositiveFloat
  , meshDisplacementPropId   :: NonEmptyString
  , meshResolution           :: Int  -- > 0
  , wireframe                :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Normal Layer
-- ────────────────────────────────────────────────────────────────────────────

data NormalVisualizationMode
  = NVMRgb | NVMHemisphere | NVMArrows | NVMLit

derive instance Eq NormalVisualizationMode
derive instance Generic NormalVisualizationMode _
instance Show NormalVisualizationMode where show = genericShow

data NormalMapFormat = NMFOpenGL | NMFDirectX

derive instance Eq NormalMapFormat
derive instance Generic NormalMapFormat _
instance Show NormalMapFormat where show = genericShow

type NormalLayerData =
  { assetId            :: Maybe NonEmptyString
  , visualizationMode  :: NormalVisualizationMode
  , format             :: NormalMapFormat
  , flipX              :: Boolean
  , flipY              :: Boolean
  , flipZ              :: Boolean
  , arrowDensity       :: PositiveFloat
  , arrowScale         :: PositiveFloat
  , arrowColor         :: HexColor
  , lightDirX          :: FiniteFloat
  , lightDirY          :: FiniteFloat
  , lightDirZ          :: FiniteFloat
  , lightIntensity     :: NonNegativeFloat
  , ambientIntensity   :: NonNegativeFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Audio Layer
-- ────────────────────────────────────────────────────────────────────────────

type AudioLayerData =
  { assetId        :: Maybe NonEmptyString
  , levelPropId    :: NonEmptyString
  , muted          :: Boolean
  , solo           :: Boolean
  , panPropId      :: NonEmptyString
  , startTime      :: NonNegativeFloat
  , loop           :: Boolean
  , speed          :: PositiveFloat
  , showWaveform   :: Boolean
  , waveformColor  :: HexColor
  , exposeFeatures :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Video Data
-- ────────────────────────────────────────────────────────────────────────────

data FrameBlendingMode = FBMNone | FBMFrameMix | FBMPixelMotion

derive instance Eq FrameBlendingMode
derive instance Generic FrameBlendingMode _
instance Show FrameBlendingMode where show = genericShow

data TimewarpMethod = TWMWholeFrames | TWMFrameMix | TWMPixelMotion

derive instance Eq TimewarpMethod
derive instance Generic TimewarpMethod _
instance Show TimewarpMethod where show = genericShow

type VideoData =
  { assetId             :: Maybe NonEmptyString
  , loop                :: Boolean
  , pingPong            :: Boolean
  , startTime           :: NonNegativeFloat
  , endTime             :: Maybe FiniteFloat
  , speed               :: PositiveFloat
  , speedMapEnabled     :: Boolean
  , speedMapPropId      :: Maybe NonEmptyString
  , timewarpEnabled     :: Boolean
  , timewarpSpeedPropId :: Maybe NonEmptyString
  , timewarpMethod      :: Maybe TimewarpMethod
  , frameBlending       :: FrameBlendingMode
  , audioEnabled        :: Boolean
  , audioLevel          :: Percentage
  , posterFrame         :: FrameNumber
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Nested Comp Data
-- ────────────────────────────────────────────────────────────────────────────

type NestedCompData =
  { compositionId        :: NonEmptyString
  , speedMapEnabled      :: Boolean
  , speedMapPropId       :: Maybe NonEmptyString
  , timewarpEnabled      :: Boolean
  , timewarpSpeedPropId  :: Maybe NonEmptyString
  , timewarpMethod       :: Maybe TimewarpMethod
  , flattenTransform     :: Boolean
  , overrideFrameRate    :: Boolean
  , frameRate            :: Maybe PositiveFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Generated Layer
-- ────────────────────────────────────────────────────────────────────────────

data GeneratedMapType
  = GMTDepth | GMTNormal | GMTEdge | GMTPose | GMTSegment | GMTLineart | GMTSoftedge

derive instance Eq GeneratedMapType
derive instance Generic GeneratedMapType _
instance Show GeneratedMapType where show = genericShow

data GenerationStatus
  = GSPending | GSGenerating | GSComplete | GSError

derive instance Eq GenerationStatus
derive instance Generic GenerationStatus _
instance Show GenerationStatus where show = genericShow

data GenerationType
  = GTDepth | GTNormal | GTEdge | GTSegment | GTInpaint | GTCustom

derive instance Eq GenerationType
derive instance Generic GenerationType _
instance Show GenerationType where show = genericShow

type GeneratedLayerData =
  { generationType    :: GenerationType
  , sourceLayerId     :: Maybe NonEmptyString
  , model             :: NonEmptyString
  , parameters        :: Array { key :: String, value :: JSONValue }
  , generatedAssetId  :: Maybe NonEmptyString
  , status            :: GenerationStatus
  , errorMessage      :: Maybe String
  , autoRegenerate    :: Boolean
  , lastGenerated     :: Maybe NonEmptyString
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Matte Layer
-- ────────────────────────────────────────────────────────────────────────────

data MatteType
  = MTLuminance | MTAlpha | MTRed | MTGreen | MTBlue | MTHue | MTSaturation

derive instance Eq MatteType
derive instance Generic MatteType _
instance Show MatteType where show = genericShow

data MattePreviewMode = MPMMatte | MPMComposite | MPMOverlay

derive instance Eq MattePreviewMode
derive instance Generic MattePreviewMode _
instance Show MattePreviewMode where show = genericShow

type MatteLayerData =
  { matteType     :: MatteType
  , invert        :: Boolean
  , threshold     :: UnitFloat
  , feather       :: NonNegativeFloat
  , expansion     :: FiniteFloat
  , sourceLayerId :: Maybe NonEmptyString
  , previewMode   :: MattePreviewMode
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Control Layer
-- ────────────────────────────────────────────────────────────────────────────

data ControlIconShape = CISCrosshair | CISDiamond | CISCircle | CISSquare

derive instance Eq ControlIconShape
derive instance Generic ControlIconShape _
instance Show ControlIconShape where show = genericShow

type ControlLayerData =
  { size      :: PositiveFloat
  , showAxes  :: Boolean
  , showIcon  :: Boolean
  , iconShape :: ControlIconShape
  , iconColor :: HexColor
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Solid Layer
-- ────────────────────────────────────────────────────────────────────────────

type SolidLayerData =
  { color         :: HexColor
  , width         :: Int  -- > 0
  , height        :: Int  -- > 0
  , shadowCatcher :: Boolean
  , shadowOpacity :: Maybe UnitFloat
  , shadowColor   :: Maybe HexColor
  , receiveShadow :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Group Layer
-- ────────────────────────────────────────────────────────────────────────────

type GroupLayerData =
  { collapsed   :: Boolean
  , color       :: Maybe HexColor
  , passThrough :: Boolean
  , isolate     :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Effect Layer
-- ────────────────────────────────────────────────────────────────────────────

type EffectLayerData =
  { effectLayer     :: Boolean
  , adjustmentLayer :: Boolean  -- Deprecated
  , color           :: HexColor
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Model Layer
-- ────────────────────────────────────────────────────────────────────────────

type ModelInstanceData =
  { posX   :: FiniteFloat
  , posY   :: FiniteFloat
  , posZ   :: FiniteFloat
  , rotX   :: FiniteFloat
  , rotY   :: FiniteFloat
  , rotZ   :: FiniteFloat
  , scaleX :: FiniteFloat
  , scaleY :: FiniteFloat
  , scaleZ :: FiniteFloat
  , color  :: Maybe HexColor
  }

type ModelLayerData =
  { assetId                :: Maybe NonEmptyString
  , animationClip          :: Maybe NonEmptyString
  , animationSpeed         :: FiniteFloat
  , animationLoop          :: Boolean
  , animationTimePropId    :: NonEmptyString
  , matAlbedoAssetId       :: Maybe NonEmptyString
  , matNormalAssetId       :: Maybe NonEmptyString
  , matRoughnessAssetId    :: Maybe NonEmptyString
  , matMetalnessAssetId    :: Maybe NonEmptyString
  , matEmissiveAssetId     :: Maybe NonEmptyString
  , matEmissiveIntensity   :: Maybe NonNegativeFloat
  , castShadows            :: Boolean
  , receiveShadows         :: Boolean
  , wireframe              :: Boolean
  , lodBias                :: FiniteFloat
  , instanceCount          :: Maybe Int
  , instanceData           :: Array ModelInstanceData
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Point Cloud Layer
-- ────────────────────────────────────────────────────────────────────────────

data PointCloudColorMode = PCCMVertex | PCCMHeight | PCCMIntensity | PCCMSolid

derive instance Eq PointCloudColorMode
derive instance Generic PointCloudColorMode _
instance Show PointCloudColorMode where show = genericShow

type PointCloudLayerData =
  { assetId         :: Maybe NonEmptyString
  , pointSizePropId :: NonEmptyString
  , sizeAttenuation :: Boolean
  , colorMode       :: PointCloudColorMode
  , solidColor      :: Maybe HexColor
  , heightColormap  :: Maybe DepthColorMap
  , heightMin       :: Maybe FiniteFloat
  , heightMax       :: Maybe FiniteFloat
  , intensityMin    :: Maybe FiniteFloat
  , intensityMax    :: Maybe FiniteFloat
  , decimation      :: Int  -- > 0
  , clipEnabled     :: Boolean
  , clipMinX        :: Maybe FiniteFloat
  , clipMaxX        :: Maybe FiniteFloat
  , clipMinY        :: Maybe FiniteFloat
  , clipMaxY        :: Maybe FiniteFloat
  , clipMinZ        :: Maybe FiniteFloat
  , clipMaxZ        :: Maybe FiniteFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Pose Layer
-- ────────────────────────────────────────────────────────────────────────────

data PoseFormat = PFOpenpose | PFCoco | PFDwpose

derive instance Eq PoseFormat
derive instance Generic PoseFormat _
instance Show PoseFormat where show = genericShow

type PoseKeypoint =
  { x          :: UnitFloat      -- Normalized 0-1
  , y          :: UnitFloat      -- Normalized 0-1
  , confidence :: UnitFloat      -- 0-1
  }

type PoseLayerData =
  { keypoints      :: Array PoseKeypoint
  , format         :: PoseFormat
  , lineWidth      :: PositiveFloat
  , jointRadius    :: PositiveFloat
  , lineColor      :: HexColor
  , jointColor     :: HexColor
  , showConfidence :: Boolean
  , mirror         :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- OpenPose Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | OpenPose skeleton connections
openposeConnections :: Array (Tuple Int Int)
openposeConnections =
  [ Tuple 0 1, Tuple 1 2, Tuple 2 3, Tuple 3 4, Tuple 1 5, Tuple 5 6, Tuple 6 7
  , Tuple 1 8, Tuple 8 9, Tuple 9 10, Tuple 1 11, Tuple 11 12, Tuple 12 13
  , Tuple 0 14, Tuple 14 16, Tuple 0 15, Tuple 15 17
  ]

-- ────────────────────────────────────────────────────────────────────────────
-- Factory Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Create default pose keypoints in OpenPose T-pose (18 keypoints)
createDefaultPoseKeypoints :: Array PoseKeypoint
createDefaultPoseKeypoints =
  [ kp 0.5 0.1       -- 0: nose
  , kp 0.5 0.2       -- 1: neck
  , kp 0.35 0.25     -- 2: right_shoulder
  , kp 0.2 0.25      -- 3: right_elbow
  , kp 0.05 0.25     -- 4: right_wrist
  , kp 0.65 0.25     -- 5: left_shoulder
  , kp 0.8 0.25      -- 6: left_elbow
  , kp 0.95 0.25     -- 7: left_wrist
  , kp 0.4 0.5       -- 8: right_hip
  , kp 0.4 0.7       -- 9: right_knee
  , kp 0.4 0.85      -- 10: right_ankle
  , kp 0.6 0.5       -- 11: left_hip
  , kp 0.6 0.7       -- 12: left_knee
  , kp 0.6 0.85      -- 13: left_ankle
  , kp 0.45 0.08     -- 14: right_eye
  , kp 0.55 0.08     -- 15: left_eye
  , kp 0.4 0.1       -- 16: right_ear
  , kp 0.6 0.1       -- 17: left_ear
  ]
  where
    kp :: Number -> Number -> PoseKeypoint
    kp x y =
      { x: uf x, y: uf y, confidence: uf 1.0 }
    uf :: Number -> UnitFloat
    uf n = case mkUnitFloat n of
      Just v -> v
      Nothing -> UnitFloat 0.0

-- ────────────────────────────────────────────────────────────────────────────
-- Light Layer
-- ────────────────────────────────────────────────────────────────────────────

data LightType = LightPoint | LightSpot | LightAmbient | LightParallel

derive instance Eq LightType
derive instance Generic LightType _
instance Show LightType where show = genericShow

data FalloffType = FONone | FOSmooth | FOInverseSquare

derive instance Eq FalloffType
derive instance Generic FalloffType _
instance Show FalloffType where show = genericShow

type LightLayerData =
  { lightType       :: LightType
  , color           :: HexColor
  , intensity       :: Percentage
  , radius          :: PositiveFloat
  , falloff         :: FalloffType
  , falloffDistance :: PositiveFloat
  , castShadows     :: Boolean
  , shadowDarkness  :: Percentage
  , shadowDiffusion :: NonNegativeFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Null Layer
-- ────────────────────────────────────────────────────────────────────────────

type NullLayerData =
  { size :: Int  -- Visual size of null icon in editor
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Additional Factory Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Create default effect layer data
createDefaultEffectLayerData :: EffectLayerData
createDefaultEffectLayerData =
  { effectLayer: true
  , adjustmentLayer: true
  , color: hex "#FF6B6B"
  }
  where
    hex s = case mkHexColor s of
      Just v -> v
      Nothing -> HexColor "#000000"

-- | Create default solid layer data
createDefaultSolidLayerData :: Int -> Int -> SolidLayerData
createDefaultSolidLayerData w h =
  { color: hex "#808080"
  , width: w
  , height: h
  , shadowCatcher: false
  , shadowOpacity: Nothing
  , shadowColor: Nothing
  , receiveShadow: false
  }
  where
    hex s = case mkHexColor s of
      Just v -> v
      Nothing -> HexColor "#000000"

-- | Create default null layer data
createDefaultNullLayerData :: NullLayerData
createDefaultNullLayerData =
  { size: 40
  }

-- | Create default light layer data
createDefaultLightLayerData :: LightLayerData
createDefaultLightLayerData =
  { lightType: LightPoint
  , color: hex "#ffffff"
  , intensity: pct 100.0
  , radius: pf 500.0
  , falloff: FONone
  , falloffDistance: pf 500.0
  , castShadows: false
  , shadowDarkness: pct 100.0
  , shadowDiffusion: nnf 0.0
  }
  where
    hex s = case mkHexColor s of
      Just v -> v
      Nothing -> HexColor "#000000"
    pct n = case mkPercentage n of
      Just v -> v
      Nothing -> Percentage 0.0
    pf n = case mkPositiveFloat n of
      Just v -> v
      Nothing -> PositiveFloat 1.0
    nnf n = case mkNonNegativeFloat n of
      Just v -> v
      Nothing -> NonNegativeFloat 0.0

-- | Create default pose layer data
createDefaultPoseLayerData :: PoseLayerData
createDefaultPoseLayerData =
  { keypoints: createDefaultPoseKeypoints
  , format: PFCoco
  , lineWidth: pf 4.0
  , jointRadius: pf 4.0
  , lineColor: hex "#FFFFFF"
  , jointColor: hex "#FF0000"
  , showConfidence: false
  , mirror: false
  }
  where
    hex s = case mkHexColor s of
      Just v -> v
      Nothing -> HexColor "#000000"
    pf n = case mkPositiveFloat n of
      Just v -> v
      Nothing -> PositiveFloat 1.0
