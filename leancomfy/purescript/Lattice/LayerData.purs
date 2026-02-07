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
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives
import Lattice.DataAsset (JSONValue)

--------------------------------------------------------------------------------
-- Image Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Depth Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Normal Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Audio Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Video Data
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Nested Comp Data
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Generated Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Matte Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Control Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Solid Layer
--------------------------------------------------------------------------------

type SolidLayerData =
  { color         :: HexColor
  , width         :: Int  -- > 0
  , height        :: Int  -- > 0
  , shadowCatcher :: Boolean
  , shadowOpacity :: Maybe UnitFloat
  , shadowColor   :: Maybe HexColor
  , receiveShadow :: Boolean
  }

--------------------------------------------------------------------------------
-- Group Layer
--------------------------------------------------------------------------------

type GroupLayerData =
  { collapsed   :: Boolean
  , color       :: Maybe HexColor
  , passThrough :: Boolean
  , isolate     :: Boolean
  }

--------------------------------------------------------------------------------
-- Effect Layer
--------------------------------------------------------------------------------

type EffectLayerData =
  { effectLayer     :: Boolean
  , adjustmentLayer :: Boolean  -- Deprecated
  , color           :: HexColor
  }

--------------------------------------------------------------------------------
-- Model Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Point Cloud Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Pose Layer
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- OpenPose Constants
--------------------------------------------------------------------------------

-- | OpenPose skeleton connections
openposeConnections :: Array (Tuple Int Int)
openposeConnections =
  [ Tuple 0 1, Tuple 1 2, Tuple 2 3, Tuple 3 4, Tuple 1 5, Tuple 5 6, Tuple 6 7
  , Tuple 1 8, Tuple 8 9, Tuple 9 10, Tuple 1 11, Tuple 11 12, Tuple 12 13
  , Tuple 0 14, Tuple 14 16, Tuple 0 15, Tuple 15 17
  ]
