{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Project
Description : Core Project Types
Copyright   : (c) Lattice, 2026
License     : MIT

Defines the root project structure, compositions, layers, and core types.
Layer-specific data is in LayerData module.

Source: ui/src/types/project.ts (2203 lines - split across modules)
-}

module Lattice.Project
  ( -- * Layer Type
    LayerType(..)
    -- * Blend Mode
  , BlendMode(..)
    -- * Track Matte
  , TrackMatteMode(..)
    -- * Composition Settings
  , CompositionSettings(..)
    -- * Project Metadata
  , ProjectMeta(..)
    -- * Motion Blur
  , MotionBlurSettings(..)
    -- * Layer Transform
  , LayerTransform2D(..)
  , LayerTransform3D(..)
    -- * Layer Base
  , LayerBase(..)
    -- * Vectors and Geometry
  , Vec3(..)
  , mkVec3
  , Point(..)
  , BoundingBox(..)
    -- * Composition
  , Composition(..)
    -- * Assets
  , AssetType(..)
  , AssetMeta(..)
    -- * Project
  , LatticeProject(..)
    -- * Export
  , MatteExportMode(..)
  , ExportOptions(..)
    -- * Color Gradient
  , GradientStop(..)
    -- * Extracted Texture
  , ExtractionMethod(..)
  , PBRTextures(..)
  , ExtractedTexture(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives hiding (Vec2(..), Vec3(..))

--------------------------------------------------------------------------------
-- Layer Type
--------------------------------------------------------------------------------

data LayerType
  = LTImage
  | LTVideo
  | LTSolid
  | LTText
  | LTShape
  | LTNull
  | LTCamera
  | LTLight
  | LTAudio
  | LTParticle
  | LTAdjustment
  | LTPreComp
  | LTGroup
  | LTNestedComp
  | LTDepth
  | LTNormal
  | LTGenerated
  | LTMatte
  | LTControl
  | LTSpline
  | LTPath
  | LTPose
  | LTEffect
  | LTModel
  | LTPointCloud
  | LTDepthflow
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Blend Mode
--------------------------------------------------------------------------------

data BlendMode
  = BMNormal
  | BMMultiply
  | BMScreen
  | BMOverlay
  | BMDarken
  | BMLighten
  | BMColorDodge
  | BMColorBurn
  | BMHardLight
  | BMSoftLight
  | BMDifference
  | BMExclusion
  | BMHue
  | BMSaturation
  | BMColor
  | BMLuminosity
  | BMAdd
  | BMSubtract
  | BMDivide
  | BMLinearBurn
  | BMLinearDodge
  | BMVividLight
  | BMLinearLight
  | BMPinLight
  | BMHardMix
  | BMDissolve
  | BMDarker
  | BMLighter
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Track Matte Mode
--------------------------------------------------------------------------------

data TrackMatteMode
  = TMNone
  | TMAlpha
  | TMAlphaInverted
  | TMLuma
  | TMLumaInverted
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Composition Settings
--------------------------------------------------------------------------------

data CompositionSettings = CompositionSettings
  { csWidth              :: !Int  -- Must be > 0 and divisible by 8
  , csHeight             :: !Int  -- Must be > 0 and divisible by 8
  , csFrameCount         :: !Int
  , csFps                :: !PositiveFloat
  , csDuration           :: !NonNegativeFloat
  , csBackgroundColor    :: !HexColor
  , csAutoResizeToContent :: !Bool
  , csFrameBlendingEnabled :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Project Metadata
--------------------------------------------------------------------------------

data ProjectMeta = ProjectMeta
  { pmName        :: !Text
  , pmCreated     :: !NonEmptyString  -- ISO timestamp
  , pmModified    :: !NonEmptyString  -- ISO timestamp
  , pmAuthor      :: !(Maybe Text)
  , pmDescription :: !(Maybe Text)
  , pmTags        :: !(Vector Text)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Motion Blur Settings
--------------------------------------------------------------------------------

data MotionBlurSettings = MotionBlurSettings
  { mbEnabled          :: !Bool
  , mbSamplesPerFrame  :: !Int  -- > 0 when enabled
  , mbShutterAngle     :: !FiniteFloat  -- 0-720
  , mbShutterPhase     :: !FiniteFloat
  , mbAdaptiveSampling :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Layer Transform
--------------------------------------------------------------------------------

data LayerTransform2D = LayerTransform2D
  { lt2dAnchorX   :: !FiniteFloat
  , lt2dAnchorY   :: !FiniteFloat
  , lt2dPositionX :: !FiniteFloat
  , lt2dPositionY :: !FiniteFloat
  , lt2dScaleX    :: !FiniteFloat
  , lt2dScaleY    :: !FiniteFloat
  , lt2dRotation  :: !FiniteFloat
  , lt2dOpacity   :: !Percentage  -- 0-100
  } deriving stock (Eq, Show, Generic)

data LayerTransform3D = LayerTransform3D
  { lt3dBase        :: !LayerTransform2D
  , lt3dPositionZ   :: !FiniteFloat
  , lt3dAnchorZ     :: !FiniteFloat
  , lt3dScaleZ      :: !FiniteFloat
  , lt3dRotationX   :: !FiniteFloat
  , lt3dRotationY   :: !FiniteFloat
  , lt3dRotationZ   :: !FiniteFloat
  , lt3dOrientation :: !(Maybe (FiniteFloat, FiniteFloat, FiniteFloat))
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Layer Base
--------------------------------------------------------------------------------

data LayerBase = LayerBase
  { lbId                   :: !NonEmptyString
  , lbName                 :: !NonEmptyString
  , lbLayerType            :: !LayerType
  , lbVisible              :: !Bool
  , lbLocked               :: !Bool
  , lbSolo                 :: !Bool
  , lbShy                  :: !Bool
  , lbEnabled              :: !Bool
  , lbSelected             :: !Bool
  , lbCollapsed            :: !Bool
  , lbGuideLayer           :: !Bool
  , lbIs3D                 :: !Bool
  , lbBlendMode            :: !BlendMode
  , lbOpacity              :: !Percentage  -- 0-100
  , lbStartFrame           :: !FrameNumber
  , lbEndFrame             :: !FrameNumber
  , lbInPoint              :: !FrameNumber
  , lbOutPoint             :: !FrameNumber
  , lbStretch              :: !PositiveFloat
  , lbParentId             :: !(Maybe NonEmptyString)
  , lbTrackMatteMode       :: !TrackMatteMode
  , lbTrackMatteLayerId    :: !(Maybe NonEmptyString)
  , lbMotionBlur           :: !Bool
  , lbQualitySetting       :: !(Maybe NonEmptyString)
  , lbSamplingQuality      :: !(Maybe NonEmptyString)
  , lbPreserveTransparency :: !Bool
  , lbFrameBlending        :: !Bool
  , lbTimeRemapEnabled     :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Vec3
--------------------------------------------------------------------------------

data Vec3 = Vec3
  { v3x :: !FiniteFloat
  , v3y :: !FiniteFloat
  , v3z :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

-- | Create Vec3 from raw doubles (validates finiteness)
mkVec3 :: Double -> Double -> Double -> Maybe Vec3
mkVec3 x y z = do
  fx <- mkFiniteFloat x
  fy <- mkFiniteFloat y
  fz <- mkFiniteFloat z
  pure $ Vec3 fx fy fz

--------------------------------------------------------------------------------
-- Point and BoundingBox
--------------------------------------------------------------------------------

data Point = Point
  { ptX :: !FiniteFloat
  , ptY :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data BoundingBox = BoundingBox
  { bbX      :: !FiniteFloat
  , bbY      :: !FiniteFloat
  , bbWidth  :: !PositiveFloat
  , bbHeight :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Composition
--------------------------------------------------------------------------------

data Composition = Composition
  { compId           :: !NonEmptyString
  , compName         :: !NonEmptyString
  , compSettings     :: !CompositionSettings
  , compLayers       :: !(Vector LayerBase)
  , compCurrentFrame :: !FrameNumber
  , compIsNestedComp :: !Bool
  , compParentCompId :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Asset Type and Metadata
--------------------------------------------------------------------------------

data AssetType
  = ATImage
  | ATVideo
  | ATAudio
  | ATFont
  | ATModel
  | ATPointCloud
  | ATData
  | ATLottie
  | ATSVG
  deriving stock (Eq, Show, Generic)

data AssetMeta = AssetMeta
  { amId         :: !NonEmptyString
  , amName       :: !NonEmptyString
  , amAssetType  :: !AssetType
  , amPath       :: !(Maybe Text)
  , amMimeType   :: !(Maybe NonEmptyString)
  , amFileSize   :: !(Maybe Int)
  , amWidth      :: !(Maybe Int)
  , amHeight     :: !(Maybe Int)
  , amDuration   :: !(Maybe FiniteFloat)
  , amFrameCount :: !(Maybe Int)
  , amFps        :: !(Maybe PositiveFloat)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Lattice Project
--------------------------------------------------------------------------------

data LatticeProject = LatticeProject
  { lpVersion           :: !NonEmptyString
  , lpSchemaVersion     :: !Int  -- >= 1
  , lpMeta              :: !ProjectMeta
  , lpCompositions      :: !(Vector Composition)
  , lpMainCompositionId :: !NonEmptyString
  , lpAssets            :: !(Vector AssetMeta)
  , lpCurrentFrame      :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Export Options
--------------------------------------------------------------------------------

data MatteExportMode = MEMExcludeText | MEMIncludeAll
  deriving stock (Eq, Show, Generic)

data ExportOptions = ExportOptions
  { eoFormat    :: !NonEmptyString
  , eoMatteMode :: !MatteExportMode
  , eoWidth     :: !Int  -- > 0
  , eoHeight    :: !Int  -- > 0
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Color Gradient
--------------------------------------------------------------------------------

data GradientStop = GradientStop
  { gsPosition :: !UnitFloat  -- 0-1
  , gsColor    :: !HexColor
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Extracted Texture
--------------------------------------------------------------------------------

data ExtractionMethod = EMMatSeg | EMManual | EMSDXL
  deriving stock (Eq, Show, Generic)

data PBRTextures = PBRTextures
  { pbrRoughness :: !NonEmptyString  -- Base64 PNG
  , pbrMetallic  :: !NonEmptyString
  , pbrNormal    :: !NonEmptyString
  , pbrHeight    :: !NonEmptyString
  , pbrAO        :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data ExtractedTexture = ExtractedTexture
  { etId               :: !NonEmptyString
  , etSourceAssetId    :: !NonEmptyString
  , etRegion           :: !BoundingBox
  , etAlbedo           :: !NonEmptyString  -- Base64 PNG
  , etPbr              :: !PBRTextures
  , etExtractionMethod :: !ExtractionMethod
  , etSeamless         :: !Bool
  , etResolutionWidth  :: !Int  -- > 0
  , etResolutionHeight :: !Int  -- > 0
  } deriving stock (Eq, Show, Generic)
