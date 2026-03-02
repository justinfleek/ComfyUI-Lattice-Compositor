-- | Lattice.Project - Core Project Types
-- |
-- | Source: ui/src/types/project.ts (2203 lines - split across modules)
-- |
-- | Defines the root project structure, compositions, layers, and core types.
-- | Layer-specific data is in LayerData module.

module Lattice.Project
  ( LayerType(..)
  , BlendMode(..)
  , TrackMatteMode(..)
  , CompositionSettings
  , ProjectMeta
  , MotionBlurSettings
  , LayerTransform2D
  , LayerTransform3D
  , LayerBase
  , Vec3
  , mkVec3
  , Point
  , BoundingBox
  , Composition
  , AssetType(..)
  , AssetMeta
  , LatticeProject
  , MatteExportMode(..)
  , ExportOptions
  , GradientStop
  , ExtractionMethod(..)
  , PBRTextures
  , ExtractedTexture
  , createEmptyProject
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Type
-- ────────────────────────────────────────────────────────────────────────────

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

derive instance Eq LayerType
derive instance Generic LayerType _
instance Show LayerType where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Blend Mode
-- ────────────────────────────────────────────────────────────────────────────

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

derive instance Eq BlendMode
derive instance Generic BlendMode _
instance Show BlendMode where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Track Matte Mode
-- ────────────────────────────────────────────────────────────────────────────

data TrackMatteMode
  = TMNone
  | TMAlpha
  | TMAlphaInverted
  | TMLuma
  | TMLumaInverted

derive instance Eq TrackMatteMode
derive instance Generic TrackMatteMode _
instance Show TrackMatteMode where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Composition Settings
-- ────────────────────────────────────────────────────────────────────────────

type CompositionSettings =
  { width                :: Int  -- Must be > 0 and divisible by 8
  , height               :: Int  -- Must be > 0 and divisible by 8
  , frameCount           :: Int
  , fps                  :: PositiveFloat
  , duration             :: NonNegativeFloat
  , backgroundColor      :: HexColor
  , autoResizeToContent  :: Boolean
  , frameBlendingEnabled :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Project Metadata
-- ────────────────────────────────────────────────────────────────────────────

type ProjectMeta =
  { name        :: String
  , created     :: NonEmptyString  -- ISO timestamp
  , modified    :: NonEmptyString  -- ISO timestamp
  , author      :: Maybe String
  , description :: Maybe String
  , tags        :: Array String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Blur Settings
-- ────────────────────────────────────────────────────────────────────────────

type MotionBlurSettings =
  { enabled          :: Boolean
  , samplesPerFrame  :: Int  -- > 0 when enabled
  , shutterAngle     :: FiniteFloat  -- 0-720
  , shutterPhase     :: FiniteFloat
  , adaptiveSampling :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Transform
-- ────────────────────────────────────────────────────────────────────────────

type LayerTransform2D =
  { anchorX   :: FiniteFloat
  , anchorY   :: FiniteFloat
  , positionX :: FiniteFloat
  , positionY :: FiniteFloat
  , scaleX    :: FiniteFloat
  , scaleY    :: FiniteFloat
  , rotation  :: FiniteFloat
  , opacity   :: Percentage  -- 0-100
  }

type LayerTransform3D =
  { anchorX     :: FiniteFloat
  , anchorY     :: FiniteFloat
  , anchorZ     :: FiniteFloat
  , positionX   :: FiniteFloat
  , positionY   :: FiniteFloat
  , positionZ   :: FiniteFloat
  , scaleX      :: FiniteFloat
  , scaleY      :: FiniteFloat
  , scaleZ      :: FiniteFloat
  , rotation    :: FiniteFloat
  , rotationX   :: FiniteFloat
  , rotationY   :: FiniteFloat
  , rotationZ   :: FiniteFloat
  , opacity     :: Percentage
  , orientation :: Maybe { x :: FiniteFloat, y :: FiniteFloat, z :: FiniteFloat }
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Base
-- ────────────────────────────────────────────────────────────────────────────

type LayerBase =
  { id                   :: NonEmptyString
  , name                 :: NonEmptyString
  , layerType            :: LayerType
  , visible              :: Boolean
  , locked               :: Boolean
  , solo                 :: Boolean
  , shy                  :: Boolean
  , enabled              :: Boolean
  , selected             :: Boolean
  , collapsed            :: Boolean
  , guideLayer           :: Boolean
  , is3D                 :: Boolean
  , blendMode            :: BlendMode
  , opacity              :: Percentage  -- 0-100
  , startFrame           :: FrameNumber
  , endFrame             :: FrameNumber
  , inPoint              :: FrameNumber
  , outPoint             :: FrameNumber
  , stretch              :: PositiveFloat
  , parentId             :: Maybe NonEmptyString
  , trackMatteMode       :: TrackMatteMode
  , trackMatteLayerId    :: Maybe NonEmptyString
  , motionBlur           :: Boolean
  , qualitySetting       :: Maybe NonEmptyString
  , samplingQuality      :: Maybe NonEmptyString
  , preserveTransparency :: Boolean
  , frameBlending        :: Boolean
  , timeRemapEnabled     :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Vec3
-- ────────────────────────────────────────────────────────────────────────────

type Vec3 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  , z :: FiniteFloat
  }

-- | Create Vec3 from raw numbers (validates finiteness)
mkVec3 :: Number -> Number -> Number -> Maybe Vec3
mkVec3 x y z = do
  fx <- mkFiniteFloat x
  fy <- mkFiniteFloat y
  fz <- mkFiniteFloat z
  pure { x: fx, y: fy, z: fz }

-- ────────────────────────────────────────────────────────────────────────────
-- Point and BoundingBox
-- ────────────────────────────────────────────────────────────────────────────

type Point =
  { x :: FiniteFloat
  , y :: FiniteFloat
  }

type BoundingBox =
  { x      :: FiniteFloat
  , y      :: FiniteFloat
  , width  :: PositiveFloat
  , height :: PositiveFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Composition
-- ────────────────────────────────────────────────────────────────────────────

type Composition =
  { id           :: NonEmptyString
  , name         :: NonEmptyString
  , settings     :: CompositionSettings
  , layers       :: Array LayerBase
  , currentFrame :: FrameNumber
  , isNestedComp :: Boolean
  , parentCompId :: Maybe NonEmptyString
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Asset Type and Metadata
-- ────────────────────────────────────────────────────────────────────────────

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

derive instance Eq AssetType
derive instance Generic AssetType _
instance Show AssetType where show = genericShow

type AssetMeta =
  { id         :: NonEmptyString
  , name       :: NonEmptyString
  , assetType  :: AssetType
  , path       :: Maybe String
  , mimeType   :: Maybe NonEmptyString
  , fileSize   :: Maybe Int
  , width      :: Maybe Int
  , height     :: Maybe Int
  , duration   :: Maybe FiniteFloat
  , frameCount :: Maybe Int
  , fps        :: Maybe PositiveFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Lattice Project
-- ────────────────────────────────────────────────────────────────────────────

type LatticeProject =
  { version           :: NonEmptyString
  , schemaVersion     :: Int  -- >= 1
  , meta              :: ProjectMeta
  , compositions      :: Array Composition
  , mainCompositionId :: NonEmptyString
  , assets            :: Array AssetMeta
  , currentFrame      :: FrameNumber
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Options
-- ────────────────────────────────────────────────────────────────────────────

data MatteExportMode = MEMExcludeText | MEMIncludeAll

derive instance Eq MatteExportMode
derive instance Generic MatteExportMode _
instance Show MatteExportMode where show = genericShow

type ExportOptions =
  { format    :: NonEmptyString
  , matteMode :: MatteExportMode
  , width     :: Int  -- > 0
  , height    :: Int  -- > 0
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Color Gradient
-- ────────────────────────────────────────────────────────────────────────────

type GradientStop =
  { position :: UnitFloat  -- 0-1
  , color    :: HexColor
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Extracted Texture
-- ────────────────────────────────────────────────────────────────────────────

data ExtractionMethod = EMMatSeg | EMManual | EMSDXL

derive instance Eq ExtractionMethod
derive instance Generic ExtractionMethod _
instance Show ExtractionMethod where show = genericShow

type PBRTextures =
  { roughness :: NonEmptyString  -- Base64 PNG
  , metallic  :: NonEmptyString
  , normal    :: NonEmptyString
  , height    :: NonEmptyString
  , ao        :: NonEmptyString
  }

type ExtractedTexture =
  { id               :: NonEmptyString
  , sourceAssetId    :: NonEmptyString
  , region           :: BoundingBox
  , albedo           :: NonEmptyString  -- Base64 PNG
  , pbr              :: PBRTextures
  , extractionMethod :: ExtractionMethod
  , seamless         :: Boolean
  , resolutionWidth  :: Int  -- > 0
  , resolutionHeight :: Int  -- > 0
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Factory Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Create an empty project with given dimensions and timestamp
-- | Pure version - takes timestamp as parameter instead of using Effect
-- | Matches TS createEmptyProject(width, height)
-- | Note: width and height must be divisible by 8
createEmptyProject :: Int -> Int -> NonEmptyString -> LatticeProject
createEmptyProject width height timestamp =
  { version: nes "1.0.0"
  , schemaVersion: 2
  , meta:
      { name: "Untitled"
      , created: timestamp
      , modified: timestamp
      , author: Nothing
      , description: Nothing
      , tags: []
      }
  , compositions:
      [ { id: nes "main"
        , name: nes "Main Comp"
        , settings:
            { width
            , height
            , frameCount: 81
            , fps: pf 16.0
            , duration: nnf 5.0625
            , backgroundColor: hex "#2d2d2d"
            , autoResizeToContent: true
            , frameBlendingEnabled: false
            }
        , layers: []
        , currentFrame: FrameNumber 0
        , isNestedComp: false
        , parentCompId: Nothing
        }
      ]
  , mainCompositionId: nes "main"
  , assets: []
  , currentFrame: FrameNumber 0
  }
  where
    nes s = case mkNonEmptyString s of
      Just v -> v
      Nothing -> NonEmptyString "error"
    pf n = case mkPositiveFloat n of
      Just v -> v
      Nothing -> PositiveFloat 1.0
    nnf n = case mkNonNegativeFloat n of
      Just v -> v
      Nothing -> NonNegativeFloat 0.0
    hex s = case mkHexColor s of
      Just v -> v
      Nothing -> HexColor "#000000"
