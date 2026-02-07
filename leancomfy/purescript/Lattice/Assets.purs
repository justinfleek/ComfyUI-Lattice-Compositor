-- | Lattice.Assets - Asset types and references
-- |
-- | Source: leancomfy/lean/Lattice/Assets.lean

module Lattice.Assets
  ( AssetType(..)
  , TextureMapType(..)
  , ModelFormat(..)
  , PointCloudFormat(..)
  , TextureColorSpace(..)
  , AssetSource(..)
  , DataAssetType(..)
  , ModelBoundingBox
  , SvgViewBox
  , SpriteValidation
  , MaterialMaps
  , AssetReference
  , DataAssetReference
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Asset Type
--------------------------------------------------------------------------------

data AssetType
  = ATDepthMap     -- Depth map image
  | ATImage        -- Standard image (PNG, JPG, WebP)
  | ATVideo        -- Video file (MP4, WebM)
  | ATAudio        -- Audio file (MP3, WAV, OGG)
  | ATModel        -- 3D model (GLTF, OBJ, FBX, USD)
  | ATPointcloud   -- Point cloud (PLY, PCD, LAS)
  | ATTexture      -- PBR texture map
  | ATMaterial     -- Material definition
  | ATHDRI         -- Environment map (HDR, EXR)
  | ATSVG          -- Vector graphic
  | ATSprite       -- Single image for particles
  | ATSpritesheet  -- Sprite sheet (grid of frames)
  | ATLUT          -- Color lookup table

derive instance Eq AssetType
derive instance Generic AssetType _
instance Show AssetType where show = genericShow

--------------------------------------------------------------------------------
-- Texture Map Type
--------------------------------------------------------------------------------

data TextureMapType
  = TMTAlbedo     -- Base color / diffuse
  | TMTNormal     -- Normal map
  | TMTRoughness  -- Roughness map
  | TMTMetalness  -- Metalness map
  | TMTAO         -- Ambient occlusion
  | TMTEmissive   -- Emissive map
  | TMTHeight     -- Height/displacement
  | TMTOpacity    -- Alpha/opacity
  | TMTSpecular   -- Specular (non-PBR)

derive instance Eq TextureMapType
derive instance Generic TextureMapType _
instance Show TextureMapType where show = genericShow

--------------------------------------------------------------------------------
-- Model Format
--------------------------------------------------------------------------------

data ModelFormat
  = MFGltf | MFGlb | MFObj | MFFbx | MFUsd | MFUsda | MFUsdc | MFUsdz

derive instance Eq ModelFormat
derive instance Generic ModelFormat _
instance Show ModelFormat where show = genericShow

--------------------------------------------------------------------------------
-- Point Cloud Format
--------------------------------------------------------------------------------

data PointCloudFormat
  = PCFPly | PCFPcd | PCFLas | PCFLaz | PCFXyz | PCFPts

derive instance Eq PointCloudFormat
derive instance Generic PointCloudFormat _
instance Show PointCloudFormat where show = genericShow

--------------------------------------------------------------------------------
-- Texture Color Space
--------------------------------------------------------------------------------

data TextureColorSpace = TCSSrgb | TCSLinear

derive instance Eq TextureColorSpace
derive instance Generic TextureColorSpace _
instance Show TextureColorSpace where show = genericShow

--------------------------------------------------------------------------------
-- Asset Source
--------------------------------------------------------------------------------

data AssetSource
  = ASComfyuiNode | ASFile | ASGenerated | ASUrl

derive instance Eq AssetSource
derive instance Generic AssetSource _
instance Show AssetSource where show = genericShow

--------------------------------------------------------------------------------
-- Model Bounding Box
--------------------------------------------------------------------------------

type ModelBoundingBox =
  { minX    :: FiniteFloat
  , minY    :: FiniteFloat
  , minZ    :: FiniteFloat
  , maxX    :: FiniteFloat
  , maxY    :: FiniteFloat
  , maxZ    :: FiniteFloat
  , centerX :: FiniteFloat
  , centerY :: FiniteFloat
  , centerZ :: FiniteFloat
  , sizeX   :: FiniteFloat
  , sizeY   :: FiniteFloat
  , sizeZ   :: FiniteFloat
  }

--------------------------------------------------------------------------------
-- SVG View Box
--------------------------------------------------------------------------------

type SvgViewBox =
  { x      :: FiniteFloat
  , y      :: FiniteFloat
  , width  :: PositiveFloat
  , height :: PositiveFloat
  }

--------------------------------------------------------------------------------
-- Sprite Validation
--------------------------------------------------------------------------------

type SpriteValidation =
  { isPowerOfTwo   :: Boolean
  , hasAlpha       :: Boolean
  , originalFormat :: NonEmptyString
  , warnings       :: Array String
  }

--------------------------------------------------------------------------------
-- Material Maps
--------------------------------------------------------------------------------

type MaterialMaps =
  { albedo    :: Maybe NonEmptyString
  , normal    :: Maybe NonEmptyString
  , roughness :: Maybe NonEmptyString
  , metalness :: Maybe NonEmptyString
  , ao        :: Maybe NonEmptyString
  , emissive  :: Maybe NonEmptyString
  , height    :: Maybe NonEmptyString
  , opacity   :: Maybe NonEmptyString
  }

--------------------------------------------------------------------------------
-- Asset Reference
--------------------------------------------------------------------------------

type AssetReference =
  { id                  :: NonEmptyString
  , assetType           :: AssetType
  , source              :: AssetSource
  , nodeId              :: Maybe NonEmptyString
  , width               :: Int  -- > 0
  , height              :: Int  -- > 0
  , data                :: String  -- Base64 or URL
  , filename            :: Maybe NonEmptyString
  -- Video/Audio metadata
  , frameCount          :: Maybe Int
  , duration            :: Maybe PositiveFloat  -- Seconds
  , fps                 :: Maybe PositiveFloat  -- Source FPS
  , hasAudio            :: Maybe Boolean
  , audioChannels       :: Maybe Int  -- 1=mono, 2=stereo
  , sampleRate          :: Maybe Int
  -- 3D Model metadata
  , modelFormat         :: Maybe ModelFormat
  , modelBoundingBox    :: Maybe ModelBoundingBox
  , modelAnimations     :: Array String  -- Animation clip names
  , modelMeshCount      :: Maybe Int
  , modelVertexCount    :: Maybe Int
  -- Point cloud metadata
  , pointCloudFormat    :: Maybe PointCloudFormat
  , pointCount          :: Maybe Int
  -- Texture metadata
  , textureMapType      :: Maybe TextureMapType
  , textureColorSpace   :: Maybe TextureColorSpace
  -- Material definition
  , materialMaps        :: Maybe MaterialMaps
  -- HDRI metadata
  , hdriExposure        :: Maybe FiniteFloat
  , hdriRotation        :: Maybe FiniteFloat
  -- SVG metadata
  , svgPaths            :: Maybe Int
  , svgViewBox          :: Maybe SvgViewBox
  -- Sprite sheet metadata
  , spriteColumns       :: Maybe Int
  , spriteRows          :: Maybe Int
  , spriteCount         :: Maybe Int
  , spriteFrameRate     :: Maybe PositiveFloat
  , spriteValidation    :: Maybe SpriteValidation
  }

--------------------------------------------------------------------------------
-- Data Asset
--------------------------------------------------------------------------------

data DataAssetType = DATJson | DATCsv | DATTsv | DATMgjson

derive instance Eq DataAssetType
derive instance Generic DataAssetType _
instance Show DataAssetType where show = genericShow

type DataAssetReference =
  { id           :: NonEmptyString
  , name         :: NonEmptyString  -- Original filename
  , dataType     :: DataAssetType
  , rawContent   :: String
  , lastModified :: Int  -- Timestamp
  -- For CSV/TSV
  , headers      :: Array String
  , rows         :: Array (Array String)
  , numRows      :: Maybe Int
  , numColumns   :: Maybe Int
  }
