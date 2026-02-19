{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Assets
Description : Asset types and references
Copyright   : (c) Lattice, 2026
License     : MIT

Source: lattice-core/lean/Lattice/Assets.lean
-}

module Lattice.Assets
  ( -- * Enumerations
    AssetType(..)
  , TextureMapType(..)
  , ModelFormat(..)
  , PointCloudFormat(..)
  , TextureColorSpace(..)
  , AssetSource(..)
  , DataAssetType(..)
    -- * Bounding Box
  , ModelBoundingBox(..)
    -- * SVG
  , SvgViewBox(..)
    -- * Sprite
  , SpriteValidation(..)
    -- * Material
  , MaterialMaps(..)
    -- * Asset Reference
  , AssetReference(..)
    -- * Data Asset
  , DataAssetReference(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Asset Type
--------------------------------------------------------------------------------

data AssetType
  = ATDepthMap     -- ^ Depth map image
  | ATImage        -- ^ Standard image (PNG, JPG, WebP)
  | ATVideo        -- ^ Video file (MP4, WebM)
  | ATAudio        -- ^ Audio file (MP3, WAV, OGG)
  | ATModel        -- ^ 3D model (GLTF, OBJ, FBX, USD)
  | ATPointcloud   -- ^ Point cloud (PLY, PCD, LAS)
  | ATTexture      -- ^ PBR texture map
  | ATMaterial     -- ^ Material definition
  | ATHDRI         -- ^ Environment map (HDR, EXR)
  | ATSVG          -- ^ Vector graphic
  | ATSprite       -- ^ Single image for particles
  | ATSpritesheet  -- ^ Sprite sheet (grid of frames)
  | ATLUT          -- ^ Color lookup table
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Texture Map Type
--------------------------------------------------------------------------------

data TextureMapType
  = TMTAlbedo     -- ^ Base color / diffuse
  | TMTNormal     -- ^ Normal map
  | TMTRoughness  -- ^ Roughness map
  | TMTMetalness  -- ^ Metalness map
  | TMTAO         -- ^ Ambient occlusion
  | TMTEmissive   -- ^ Emissive map
  | TMTHeight     -- ^ Height/displacement
  | TMTOpacity    -- ^ Alpha/opacity
  | TMTSpecular   -- ^ Specular (non-PBR)
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Model Format
--------------------------------------------------------------------------------

data ModelFormat
  = MFGltf | MFGlb | MFObj | MFFbx | MFUsd | MFUsda | MFUsdc | MFUsdz
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Point Cloud Format
--------------------------------------------------------------------------------

data PointCloudFormat
  = PCFPly | PCFPcd | PCFLas | PCFLaz | PCFXyz | PCFPts
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Texture Color Space
--------------------------------------------------------------------------------

data TextureColorSpace = TCSSrgb | TCSLinear
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Asset Source
--------------------------------------------------------------------------------

data AssetSource
  = ASComfyuiNode | ASFile | ASGenerated | ASUrl
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Model Bounding Box
--------------------------------------------------------------------------------

data ModelBoundingBox = ModelBoundingBox
  { mbbMinX    :: !FiniteFloat
  , mbbMinY    :: !FiniteFloat
  , mbbMinZ    :: !FiniteFloat
  , mbbMaxX    :: !FiniteFloat
  , mbbMaxY    :: !FiniteFloat
  , mbbMaxZ    :: !FiniteFloat
  , mbbCenterX :: !FiniteFloat
  , mbbCenterY :: !FiniteFloat
  , mbbCenterZ :: !FiniteFloat
  , mbbSizeX   :: !FiniteFloat
  , mbbSizeY   :: !FiniteFloat
  , mbbSizeZ   :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- SVG View Box
--------------------------------------------------------------------------------

data SvgViewBox = SvgViewBox
  { svbX      :: !FiniteFloat
  , svbY      :: !FiniteFloat
  , svbWidth  :: !PositiveFloat
  , svbHeight :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Sprite Validation
--------------------------------------------------------------------------------

data SpriteValidation = SpriteValidation
  { svIsPowerOfTwo   :: !Bool
  , svHasAlpha       :: !Bool
  , svOriginalFormat :: !NonEmptyString
  , svWarnings       :: !(Vector Text)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Material Maps
--------------------------------------------------------------------------------

data MaterialMaps = MaterialMaps
  { mmAlbedo    :: !(Maybe NonEmptyString)
  , mmNormal    :: !(Maybe NonEmptyString)
  , mmRoughness :: !(Maybe NonEmptyString)
  , mmMetalness :: !(Maybe NonEmptyString)
  , mmAO        :: !(Maybe NonEmptyString)
  , mmEmissive  :: !(Maybe NonEmptyString)
  , mmHeight    :: !(Maybe NonEmptyString)
  , mmOpacity   :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Asset Reference
--------------------------------------------------------------------------------

data AssetReference = AssetReference
  { arId                  :: !NonEmptyString
  , arAssetType           :: !AssetType
  , arSource              :: !AssetSource
  , arNodeId              :: !(Maybe NonEmptyString)
  , arWidth               :: !Int  -- > 0
  , arHeight              :: !Int  -- > 0
  , arData                :: !Text  -- Base64 or URL
  , arFilename            :: !(Maybe NonEmptyString)
  -- Video/Audio metadata
  , arFrameCount          :: !(Maybe Int)
  , arDuration            :: !(Maybe PositiveFloat)  -- Seconds
  , arFps                 :: !(Maybe PositiveFloat)  -- Source FPS
  , arHasAudio            :: !(Maybe Bool)
  , arAudioChannels       :: !(Maybe Int)  -- 1=mono, 2=stereo
  , arSampleRate          :: !(Maybe Int)
  -- 3D Model metadata
  , arModelFormat         :: !(Maybe ModelFormat)
  , arModelBoundingBox    :: !(Maybe ModelBoundingBox)
  , arModelAnimations     :: !(Vector Text)  -- Animation clip names
  , arModelMeshCount      :: !(Maybe Int)
  , arModelVertexCount    :: !(Maybe Int)
  -- Point cloud metadata
  , arPointCloudFormat    :: !(Maybe PointCloudFormat)
  , arPointCount          :: !(Maybe Int)
  -- Texture metadata
  , arTextureMapType      :: !(Maybe TextureMapType)
  , arTextureColorSpace   :: !(Maybe TextureColorSpace)
  -- Material definition
  , arMaterialMaps        :: !(Maybe MaterialMaps)
  -- HDRI metadata
  , arHdriExposure        :: !(Maybe FiniteFloat)
  , arHdriRotation        :: !(Maybe FiniteFloat)
  -- SVG metadata
  , arSvgPaths            :: !(Maybe Int)
  , arSvgViewBox          :: !(Maybe SvgViewBox)
  -- Sprite sheet metadata
  , arSpriteColumns       :: !(Maybe Int)
  , arSpriteRows          :: !(Maybe Int)
  , arSpriteCount         :: !(Maybe Int)
  , arSpriteFrameRate     :: !(Maybe PositiveFloat)
  , arSpriteValidation    :: !(Maybe SpriteValidation)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Data Asset
--------------------------------------------------------------------------------

data DataAssetType = DATJson | DATCsv | DATTsv | DATMgjson
  deriving stock (Eq, Show, Generic)

data DataAssetReference = DataAssetReference
  { darId           :: !NonEmptyString
  , darName         :: !NonEmptyString  -- Original filename
  , darDataType     :: !DataAssetType
  , darRawContent   :: !Text
  , darLastModified :: !Int  -- Timestamp
  -- For CSV/TSV
  , darHeaders      :: !(Vector Text)
  , darRows         :: !(Vector (Vector Text))
  , darNumRows      :: !(Maybe Int)
  , darNumColumns   :: !(Maybe Int)
  } deriving stock (Eq, Show, Generic)
