{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Assets.AssetsSchema
Description : Asset type enums and reference types
Copyright   : (c) Lattice, 2026
License     : MIT

Asset type enums and reference types.

Source: ui/src/schemas/assets/assets-schema.ts
-}

module Lattice.Schemas.Assets.AssetsSchema
  ( -- * Asset Type
    AssetType(..)
  , assetTypeFromText
  , assetTypeToText
    -- * Texture Map Type
  , TextureMapType(..)
  , textureMapTypeFromText
  , textureMapTypeToText
    -- * Model Format
  , ModelFormat(..)
  , modelFormatFromText
  , modelFormatToText
    -- * Point Cloud Format
  , PointCloudFormat(..)
  , pointCloudFormatFromText
  , pointCloudFormatToText
    -- * Asset Source
  , AssetSource(..)
  , assetSourceFromText
  , assetSourceToText
    -- * Texture Color Space
  , TextureColorSpace(..)
  , textureColorSpaceFromText
  , textureColorSpaceToText
    -- * Data Asset Type
  , DataAssetType(..)
  , dataAssetTypeFromText
  , dataAssetTypeToText
    -- * Structures
  , Vec3(..)
  , SVGViewBox(..)
    -- * Constants
  , maxDimension
  , maxFrameCount
  , maxDuration
  , maxFPS
  , maxSampleRate
  , maxMeshCount
  , maxVertexCount
  , maxPointCount
  , maxSpriteCols
  , maxSpriteRows
  , maxSpriteCount
  , maxSvgPaths
  , maxHdriExposure
  , minHdriExposure
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Asset Type
--------------------------------------------------------------------------------

-- | Asset type options
data AssetType
  = AssetDepthMap
  | AssetImage
  | AssetVideo
  | AssetAudio
  | AssetModel
  | AssetPointcloud
  | AssetTexture
  | AssetMaterial
  | AssetHdri
  | AssetSvg
  | AssetSprite
  | AssetSpritesheet
  | AssetLut
  deriving stock (Eq, Show, Generic, Enum, Bounded)

assetTypeFromText :: Text -> Maybe AssetType
assetTypeFromText "depth_map" = Just AssetDepthMap
assetTypeFromText "image" = Just AssetImage
assetTypeFromText "video" = Just AssetVideo
assetTypeFromText "audio" = Just AssetAudio
assetTypeFromText "model" = Just AssetModel
assetTypeFromText "pointcloud" = Just AssetPointcloud
assetTypeFromText "texture" = Just AssetTexture
assetTypeFromText "material" = Just AssetMaterial
assetTypeFromText "hdri" = Just AssetHdri
assetTypeFromText "svg" = Just AssetSvg
assetTypeFromText "sprite" = Just AssetSprite
assetTypeFromText "spritesheet" = Just AssetSpritesheet
assetTypeFromText "lut" = Just AssetLut
assetTypeFromText _ = Nothing

assetTypeToText :: AssetType -> Text
assetTypeToText AssetDepthMap = "depth_map"
assetTypeToText AssetImage = "image"
assetTypeToText AssetVideo = "video"
assetTypeToText AssetAudio = "audio"
assetTypeToText AssetModel = "model"
assetTypeToText AssetPointcloud = "pointcloud"
assetTypeToText AssetTexture = "texture"
assetTypeToText AssetMaterial = "material"
assetTypeToText AssetHdri = "hdri"
assetTypeToText AssetSvg = "svg"
assetTypeToText AssetSprite = "sprite"
assetTypeToText AssetSpritesheet = "spritesheet"
assetTypeToText AssetLut = "lut"

--------------------------------------------------------------------------------
-- Texture Map Type
--------------------------------------------------------------------------------

-- | Texture map type options
data TextureMapType
  = MapAlbedo
  | MapNormal
  | MapRoughness
  | MapMetalness
  | MapAO
  | MapEmissive
  | MapHeight
  | MapOpacity
  | MapSpecular
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textureMapTypeFromText :: Text -> Maybe TextureMapType
textureMapTypeFromText "albedo" = Just MapAlbedo
textureMapTypeFromText "normal" = Just MapNormal
textureMapTypeFromText "roughness" = Just MapRoughness
textureMapTypeFromText "metalness" = Just MapMetalness
textureMapTypeFromText "ao" = Just MapAO
textureMapTypeFromText "emissive" = Just MapEmissive
textureMapTypeFromText "height" = Just MapHeight
textureMapTypeFromText "opacity" = Just MapOpacity
textureMapTypeFromText "specular" = Just MapSpecular
textureMapTypeFromText _ = Nothing

textureMapTypeToText :: TextureMapType -> Text
textureMapTypeToText MapAlbedo = "albedo"
textureMapTypeToText MapNormal = "normal"
textureMapTypeToText MapRoughness = "roughness"
textureMapTypeToText MapMetalness = "metalness"
textureMapTypeToText MapAO = "ao"
textureMapTypeToText MapEmissive = "emissive"
textureMapTypeToText MapHeight = "height"
textureMapTypeToText MapOpacity = "opacity"
textureMapTypeToText MapSpecular = "specular"

--------------------------------------------------------------------------------
-- Model Format
--------------------------------------------------------------------------------

-- | 3D model format options
data ModelFormat
  = FormatGLTF
  | FormatGLB
  | FormatOBJ
  | FormatFBX
  | FormatUSD
  | FormatUSDA
  | FormatUSDC
  | FormatUSDZ
  deriving stock (Eq, Show, Generic, Enum, Bounded)

modelFormatFromText :: Text -> Maybe ModelFormat
modelFormatFromText "gltf" = Just FormatGLTF
modelFormatFromText "glb" = Just FormatGLB
modelFormatFromText "obj" = Just FormatOBJ
modelFormatFromText "fbx" = Just FormatFBX
modelFormatFromText "usd" = Just FormatUSD
modelFormatFromText "usda" = Just FormatUSDA
modelFormatFromText "usdc" = Just FormatUSDC
modelFormatFromText "usdz" = Just FormatUSDZ
modelFormatFromText _ = Nothing

modelFormatToText :: ModelFormat -> Text
modelFormatToText FormatGLTF = "gltf"
modelFormatToText FormatGLB = "glb"
modelFormatToText FormatOBJ = "obj"
modelFormatToText FormatFBX = "fbx"
modelFormatToText FormatUSD = "usd"
modelFormatToText FormatUSDA = "usda"
modelFormatToText FormatUSDC = "usdc"
modelFormatToText FormatUSDZ = "usdz"

--------------------------------------------------------------------------------
-- Point Cloud Format
--------------------------------------------------------------------------------

-- | Point cloud format options
data PointCloudFormat
  = FormatPLY
  | FormatPCD
  | FormatLAS
  | FormatLAZ
  | FormatXYZ
  | FormatPTS
  deriving stock (Eq, Show, Generic, Enum, Bounded)

pointCloudFormatFromText :: Text -> Maybe PointCloudFormat
pointCloudFormatFromText "ply" = Just FormatPLY
pointCloudFormatFromText "pcd" = Just FormatPCD
pointCloudFormatFromText "las" = Just FormatLAS
pointCloudFormatFromText "laz" = Just FormatLAZ
pointCloudFormatFromText "xyz" = Just FormatXYZ
pointCloudFormatFromText "pts" = Just FormatPTS
pointCloudFormatFromText _ = Nothing

pointCloudFormatToText :: PointCloudFormat -> Text
pointCloudFormatToText FormatPLY = "ply"
pointCloudFormatToText FormatPCD = "pcd"
pointCloudFormatToText FormatLAS = "las"
pointCloudFormatToText FormatLAZ = "laz"
pointCloudFormatToText FormatXYZ = "xyz"
pointCloudFormatToText FormatPTS = "pts"

--------------------------------------------------------------------------------
-- Asset Source
--------------------------------------------------------------------------------

-- | Asset source options
data AssetSource
  = SourceComfyUINode
  | SourceFile
  | SourceGenerated
  | SourceURL
  deriving stock (Eq, Show, Generic, Enum, Bounded)

assetSourceFromText :: Text -> Maybe AssetSource
assetSourceFromText "comfyui_node" = Just SourceComfyUINode
assetSourceFromText "file" = Just SourceFile
assetSourceFromText "generated" = Just SourceGenerated
assetSourceFromText "url" = Just SourceURL
assetSourceFromText _ = Nothing

assetSourceToText :: AssetSource -> Text
assetSourceToText SourceComfyUINode = "comfyui_node"
assetSourceToText SourceFile = "file"
assetSourceToText SourceGenerated = "generated"
assetSourceToText SourceURL = "url"

--------------------------------------------------------------------------------
-- Texture Color Space
--------------------------------------------------------------------------------

-- | Texture color space options
data TextureColorSpace
  = ColorSpaceSRGB
  | ColorSpaceLinear
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textureColorSpaceFromText :: Text -> Maybe TextureColorSpace
textureColorSpaceFromText "srgb" = Just ColorSpaceSRGB
textureColorSpaceFromText "linear" = Just ColorSpaceLinear
textureColorSpaceFromText _ = Nothing

textureColorSpaceToText :: TextureColorSpace -> Text
textureColorSpaceToText ColorSpaceSRGB = "srgb"
textureColorSpaceToText ColorSpaceLinear = "linear"

--------------------------------------------------------------------------------
-- Data Asset Type
--------------------------------------------------------------------------------

-- | Data asset type options
data DataAssetType
  = DataJSON
  | DataCSV
  | DataTSV
  | DataMGJSON
  deriving stock (Eq, Show, Generic, Enum, Bounded)

dataAssetTypeFromText :: Text -> Maybe DataAssetType
dataAssetTypeFromText "json" = Just DataJSON
dataAssetTypeFromText "csv" = Just DataCSV
dataAssetTypeFromText "tsv" = Just DataTSV
dataAssetTypeFromText "mgjson" = Just DataMGJSON
dataAssetTypeFromText _ = Nothing

dataAssetTypeToText :: DataAssetType -> Text
dataAssetTypeToText DataJSON = "json"
dataAssetTypeToText DataCSV = "csv"
dataAssetTypeToText DataTSV = "tsv"
dataAssetTypeToText DataMGJSON = "mgjson"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | 3D vector
data Vec3 = Vec3
  { vec3X :: !Double
  , vec3Y :: !Double
  , vec3Z :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | SVG viewbox
data SVGViewBox = SVGViewBox
  { svgVBX :: !Double
  , svgVBY :: !Double
  , svgVBWidth :: !Double
  , svgVBHeight :: !Double
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxDimension :: Int
maxDimension = 16384

maxFrameCount :: Int
maxFrameCount = 100000

maxDuration :: Double
maxDuration = 86400.0

maxFPS :: Double
maxFPS = 120.0

maxSampleRate :: Int
maxSampleRate = 192000

maxMeshCount :: Int
maxMeshCount = 100000

maxVertexCount :: Int
maxVertexCount = 10000000

maxPointCount :: Int
maxPointCount = 100000000

maxSpriteCols :: Int
maxSpriteCols = 1000

maxSpriteRows :: Int
maxSpriteRows = 1000

maxSpriteCount :: Int
maxSpriteCount = 1000000

maxSvgPaths :: Int
maxSvgPaths = 100000

maxHdriExposure :: Double
maxHdriExposure = 10.0

minHdriExposure :: Double
minHdriExposure = -10.0
