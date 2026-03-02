-- | Lattice.Schemas.Assets.AssetsSchema - Asset type enums and reference types
-- |
-- | Asset type enums and reference types.
-- |
-- | Source: ui/src/schemas/assets/assets-schema.ts

module Lattice.Schemas.Assets.AssetsSchema
  ( -- Asset Type
    AssetType(..)
  , assetTypeFromString
  , assetTypeToString
    -- Texture Map Type
  , TextureMapType(..)
  , textureMapTypeFromString
  , textureMapTypeToString
    -- Model Format
  , ModelFormat(..)
  , modelFormatFromString
  , modelFormatToString
    -- Point Cloud Format
  , PointCloudFormat(..)
  , pointCloudFormatFromString
  , pointCloudFormatToString
    -- Asset Source
  , AssetSource(..)
  , assetSourceFromString
  , assetSourceToString
    -- Texture Color Space
  , TextureColorSpace(..)
  , textureColorSpaceFromString
  , textureColorSpaceToString
    -- Data Asset Type
  , DataAssetType(..)
  , dataAssetTypeFromString
  , dataAssetTypeToString
    -- Structures
  , Vec3
  , SVGViewBox
    -- Constants
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

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Asset Type
-- ────────────────────────────────────────────────────────────────────────────

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

derive instance Eq AssetType
derive instance Generic AssetType _

instance Show AssetType where
  show = genericShow

assetTypeFromString :: String -> Maybe AssetType
assetTypeFromString = case _ of
  "depth_map" -> Just AssetDepthMap
  "image" -> Just AssetImage
  "video" -> Just AssetVideo
  "audio" -> Just AssetAudio
  "model" -> Just AssetModel
  "pointcloud" -> Just AssetPointcloud
  "texture" -> Just AssetTexture
  "material" -> Just AssetMaterial
  "hdri" -> Just AssetHdri
  "svg" -> Just AssetSvg
  "sprite" -> Just AssetSprite
  "spritesheet" -> Just AssetSpritesheet
  "lut" -> Just AssetLut
  _ -> Nothing

assetTypeToString :: AssetType -> String
assetTypeToString = case _ of
  AssetDepthMap -> "depth_map"
  AssetImage -> "image"
  AssetVideo -> "video"
  AssetAudio -> "audio"
  AssetModel -> "model"
  AssetPointcloud -> "pointcloud"
  AssetTexture -> "texture"
  AssetMaterial -> "material"
  AssetHdri -> "hdri"
  AssetSvg -> "svg"
  AssetSprite -> "sprite"
  AssetSpritesheet -> "spritesheet"
  AssetLut -> "lut"

-- ────────────────────────────────────────────────────────────────────────────
-- Texture Map Type
-- ────────────────────────────────────────────────────────────────────────────

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

derive instance Eq TextureMapType
derive instance Generic TextureMapType _

instance Show TextureMapType where
  show = genericShow

textureMapTypeFromString :: String -> Maybe TextureMapType
textureMapTypeFromString = case _ of
  "albedo" -> Just MapAlbedo
  "normal" -> Just MapNormal
  "roughness" -> Just MapRoughness
  "metalness" -> Just MapMetalness
  "ao" -> Just MapAO
  "emissive" -> Just MapEmissive
  "height" -> Just MapHeight
  "opacity" -> Just MapOpacity
  "specular" -> Just MapSpecular
  _ -> Nothing

textureMapTypeToString :: TextureMapType -> String
textureMapTypeToString = case _ of
  MapAlbedo -> "albedo"
  MapNormal -> "normal"
  MapRoughness -> "roughness"
  MapMetalness -> "metalness"
  MapAO -> "ao"
  MapEmissive -> "emissive"
  MapHeight -> "height"
  MapOpacity -> "opacity"
  MapSpecular -> "specular"

-- ────────────────────────────────────────────────────────────────────────────
-- Model Format
-- ────────────────────────────────────────────────────────────────────────────

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

derive instance Eq ModelFormat
derive instance Generic ModelFormat _

instance Show ModelFormat where
  show = genericShow

modelFormatFromString :: String -> Maybe ModelFormat
modelFormatFromString = case _ of
  "gltf" -> Just FormatGLTF
  "glb" -> Just FormatGLB
  "obj" -> Just FormatOBJ
  "fbx" -> Just FormatFBX
  "usd" -> Just FormatUSD
  "usda" -> Just FormatUSDA
  "usdc" -> Just FormatUSDC
  "usdz" -> Just FormatUSDZ
  _ -> Nothing

modelFormatToString :: ModelFormat -> String
modelFormatToString = case _ of
  FormatGLTF -> "gltf"
  FormatGLB -> "glb"
  FormatOBJ -> "obj"
  FormatFBX -> "fbx"
  FormatUSD -> "usd"
  FormatUSDA -> "usda"
  FormatUSDC -> "usdc"
  FormatUSDZ -> "usdz"

-- ────────────────────────────────────────────────────────────────────────────
-- Point Cloud Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Point cloud format options
data PointCloudFormat
  = FormatPLY
  | FormatPCD
  | FormatLAS
  | FormatLAZ
  | FormatXYZ
  | FormatPTS

derive instance Eq PointCloudFormat
derive instance Generic PointCloudFormat _

instance Show PointCloudFormat where
  show = genericShow

pointCloudFormatFromString :: String -> Maybe PointCloudFormat
pointCloudFormatFromString = case _ of
  "ply" -> Just FormatPLY
  "pcd" -> Just FormatPCD
  "las" -> Just FormatLAS
  "laz" -> Just FormatLAZ
  "xyz" -> Just FormatXYZ
  "pts" -> Just FormatPTS
  _ -> Nothing

pointCloudFormatToString :: PointCloudFormat -> String
pointCloudFormatToString = case _ of
  FormatPLY -> "ply"
  FormatPCD -> "pcd"
  FormatLAS -> "las"
  FormatLAZ -> "laz"
  FormatXYZ -> "xyz"
  FormatPTS -> "pts"

-- ────────────────────────────────────────────────────────────────────────────
-- Asset Source
-- ────────────────────────────────────────────────────────────────────────────

-- | Asset source options
data AssetSource
  = SourceComfyUINode
  | SourceFile
  | SourceGenerated
  | SourceURL

derive instance Eq AssetSource
derive instance Generic AssetSource _

instance Show AssetSource where
  show = genericShow

assetSourceFromString :: String -> Maybe AssetSource
assetSourceFromString = case _ of
  "comfyui_node" -> Just SourceComfyUINode
  "file" -> Just SourceFile
  "generated" -> Just SourceGenerated
  "url" -> Just SourceURL
  _ -> Nothing

assetSourceToString :: AssetSource -> String
assetSourceToString = case _ of
  SourceComfyUINode -> "comfyui_node"
  SourceFile -> "file"
  SourceGenerated -> "generated"
  SourceURL -> "url"

-- ────────────────────────────────────────────────────────────────────────────
-- Texture Color Space
-- ────────────────────────────────────────────────────────────────────────────

-- | Texture color space options
data TextureColorSpace
  = ColorSpaceSRGB
  | ColorSpaceLinear

derive instance Eq TextureColorSpace
derive instance Generic TextureColorSpace _

instance Show TextureColorSpace where
  show = genericShow

textureColorSpaceFromString :: String -> Maybe TextureColorSpace
textureColorSpaceFromString = case _ of
  "srgb" -> Just ColorSpaceSRGB
  "linear" -> Just ColorSpaceLinear
  _ -> Nothing

textureColorSpaceToString :: TextureColorSpace -> String
textureColorSpaceToString = case _ of
  ColorSpaceSRGB -> "srgb"
  ColorSpaceLinear -> "linear"

-- ────────────────────────────────────────────────────────────────────────────
-- Data Asset Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Data asset type options
data DataAssetType
  = DataJSON
  | DataCSV
  | DataTSV
  | DataMGJSON

derive instance Eq DataAssetType
derive instance Generic DataAssetType _

instance Show DataAssetType where
  show = genericShow

dataAssetTypeFromString :: String -> Maybe DataAssetType
dataAssetTypeFromString = case _ of
  "json" -> Just DataJSON
  "csv" -> Just DataCSV
  "tsv" -> Just DataTSV
  "mgjson" -> Just DataMGJSON
  _ -> Nothing

dataAssetTypeToString :: DataAssetType -> String
dataAssetTypeToString = case _ of
  DataJSON -> "json"
  DataCSV -> "csv"
  DataTSV -> "tsv"
  DataMGJSON -> "mgjson"

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 3D vector
type Vec3 =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | SVG viewbox
type SVGViewBox =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxDimension :: Int
maxDimension = 16384

maxFrameCount :: Int
maxFrameCount = 100000

maxDuration :: Number
maxDuration = 86400.0

maxFPS :: Number
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

maxHdriExposure :: Number
maxHdriExposure = 10.0

minHdriExposure :: Number
minHdriExposure = -10.0
