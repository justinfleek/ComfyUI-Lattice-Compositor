-- | Lattice.Schemas.Project.ProjectSchema - Project-level enums
-- |
-- | Project, composition, and asset type enums.
-- |
-- | Source: ui/src/schemas/project-schema.ts

module Lattice.Schemas.Project.ProjectSchema
  ( -- Constants
    projectVersion
  , maxDimension
  , maxFps
  , maxFrameCount
    -- Color Settings
  , ColorSpace(..), colorSpaceFromString, colorSpaceToString
  , ViewTransform(..), viewTransformFromString, viewTransformToString
    -- Workflow Types
  , WorkflowInputType(..), workflowInputTypeFromString
  , WorkflowOutputType(..), workflowOutputTypeFromString
    -- Asset Types
  , AssetType(..), assetTypeFromString, assetTypeToString
  , AssetSource(..), assetSourceFromString, assetSourceToString
  , TextureMapType(..), textureMapTypeFromString
  , ModelFormat(..), modelFormatFromString
  , PointCloudFormat(..), pointCloudFormatFromString
  , TextureColorSpace(..), textureColorSpaceFromString
    -- Data Asset Types
  , DataAssetType(..), dataAssetTypeFromString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

projectVersion :: String
projectVersion = "1.0.0"

maxDimension :: Int
maxDimension = 16384

maxFps :: Int
maxFps = 120

maxFrameCount :: Int
maxFrameCount = 100000

-- ────────────────────────────────────────────────────────────────────────────
-- Color Settings
-- ────────────────────────────────────────────────────────────────────────────

data ColorSpace
  = CsSRGB
  | CsLinearSRGB
  | CsWideGamutRGB
  | CsDisplayP3
  | CsProPhotoRGB
  | CsACEScg
  | CsRec709
  | CsRec2020

derive instance Eq ColorSpace
derive instance Generic ColorSpace _
instance Show ColorSpace where show = genericShow

colorSpaceFromString :: String -> Maybe ColorSpace
colorSpaceFromString = case _ of
  "sRGB" -> Just CsSRGB
  "linear-sRGB" -> Just CsLinearSRGB
  "Wide-Gamut-RGB" -> Just CsWideGamutRGB
  "Display-P3" -> Just CsDisplayP3
  "ProPhoto-RGB" -> Just CsProPhotoRGB
  "ACEScg" -> Just CsACEScg
  "Rec709" -> Just CsRec709
  "Rec2020" -> Just CsRec2020
  _ -> Nothing

colorSpaceToString :: ColorSpace -> String
colorSpaceToString = case _ of
  CsSRGB -> "sRGB"
  CsLinearSRGB -> "linear-sRGB"
  CsWideGamutRGB -> "Wide-Gamut-RGB"
  CsDisplayP3 -> "Display-P3"
  CsProPhotoRGB -> "ProPhoto-RGB"
  CsACEScg -> "ACEScg"
  CsRec709 -> "Rec709"
  CsRec2020 -> "Rec2020"

data ViewTransform
  = VtSRGB
  | VtDisplayP3
  | VtRec709
  | VtACESsRGB
  | VtFilmic

derive instance Eq ViewTransform
derive instance Generic ViewTransform _
instance Show ViewTransform where show = genericShow

viewTransformFromString :: String -> Maybe ViewTransform
viewTransformFromString = case _ of
  "sRGB" -> Just VtSRGB
  "Display-P3" -> Just VtDisplayP3
  "Rec709" -> Just VtRec709
  "ACES-sRGB" -> Just VtACESsRGB
  "Filmic" -> Just VtFilmic
  _ -> Nothing

viewTransformToString :: ViewTransform -> String
viewTransformToString = case _ of
  VtSRGB -> "sRGB"
  VtDisplayP3 -> "Display-P3"
  VtRec709 -> "Rec709"
  VtACESsRGB -> "ACES-sRGB"
  VtFilmic -> "Filmic"

-- ────────────────────────────────────────────────────────────────────────────
-- Workflow Types
-- ────────────────────────────────────────────────────────────────────────────

data WorkflowInputType
  = WiImage
  | WiVideo
  | WiLatent
  | WiMask
  | WiNumber
  | WiString

derive instance Eq WorkflowInputType
derive instance Generic WorkflowInputType _
instance Show WorkflowInputType where show = genericShow

workflowInputTypeFromString :: String -> Maybe WorkflowInputType
workflowInputTypeFromString = case _ of
  "image" -> Just WiImage
  "video" -> Just WiVideo
  "latent" -> Just WiLatent
  "mask" -> Just WiMask
  "number" -> Just WiNumber
  "string" -> Just WiString
  _ -> Nothing

data WorkflowOutputType
  = WoImage
  | WoVideo
  | WoLatent

derive instance Eq WorkflowOutputType
derive instance Generic WorkflowOutputType _
instance Show WorkflowOutputType where show = genericShow

workflowOutputTypeFromString :: String -> Maybe WorkflowOutputType
workflowOutputTypeFromString = case _ of
  "image" -> Just WoImage
  "video" -> Just WoVideo
  "latent" -> Just WoLatent
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Asset Types
-- ────────────────────────────────────────────────────────────────────────────

data AssetType
  = AtDepthMap
  | AtImage
  | AtVideo
  | AtAudio
  | AtModel
  | AtPointcloud
  | AtTexture
  | AtMaterial
  | AtHdri
  | AtSvg
  | AtSprite
  | AtSpritesheet
  | AtLut

derive instance Eq AssetType
derive instance Generic AssetType _
instance Show AssetType where show = genericShow

assetTypeFromString :: String -> Maybe AssetType
assetTypeFromString = case _ of
  "depth_map" -> Just AtDepthMap
  "image" -> Just AtImage
  "video" -> Just AtVideo
  "audio" -> Just AtAudio
  "model" -> Just AtModel
  "pointcloud" -> Just AtPointcloud
  "texture" -> Just AtTexture
  "material" -> Just AtMaterial
  "hdri" -> Just AtHdri
  "svg" -> Just AtSvg
  "sprite" -> Just AtSprite
  "spritesheet" -> Just AtSpritesheet
  "lut" -> Just AtLut
  _ -> Nothing

assetTypeToString :: AssetType -> String
assetTypeToString = case _ of
  AtDepthMap -> "depth_map"
  AtImage -> "image"
  AtVideo -> "video"
  AtAudio -> "audio"
  AtModel -> "model"
  AtPointcloud -> "pointcloud"
  AtTexture -> "texture"
  AtMaterial -> "material"
  AtHdri -> "hdri"
  AtSvg -> "svg"
  AtSprite -> "sprite"
  AtSpritesheet -> "spritesheet"
  AtLut -> "lut"

data AssetSource
  = AsComfyuiNode
  | AsFile
  | AsGenerated
  | AsUrl

derive instance Eq AssetSource
derive instance Generic AssetSource _
instance Show AssetSource where show = genericShow

assetSourceFromString :: String -> Maybe AssetSource
assetSourceFromString = case _ of
  "comfyui_node" -> Just AsComfyuiNode
  "file" -> Just AsFile
  "generated" -> Just AsGenerated
  "url" -> Just AsUrl
  _ -> Nothing

assetSourceToString :: AssetSource -> String
assetSourceToString = case _ of
  AsComfyuiNode -> "comfyui_node"
  AsFile -> "file"
  AsGenerated -> "generated"
  AsUrl -> "url"

data TextureMapType
  = TmAlbedo
  | TmNormal
  | TmRoughness
  | TmMetalness
  | TmAo
  | TmEmissive
  | TmHeight
  | TmOpacity
  | TmSpecular

derive instance Eq TextureMapType
derive instance Generic TextureMapType _
instance Show TextureMapType where show = genericShow

textureMapTypeFromString :: String -> Maybe TextureMapType
textureMapTypeFromString = case _ of
  "albedo" -> Just TmAlbedo
  "normal" -> Just TmNormal
  "roughness" -> Just TmRoughness
  "metalness" -> Just TmMetalness
  "ao" -> Just TmAo
  "emissive" -> Just TmEmissive
  "height" -> Just TmHeight
  "opacity" -> Just TmOpacity
  "specular" -> Just TmSpecular
  _ -> Nothing

data ModelFormat = MfGltf | MfGlb | MfObj | MfFbx | MfUsd

derive instance Eq ModelFormat
derive instance Generic ModelFormat _
instance Show ModelFormat where show = genericShow

modelFormatFromString :: String -> Maybe ModelFormat
modelFormatFromString = case _ of
  "gltf" -> Just MfGltf
  "glb" -> Just MfGlb
  "obj" -> Just MfObj
  "fbx" -> Just MfFbx
  "usd" -> Just MfUsd
  _ -> Nothing

data PointCloudFormat = PcfPly | PcfPcd | PcfLas | PcfXyz

derive instance Eq PointCloudFormat
derive instance Generic PointCloudFormat _
instance Show PointCloudFormat where show = genericShow

pointCloudFormatFromString :: String -> Maybe PointCloudFormat
pointCloudFormatFromString = case _ of
  "ply" -> Just PcfPly
  "pcd" -> Just PcfPcd
  "las" -> Just PcfLas
  "xyz" -> Just PcfXyz
  _ -> Nothing

data TextureColorSpace = TcsSrgb | TcsLinear

derive instance Eq TextureColorSpace
derive instance Generic TextureColorSpace _
instance Show TextureColorSpace where show = genericShow

textureColorSpaceFromString :: String -> Maybe TextureColorSpace
textureColorSpaceFromString = case _ of
  "srgb" -> Just TcsSrgb
  "linear" -> Just TcsLinear
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Data Asset Types
-- ────────────────────────────────────────────────────────────────────────────

data DataAssetType = DatJson | DatCsv | DatTsv | DatMgjson

derive instance Eq DataAssetType
derive instance Generic DataAssetType _
instance Show DataAssetType where show = genericShow

dataAssetTypeFromString :: String -> Maybe DataAssetType
dataAssetTypeFromString = case _ of
  "json" -> Just DatJson
  "csv" -> Just DatCsv
  "tsv" -> Just DatTsv
  "mgjson" -> Just DatMgjson
  _ -> Nothing
