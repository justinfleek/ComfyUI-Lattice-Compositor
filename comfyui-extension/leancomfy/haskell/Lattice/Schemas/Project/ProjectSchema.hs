{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Project.ProjectSchema
Description : Project-level enums
Copyright   : (c) Lattice, 2026
License     : MIT

Project, composition, and asset type enums.

Source: ui/src/schemas/project-schema.ts
-}

module Lattice.Schemas.Project.ProjectSchema
  ( -- * Constants
    projectVersion
  , maxDimension
  , maxFps
  , maxFrameCount
    -- * Color Settings
  , ColorSpace(..), colorSpaceFromText, colorSpaceToText
  , ViewTransform(..), viewTransformFromText, viewTransformToText
    -- * Workflow Types
  , WorkflowInputType(..), workflowInputTypeFromText
  , WorkflowOutputType(..), workflowOutputTypeFromText
    -- * Asset Types
  , AssetType(..), assetTypeFromText, assetTypeToText
  , AssetSource(..), assetSourceFromText, assetSourceToText
  , TextureMapType(..), textureMapTypeFromText
  , ModelFormat(..), modelFormatFromText
  , PointCloudFormat(..), pointCloudFormatFromText
  , TextureColorSpace(..), textureColorSpaceFromText
    -- * Data Asset Types
  , DataAssetType(..), dataAssetTypeFromText
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

projectVersion :: Text
projectVersion = "1.0.0"

maxDimension :: Int
maxDimension = 16384

maxFps :: Int
maxFps = 120

maxFrameCount :: Int
maxFrameCount = 100000

--------------------------------------------------------------------------------
-- Color Settings
--------------------------------------------------------------------------------

data ColorSpace
  = CsSRGB
  | CsLinearSRGB
  | CsWideGamutRGB
  | CsDisplayP3
  | CsProPhotoRGB
  | CsACEScg
  | CsRec709
  | CsRec2020
  deriving stock (Eq, Show, Generic, Enum, Bounded)

colorSpaceFromText :: Text -> Maybe ColorSpace
colorSpaceFromText "sRGB" = Just CsSRGB
colorSpaceFromText "linear-sRGB" = Just CsLinearSRGB
colorSpaceFromText "Wide-Gamut-RGB" = Just CsWideGamutRGB
colorSpaceFromText "Display-P3" = Just CsDisplayP3
colorSpaceFromText "ProPhoto-RGB" = Just CsProPhotoRGB
colorSpaceFromText "ACEScg" = Just CsACEScg
colorSpaceFromText "Rec709" = Just CsRec709
colorSpaceFromText "Rec2020" = Just CsRec2020
colorSpaceFromText _ = Nothing

colorSpaceToText :: ColorSpace -> Text
colorSpaceToText CsSRGB = "sRGB"
colorSpaceToText CsLinearSRGB = "linear-sRGB"
colorSpaceToText CsWideGamutRGB = "Wide-Gamut-RGB"
colorSpaceToText CsDisplayP3 = "Display-P3"
colorSpaceToText CsProPhotoRGB = "ProPhoto-RGB"
colorSpaceToText CsACEScg = "ACEScg"
colorSpaceToText CsRec709 = "Rec709"
colorSpaceToText CsRec2020 = "Rec2020"

data ViewTransform
  = VtSRGB
  | VtDisplayP3
  | VtRec709
  | VtACESsRGB
  | VtFilmic
  deriving stock (Eq, Show, Generic, Enum, Bounded)

viewTransformFromText :: Text -> Maybe ViewTransform
viewTransformFromText "sRGB" = Just VtSRGB
viewTransformFromText "Display-P3" = Just VtDisplayP3
viewTransformFromText "Rec709" = Just VtRec709
viewTransformFromText "ACES-sRGB" = Just VtACESsRGB
viewTransformFromText "Filmic" = Just VtFilmic
viewTransformFromText _ = Nothing

viewTransformToText :: ViewTransform -> Text
viewTransformToText VtSRGB = "sRGB"
viewTransformToText VtDisplayP3 = "Display-P3"
viewTransformToText VtRec709 = "Rec709"
viewTransformToText VtACESsRGB = "ACES-sRGB"
viewTransformToText VtFilmic = "Filmic"

--------------------------------------------------------------------------------
-- Workflow Types
--------------------------------------------------------------------------------

data WorkflowInputType
  = WiImage
  | WiVideo
  | WiLatent
  | WiMask
  | WiNumber
  | WiString
  deriving stock (Eq, Show, Generic, Enum, Bounded)

workflowInputTypeFromText :: Text -> Maybe WorkflowInputType
workflowInputTypeFromText "image" = Just WiImage
workflowInputTypeFromText "video" = Just WiVideo
workflowInputTypeFromText "latent" = Just WiLatent
workflowInputTypeFromText "mask" = Just WiMask
workflowInputTypeFromText "number" = Just WiNumber
workflowInputTypeFromText "string" = Just WiString
workflowInputTypeFromText _ = Nothing

data WorkflowOutputType
  = WoImage
  | WoVideo
  | WoLatent
  deriving stock (Eq, Show, Generic, Enum, Bounded)

workflowOutputTypeFromText :: Text -> Maybe WorkflowOutputType
workflowOutputTypeFromText "image" = Just WoImage
workflowOutputTypeFromText "video" = Just WoVideo
workflowOutputTypeFromText "latent" = Just WoLatent
workflowOutputTypeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Asset Types
--------------------------------------------------------------------------------

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

assetTypeFromText :: Text -> Maybe AssetType
assetTypeFromText "depth_map" = Just AtDepthMap
assetTypeFromText "image" = Just AtImage
assetTypeFromText "video" = Just AtVideo
assetTypeFromText "audio" = Just AtAudio
assetTypeFromText "model" = Just AtModel
assetTypeFromText "pointcloud" = Just AtPointcloud
assetTypeFromText "texture" = Just AtTexture
assetTypeFromText "material" = Just AtMaterial
assetTypeFromText "hdri" = Just AtHdri
assetTypeFromText "svg" = Just AtSvg
assetTypeFromText "sprite" = Just AtSprite
assetTypeFromText "spritesheet" = Just AtSpritesheet
assetTypeFromText "lut" = Just AtLut
assetTypeFromText _ = Nothing

assetTypeToText :: AssetType -> Text
assetTypeToText AtDepthMap = "depth_map"
assetTypeToText AtImage = "image"
assetTypeToText AtVideo = "video"
assetTypeToText AtAudio = "audio"
assetTypeToText AtModel = "model"
assetTypeToText AtPointcloud = "pointcloud"
assetTypeToText AtTexture = "texture"
assetTypeToText AtMaterial = "material"
assetTypeToText AtHdri = "hdri"
assetTypeToText AtSvg = "svg"
assetTypeToText AtSprite = "sprite"
assetTypeToText AtSpritesheet = "spritesheet"
assetTypeToText AtLut = "lut"

data AssetSource
  = AsComfyuiNode
  | AsFile
  | AsGenerated
  | AsUrl
  deriving stock (Eq, Show, Generic, Enum, Bounded)

assetSourceFromText :: Text -> Maybe AssetSource
assetSourceFromText "comfyui_node" = Just AsComfyuiNode
assetSourceFromText "file" = Just AsFile
assetSourceFromText "generated" = Just AsGenerated
assetSourceFromText "url" = Just AsUrl
assetSourceFromText _ = Nothing

assetSourceToText :: AssetSource -> Text
assetSourceToText AsComfyuiNode = "comfyui_node"
assetSourceToText AsFile = "file"
assetSourceToText AsGenerated = "generated"
assetSourceToText AsUrl = "url"

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textureMapTypeFromText :: Text -> Maybe TextureMapType
textureMapTypeFromText "albedo" = Just TmAlbedo
textureMapTypeFromText "normal" = Just TmNormal
textureMapTypeFromText "roughness" = Just TmRoughness
textureMapTypeFromText "metalness" = Just TmMetalness
textureMapTypeFromText "ao" = Just TmAo
textureMapTypeFromText "emissive" = Just TmEmissive
textureMapTypeFromText "height" = Just TmHeight
textureMapTypeFromText "opacity" = Just TmOpacity
textureMapTypeFromText "specular" = Just TmSpecular
textureMapTypeFromText _ = Nothing

data ModelFormat = MfGltf | MfGlb | MfObj | MfFbx | MfUsd
  deriving stock (Eq, Show, Generic, Enum, Bounded)

modelFormatFromText :: Text -> Maybe ModelFormat
modelFormatFromText "gltf" = Just MfGltf
modelFormatFromText "glb" = Just MfGlb
modelFormatFromText "obj" = Just MfObj
modelFormatFromText "fbx" = Just MfFbx
modelFormatFromText "usd" = Just MfUsd
modelFormatFromText _ = Nothing

data PointCloudFormat = PcfPly | PcfPcd | PcfLas | PcfXyz
  deriving stock (Eq, Show, Generic, Enum, Bounded)

pointCloudFormatFromText :: Text -> Maybe PointCloudFormat
pointCloudFormatFromText "ply" = Just PcfPly
pointCloudFormatFromText "pcd" = Just PcfPcd
pointCloudFormatFromText "las" = Just PcfLas
pointCloudFormatFromText "xyz" = Just PcfXyz
pointCloudFormatFromText _ = Nothing

data TextureColorSpace = TcsSrgb | TcsLinear
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textureColorSpaceFromText :: Text -> Maybe TextureColorSpace
textureColorSpaceFromText "srgb" = Just TcsSrgb
textureColorSpaceFromText "linear" = Just TcsLinear
textureColorSpaceFromText _ = Nothing

--------------------------------------------------------------------------------
-- Data Asset Types
--------------------------------------------------------------------------------

data DataAssetType = DatJson | DatCsv | DatTsv | DatMgjson
  deriving stock (Eq, Show, Generic, Enum, Bounded)

dataAssetTypeFromText :: Text -> Maybe DataAssetType
dataAssetTypeFromText "json" = Just DatJson
dataAssetTypeFromText "csv" = Just DatCsv
dataAssetTypeFromText "tsv" = Just DatTsv
dataAssetTypeFromText "mgjson" = Just DatMgjson
dataAssetTypeFromText _ = Nothing
