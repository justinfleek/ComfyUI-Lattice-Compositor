-- |
-- Module      : Lattice.Types.Assets.Core
-- Description : Core types for asset references and metadata
-- 
-- Migrated from ui/src/types/assets.ts
-- Complete asset reference types with all optional metadata fields
--                                                                      // note
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Assets.Core
  ( -- Asset types
    AssetType (..),
    TextureMapType (..),
    ModelFormat (..),
    PointCloudFormat (..),
    ModelBoundingBox (..),
    SpriteValidation (..),
    MaterialMaps (..),
    SVGViewBox (..),
    -- Asset reference
    AssetReference (..),
    AssetSource (..),
    TextureColorSpace (..),
  )
where

import Data.Aeson
  ( ToJSON (..),
    FromJSON (..),
    withObject,
    withText,
    object,
    (.=),
    (.:),
    (.:?),
    Value (..),
  )
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Primitives
  ( Vec3 (..),
    validateFinite,
    validateNonNegative,
  )
import Lattice.Schema.SharedValidation (validateBoundedArray)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // asset // type // definitions
-- ════════════════════════════════════════════════════════════════════════════

-- | Asset types supported by the compositor
data AssetType
  = AssetTypeDepthMap -- Depth map image
  | AssetTypeImage -- Standard image (PNG, JPG, WebP)
  | AssetTypeVideo -- Video file (MP4, WebM)
  | AssetTypeAudio -- Audio file (MP3, WAV, OGG)
  | AssetTypeModel -- 3D model (GLTF, OBJ, FBX, USD)
  | AssetTypePointCloud -- Point cloud (PLY, PCD, LAS)
  | AssetTypeTexture -- PBR texture map
  | AssetTypeMaterial -- Material definition (with texture refs)
  | AssetTypeHDRI -- Environment map (HDR, EXR)
  | AssetTypeSVG -- Vector graphic (for extrusion)
  | AssetTypeSprite -- Single image for particles (no grid)
  | AssetTypeSpriteSheet -- Sprite sheet for particles (grid of frames)
  | AssetTypeLUT -- Color lookup table
  deriving (Eq, Show, Generic)

instance ToJSON AssetType where
  toJSON AssetTypeDepthMap = "depth_map"
  toJSON AssetTypeImage = "image"
  toJSON AssetTypeVideo = "video"
  toJSON AssetTypeAudio = "audio"
  toJSON AssetTypeModel = "model"
  toJSON AssetTypePointCloud = "pointcloud"
  toJSON AssetTypeTexture = "texture"
  toJSON AssetTypeMaterial = "material"
  toJSON AssetTypeHDRI = "hdri"
  toJSON AssetTypeSVG = "svg"
  toJSON AssetTypeSprite = "sprite"
  toJSON AssetTypeSpriteSheet = "spritesheet"
  toJSON AssetTypeLUT = "lut"

instance FromJSON AssetType where
  parseJSON = withText "AssetType" $ \s ->
    case s of
      "depth_map" -> return AssetTypeDepthMap
      "image" -> return AssetTypeImage
      "video" -> return AssetTypeVideo
      "audio" -> return AssetTypeAudio
      "model" -> return AssetTypeModel
      "pointcloud" -> return AssetTypePointCloud
      "texture" -> return AssetTypeTexture
      "material" -> return AssetTypeMaterial
      "hdri" -> return AssetTypeHDRI
      "svg" -> return AssetTypeSVG
      "sprite" -> return AssetTypeSprite
      "spritesheet" -> return AssetTypeSpriteSheet
      "lut" -> return AssetTypeLUT
      _ -> fail "Invalid AssetType"

-- | PBR texture map types
data TextureMapType
  = TextureMapAlbedo -- Base color / diffuse
  | TextureMapNormal -- Normal map
  | TextureMapRoughness -- Roughness map
  | TextureMapMetalness -- Metalness map
  | TextureMapAO -- Ambient occlusion
  | TextureMapEmissive -- Emissive map
  | TextureMapHeight -- Height/displacement map
  | TextureMapOpacity -- Alpha/opacity map
  | TextureMapSpecular -- Specular map (for non-PBR workflows)
  deriving (Eq, Show, Generic)

instance ToJSON TextureMapType where
  toJSON TextureMapAlbedo = "albedo"
  toJSON TextureMapNormal = "normal"
  toJSON TextureMapRoughness = "roughness"
  toJSON TextureMapMetalness = "metalness"
  toJSON TextureMapAO = "ao"
  toJSON TextureMapEmissive = "emissive"
  toJSON TextureMapHeight = "height"
  toJSON TextureMapOpacity = "opacity"
  toJSON TextureMapSpecular = "specular"

instance FromJSON TextureMapType where
  parseJSON = withText "TextureMapType" $ \s ->
    case s of
      "albedo" -> return TextureMapAlbedo
      "normal" -> return TextureMapNormal
      "roughness" -> return TextureMapRoughness
      "metalness" -> return TextureMapMetalness
      "ao" -> return TextureMapAO
      "emissive" -> return TextureMapEmissive
      "height" -> return TextureMapHeight
      "opacity" -> return TextureMapOpacity
      "specular" -> return TextureMapSpecular
      _ -> fail "Invalid TextureMapType"

-- | 3D model formats
data ModelFormat
  = ModelFormatGLTF
  | ModelFormatGLB
  | ModelFormatOBJ
  | ModelFormatFBX
  | ModelFormatUSD
  | ModelFormatUSDA
  | ModelFormatUSDC
  | ModelFormatUSDZ
  deriving (Eq, Show, Generic)

instance ToJSON ModelFormat where
  toJSON ModelFormatGLTF = "gltf"
  toJSON ModelFormatGLB = "glb"
  toJSON ModelFormatOBJ = "obj"
  toJSON ModelFormatFBX = "fbx"
  toJSON ModelFormatUSD = "usd"
  toJSON ModelFormatUSDA = "usda"
  toJSON ModelFormatUSDC = "usdc"
  toJSON ModelFormatUSDZ = "usdz"

instance FromJSON ModelFormat where
  parseJSON = withText "ModelFormat" $ \s ->
    case s of
      "gltf" -> return ModelFormatGLTF
      "glb" -> return ModelFormatGLB
      "obj" -> return ModelFormatOBJ
      "fbx" -> return ModelFormatFBX
      "usd" -> return ModelFormatUSD
      "usda" -> return ModelFormatUSDA
      "usdc" -> return ModelFormatUSDC
      "usdz" -> return ModelFormatUSDZ
      _ -> fail "Invalid ModelFormat"

-- | Point cloud formats
data PointCloudFormat
  = PointCloudFormatPLY
  | PointCloudFormatPCD
  | PointCloudFormatLAS
  | PointCloudFormatLAZ
  | PointCloudFormatXYZ
  | PointCloudFormatPTS
  deriving (Eq, Show, Generic)

instance ToJSON PointCloudFormat where
  toJSON PointCloudFormatPLY = "ply"
  toJSON PointCloudFormatPCD = "pcd"
  toJSON PointCloudFormatLAS = "las"
  toJSON PointCloudFormatLAZ = "laz"
  toJSON PointCloudFormatXYZ = "xyz"
  toJSON PointCloudFormatPTS = "pts"

instance FromJSON PointCloudFormat where
  parseJSON = withText "PointCloudFormat" $ \s ->
    case s of
      "ply" -> return PointCloudFormatPLY
      "pcd" -> return PointCloudFormatPCD
      "las" -> return PointCloudFormatLAS
      "laz" -> return PointCloudFormatLAZ
      "xyz" -> return PointCloudFormatXYZ
      "pts" -> return PointCloudFormatPTS
      _ -> fail "Invalid PointCloudFormat"

-- | Model bounding box
data ModelBoundingBox = ModelBoundingBox
  { modelBoundingBoxMin :: Vec3,
    modelBoundingBoxMax :: Vec3,
    modelBoundingBoxCenter :: Vec3,
    modelBoundingBoxSize :: Vec3
  }
  deriving (Eq, Show, Generic)

instance ToJSON ModelBoundingBox where
  toJSON (ModelBoundingBox min_ max_ center size_) =
    object
      [ "min" .= min_,
        "max" .= max_,
        "center" .= center,
        "size" .= size_
      ]

instance FromJSON ModelBoundingBox where
  parseJSON = withObject "ModelBoundingBox" $ \o -> do
    min_ <- o .: "min"
    max_ <- o .: "max"
    center <- o .: "center"
    size_ <- o .: "size"
    return (ModelBoundingBox min_ max_ center size_)

-- | Texture color space
data TextureColorSpace
  = TextureColorSpaceSRGB
  | TextureColorSpaceLinear
  deriving (Eq, Show, Generic)

instance ToJSON TextureColorSpace where
  toJSON TextureColorSpaceSRGB = "srgb"
  toJSON TextureColorSpaceLinear = "linear"

instance FromJSON TextureColorSpace where
  parseJSON = withText "TextureColorSpace" $ \s ->
    case s of
      "srgb" -> return TextureColorSpaceSRGB
      "linear" -> return TextureColorSpaceLinear
      _ -> fail "Invalid TextureColorSpace"

-- | Material maps (references other texture assets)
data MaterialMaps = MaterialMaps
  { materialMapsAlbedo :: Maybe Text, -- Asset ID for albedo texture
    materialMapsNormal :: Maybe Text, -- Asset ID for normal map
    materialMapsRoughness :: Maybe Text, -- Asset ID for roughness map
    materialMapsMetalness :: Maybe Text, -- Asset ID for metalness map
    materialMapsAO :: Maybe Text, -- Asset ID for AO map
    materialMapsEmissive :: Maybe Text, -- Asset ID for emissive map
    materialMapsHeight :: Maybe Text, -- Asset ID for height map
    materialMapsOpacity :: Maybe Text -- Asset ID for opacity map
  }
  deriving (Eq, Show, Generic)

instance ToJSON MaterialMaps where
  toJSON (MaterialMaps albedo normal roughness metalness ao emissive height opacity) =
    object $
      concat
        [ maybe [] (\a -> ["albedo" .= a]) albedo,
          maybe [] (\n -> ["normal" .= n]) normal,
          maybe [] (\r -> ["roughness" .= r]) roughness,
          maybe [] (\m -> ["metalness" .= m]) metalness,
          maybe [] (\ao_ -> ["ao" .= ao_]) ao,
          maybe [] (\e -> ["emissive" .= e]) emissive,
          maybe [] (\h -> ["height" .= h]) height,
          maybe [] (\o -> ["opacity" .= o]) opacity
        ]

instance FromJSON MaterialMaps where
  parseJSON = withObject "MaterialMaps" $ \o -> do
    albedo <- o .:? "albedo"
    normal <- o .:? "normal"
    roughness <- o .:? "roughness"
    metalness <- o .:? "metalness"
    ao <- o .:? "ao"
    emissive <- o .:? "emissive"
    height <- o .:? "height"
    opacity <- o .:? "opacity"
    return (MaterialMaps albedo normal roughness metalness ao emissive height opacity)

-- | SVG view box
data SVGViewBox = SVGViewBox
  { svgViewBoxX :: Double,
    svgViewBoxY :: Double,
    svgViewBoxWidth :: Double,
    svgViewBoxHeight :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON SVGViewBox where
  toJSON (SVGViewBox x y width height) =
    object
      [ "x" .= x,
        "y" .= y,
        "width" .= width,
        "height" .= height
      ]

instance FromJSON SVGViewBox where
  parseJSON = withObject "SVGViewBox" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    width <- o .: "width"
    height <- o .: "height"
    if validateFinite x && validateFinite y && validateFinite width && validateFinite height &&
       validateNonNegative width && validateNonNegative height
      then return (SVGViewBox x y width height)
      else fail "SVGViewBox: all components must be finite and width/height must be non-negative"

-- | Sprite validation metadata (stored from import validation)
data SpriteValidation = SpriteValidation
  { spriteValidationIsPowerOfTwo :: Bool,
    spriteValidationHasAlpha :: Bool,
    spriteValidationOriginalFormat :: Text,
    spriteValidationWarnings :: Maybe [Text]
  }
  deriving (Eq, Show, Generic)

instance ToJSON SpriteValidation where
  toJSON (SpriteValidation isPowerOfTwo hasAlpha originalFormat warnings) =
    object $
      concat
        [ [ "isPowerOfTwo" .= isPowerOfTwo,
            "hasAlpha" .= hasAlpha,
            "originalFormat" .= originalFormat
          ],
          maybe [] (\w -> ["warnings" .= w]) warnings
        ]

instance FromJSON SpriteValidation where
  parseJSON = withObject "SpriteValidation" $ \o -> do
    isPowerOfTwo <- o .: "isPowerOfTwo"
    hasAlpha <- o .: "hasAlpha"
    originalFormat <- o .: "originalFormat"
    warnings <- o .:? "warnings"
    return (SpriteValidation isPowerOfTwo hasAlpha originalFormat warnings)

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // asset // source
-- ════════════════════════════════════════════════════════════════════════════

-- | Asset source type
data AssetSource
  = AssetSourceComfyUINode
  | AssetSourceFile
  | AssetSourceGenerated
  | AssetSourceURL
  deriving (Eq, Show, Generic)

instance ToJSON AssetSource where
  toJSON AssetSourceComfyUINode = "comfyui_node"
  toJSON AssetSourceFile = "file"
  toJSON AssetSourceGenerated = "generated"
  toJSON AssetSourceURL = "url"

instance FromJSON AssetSource where
  parseJSON = withText "AssetSource" $ \s ->
    case s of
      "comfyui_node" -> return AssetSourceComfyUINode
      "file" -> return AssetSourceFile
      "generated" -> return AssetSourceGenerated
      "url" -> return AssetSourceURL
      _ -> fail "Invalid AssetSource"

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // asset // reference
-- ════════════════════════════════════════════════════════════════════════════

-- | Complete asset reference with all optional metadata fields
--                                                                      // note
data AssetReference = AssetReference
  { assetReferenceId :: Text,
    assetReferenceType :: AssetType,
    assetReferenceSource :: AssetSource,
    assetReferenceNodeId :: Maybe Text,
    assetReferenceWidth :: Double,
    assetReferenceHeight :: Double,
    assetReferenceData :: Text, -- Base64 or URL - always required for valid assets
    assetReferenceFilename :: Maybe Text, -- Original filename
    -- Video/Audio specific metadata
    assetReferenceFrameCount :: Maybe Double, -- Total frames in video
    assetReferenceDuration :: Maybe Double, -- Duration in seconds
    assetReferenceFPS :: Maybe Double, -- Source FPS (for video)
    assetReferenceHasAudio :: Maybe Bool, -- Video has audio track
    assetReferenceAudioChannels :: Maybe Double, -- 1=mono, 2=stereo
    assetReferenceSampleRate :: Maybe Double, -- Audio sample rate
    -- 3D Model metadata
    assetReferenceModelFormat :: Maybe ModelFormat,
    assetReferenceModelBoundingBox :: Maybe ModelBoundingBox,
    assetReferenceModelAnimations :: Maybe [Text], -- Animation clip names
    assetReferenceModelMeshCount :: Maybe Double,
    assetReferenceModelVertexCount :: Maybe Double,
    -- Point cloud metadata
    assetReferencePointCloudFormat :: Maybe PointCloudFormat,
    assetReferencePointCount :: Maybe Double,
    -- Texture metadata
    assetReferenceTextureMapType :: Maybe TextureMapType,
    assetReferenceTextureColorSpace :: Maybe TextureColorSpace,
    -- Material definition (references other texture assets)
    assetReferenceMaterialMaps :: Maybe MaterialMaps,
    --                                                                      // hdri
    assetReferenceHDRIExposure :: Maybe Double,
    assetReferenceHDRIRotation :: Maybe Double,
    --                                                                       // svg
    assetReferenceSVGPaths :: Maybe Double, -- Number of paths in SVG
    assetReferenceSVGViewBox :: Maybe SVGViewBox,
    -- Sprite sheet metadata
    assetReferenceSpriteColumns :: Maybe Double,
    assetReferenceSpriteRows :: Maybe Double,
    assetReferenceSpriteCount :: Maybe Double,
    assetReferenceSpriteFrameRate :: Maybe Double,
    -- Sprite validation metadata (stored from import validation)
    assetReferenceSpriteValidation :: Maybe SpriteValidation
  }
  deriving (Eq, Show, Generic)

instance ToJSON AssetReference where
  toJSON (AssetReference id_ typ source mNodeId w h data_ mFilename mFrameCount mDuration mFPS mHasAudio mAudioChannels mSampleRate mModelFormat mModelBoundingBox mModelAnimations mModelMeshCount mModelVertexCount mPointCloudFormat mPointCount mTextureMapType mTextureColorSpace mMaterialMaps mHDRIExposure mHDRIRotation mSVGPaths mSVGViewBox mSpriteColumns mSpriteRows mSpriteCount mSpriteFrameRate mSpriteValidation) =
    object $
      concat
        [ [ "id" .= id_,
            "type" .= typ,
            "source" .= source,
            "width" .= w,
            "height" .= h,
            "data" .= data_
          ],
          maybe [] (\n -> ["nodeId" .= n]) mNodeId,
          maybe [] (\f -> ["filename" .= f]) mFilename,
          maybe [] (\fc -> ["frameCount" .= fc]) mFrameCount,
          maybe [] (\d -> ["duration" .= d]) mDuration,
          maybe [] (\fps -> ["fps" .= fps]) mFPS,
          maybe [] (\ha -> ["hasAudio" .= ha]) mHasAudio,
          maybe [] (\ac -> ["audioChannels" .= ac]) mAudioChannels,
          maybe [] (\sr -> ["sampleRate" .= sr]) mSampleRate,
          maybe [] (\mf -> ["modelFormat" .= mf]) mModelFormat,
          maybe [] (\mbb -> ["modelBoundingBox" .= mbb]) mModelBoundingBox,
          maybe [] (\ma -> ["modelAnimations" .= ma]) mModelAnimations,
          maybe [] (\mmc -> ["modelMeshCount" .= mmc]) mModelMeshCount,
          maybe [] (\mvc -> ["modelVertexCount" .= mvc]) mModelVertexCount,
          maybe [] (\pcf -> ["pointCloudFormat" .= pcf]) mPointCloudFormat,
          maybe [] (\pc -> ["pointCount" .= pc]) mPointCount,
          maybe [] (\tmt -> ["textureMapType" .= tmt]) mTextureMapType,
          maybe [] (\tcs -> ["textureColorSpace" .= tcs]) mTextureColorSpace,
          maybe [] (\mm -> ["materialMaps" .= mm]) mMaterialMaps,
          maybe [] (\he -> ["hdriExposure" .= he]) mHDRIExposure,
          maybe [] (\hr -> ["hdriRotation" .= hr]) mHDRIRotation,
          maybe [] (\sp -> ["svgPaths" .= sp]) mSVGPaths,
          maybe [] (\svb -> ["svgViewBox" .= svb]) mSVGViewBox,
          maybe [] (\sc -> ["spriteColumns" .= sc]) mSpriteColumns,
          maybe [] (\sr -> ["spriteRows" .= sr]) mSpriteRows,
          maybe [] (\sc -> ["spriteCount" .= sc]) mSpriteCount,
          maybe [] (\sfr -> ["spriteFrameRate" .= sfr]) mSpriteFrameRate,
          maybe [] (\sv -> ["spriteValidation" .= sv]) mSpriteValidation
        ]

instance FromJSON AssetReference where
  parseJSON = withObject "AssetReference" $ \o -> do
    id_ <- o .: "id"
    typ <- o .: "type"
    source <- o .: "source"
    mNodeId <- o .:? "nodeId"
    w <- o .: "width"
    h <- o .: "height"
    data_ <- o .: "data"
    mFilename <- o .:? "filename"
    mFrameCount <- o .:? "frameCount"
    mDuration <- o .:? "duration"
    mFPS <- o .:? "fps"
    mHasAudio <- o .:? "hasAudio"
    mAudioChannels <- o .:? "audioChannels"
    mSampleRate <- o .:? "sampleRate"
    mModelFormat <- o .:? "modelFormat"
    mModelBoundingBox <- o .:? "modelBoundingBox"
    mModelAnimationsRaw <- o .:? "modelAnimations"
    mModelMeshCount <- o .:? "modelMeshCount"
    mModelVertexCount <- o .:? "modelVertexCount"
    mPointCloudFormat <- o .:? "pointCloudFormat"
    mPointCount <- o .:? "pointCount"
    mTextureMapType <- o .:? "textureMapType"
    mTextureColorSpace <- o .:? "textureColorSpace"
    mMaterialMaps <- o .:? "materialMaps"
    mHDRIExposure <- o .:? "hdriExposure"
    mHDRIRotation <- o .:? "hdriRotation"
    mSVGPaths <- o .:? "svgPaths"
    mSVGViewBox <- o .:? "svgViewBox"
    mSpriteColumns <- o .:? "spriteColumns"
    mSpriteRows <- o .:? "spriteRows"
    mSpriteCount <- o .:? "spriteCount"
    mSpriteFrameRate <- o .:? "spriteFrameRate"
    mSpriteValidation <- o .:? "spriteValidation"
    -- Validate arrays
    mModelAnimations <- case mModelAnimationsRaw of
      Nothing -> return Nothing
      Just animsRaw -> do
        anims <- case validateBoundedArray 10000 animsRaw of
          Left err -> fail (T.unpack err)
          Right a -> return a
        return (Just anims)
    -- Validate finite dimensions and optional numeric fields
    if validateFinite w && validateFinite h && validateNonNegative w && validateNonNegative h &&
       maybe True validateFinite mFrameCount &&
       maybe True validateFinite mDuration &&
       maybe True validateFinite mFPS &&
       maybe True validateFinite mAudioChannels &&
       maybe True validateFinite mSampleRate &&
       maybe True validateFinite mModelMeshCount &&
       maybe True validateFinite mModelVertexCount &&
       maybe True validateFinite mPointCount &&
       maybe True validateFinite mHDRIExposure &&
       maybe True validateFinite mHDRIRotation &&
       maybe True validateFinite mSVGPaths &&
       maybe True validateFinite mSpriteColumns &&
       maybe True validateFinite mSpriteRows &&
       maybe True validateFinite mSpriteCount &&
       maybe True validateFinite mSpriteFrameRate
      then
        return
          ( AssetReference
              id_
              typ
              source
              mNodeId
              w
              h
              data_
              mFilename
              mFrameCount
              mDuration
              mFPS
              mHasAudio
              mAudioChannels
              mSampleRate
              mModelFormat
              mModelBoundingBox
              mModelAnimations
              mModelMeshCount
              mModelVertexCount
              mPointCloudFormat
              mPointCount
              mTextureMapType
              mTextureColorSpace
              mMaterialMaps
              mHDRIExposure
              mHDRIRotation
              mSVGPaths
              mSVGViewBox
              mSpriteColumns
              mSpriteRows
              mSpriteCount
              mSpriteFrameRate
              mSpriteValidation
          )
      else fail "AssetReference: numeric values must be finite and within valid ranges"
