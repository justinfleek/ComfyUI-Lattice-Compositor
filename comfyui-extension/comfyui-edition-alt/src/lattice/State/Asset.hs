-- |
-- Module      : Lattice.State.Asset
-- Description : Pure state management functions for asset store
-- 
-- Migrated from ui/src/stores/assetStore.ts
-- Pure query and calculation functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Asset
  ( -- Pure queries (getters)
    materialList
  , selectedMaterial
  , svgDocumentList
  , selectedSvgDocument
  , meshParticleList
  , selectedMeshParticle
  , spriteSheetList
  , selectedSpriteSheet
  , isLoading
  -- Pure calculations
  , createDefaultMaterialConfig
  -- Types
  , AssetState(..)
  , StoredMaterial(..)
  , StoredSVGDocument(..)
  , StoredMeshParticle(..)
  , StoredSpriteSheet(..)
  , PBRMaterialConfig(..)
  , TextureMaps(..)
  , Vec2(..)
  , MaterialSide(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.Aeson.Types ((.!=))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Material side
data MaterialSide
  = MaterialSideFront
  | MaterialSideBack
  | MaterialSideDouble
  deriving (Eq, Show, Generic)

instance ToJSON MaterialSide where
  toJSON MaterialSideFront = "front"
  toJSON MaterialSideBack = "back"
  toJSON MaterialSideDouble = "double"

instance FromJSON MaterialSide where
  parseJSON = withText "MaterialSide" $ \s ->
    case s of
      "front" -> return MaterialSideFront
      "back" -> return MaterialSideBack
      "double" -> return MaterialSideDouble
      _ -> fail "Invalid MaterialSide"

-- | 2D vector
data Vec2 = Vec2
  { vec2X :: Double
  , vec2Y :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Vec2 where
  toJSON (Vec2 x y) = object ["x" .= x, "y" .= y]

instance FromJSON Vec2 where
  parseJSON = withObject "Vec2" $ \o -> Vec2 <$> o .: "x" <*> o .: "y"

-- | Texture maps
data TextureMaps = TextureMaps
  { textureMapsAlbedo :: Maybe Text
  , textureMapsNormal :: Maybe Text
  , textureMapsRoughness :: Maybe Text
  , textureMapsMetalness :: Maybe Text
  , textureMapsAo :: Maybe Text
  , textureMapsEmissive :: Maybe Text
  , textureMapsHeight :: Maybe Text
  , textureMapsOpacity :: Maybe Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextureMaps where
  toJSON (TextureMaps albedo normal roughness metalness ao emissive height opacity) =
    let
      baseFields = []
      withAlbedo = case albedo of
        Just a -> ("albedo" .= a) : baseFields
        Nothing -> baseFields
      withNormal = case normal of
        Just n -> ("normal" .= n) : withAlbedo
        Nothing -> withAlbedo
      withRoughness = case roughness of
        Just r -> ("roughness" .= r) : withNormal
        Nothing -> withNormal
      withMetalness = case metalness of
        Just m -> ("metalness" .= m) : withRoughness
        Nothing -> withRoughness
      withAo = case ao of
        Just a -> ("ao" .= a) : withMetalness
        Nothing -> withMetalness
      withEmissive = case emissive of
        Just e -> ("emissive" .= e) : withAo
        Nothing -> withAo
      withHeight = case height of
        Just h -> ("height" .= h) : withEmissive
        Nothing -> withEmissive
      withOpacity = case opacity of
        Just o -> ("opacity" .= o) : withHeight
        Nothing -> withHeight
    in object withOpacity

instance FromJSON TextureMaps where
  parseJSON = withObject "TextureMaps" $ \o ->
    TextureMaps
      <$> o .:? "albedo"
      <*> o .:? "normal"
      <*> o .:? "roughness"
      <*> o .:? "metalness"
      <*> o .:? "ao"
      <*> o .:? "emissive"
      <*> o .:? "height"
      <*> o .:? "opacity"

-- | PBR Material Config
data PBRMaterialConfig = PBRMaterialConfig
  { pbrMaterialConfigId :: Text
  , pbrMaterialConfigName :: Text
  , pbrMaterialConfigColor :: Text
  , pbrMaterialConfigOpacity :: Double
  , pbrMaterialConfigTransparent :: Bool
  , pbrMaterialConfigMetalness :: Double
  , pbrMaterialConfigRoughness :: Double
  , pbrMaterialConfigEnvMapIntensity :: Double
  , pbrMaterialConfigEmissive :: Text
  , pbrMaterialConfigEmissiveIntensity :: Double
  , pbrMaterialConfigNormalScale :: Double
  , pbrMaterialConfigDisplacementScale :: Double
  , pbrMaterialConfigDisplacementBias :: Double
  , pbrMaterialConfigAoMapIntensity :: Double
  , pbrMaterialConfigMaps :: TextureMaps
  , pbrMaterialConfigTextureRepeat :: Vec2
  , pbrMaterialConfigTextureOffset :: Vec2
  , pbrMaterialConfigTextureRotation :: Double
  , pbrMaterialConfigSide :: MaterialSide
  , pbrMaterialConfigFlatShading :: Bool
  , pbrMaterialConfigWireframe :: Bool
  , pbrMaterialConfigDepthWrite :: Bool
  , pbrMaterialConfigDepthTest :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON PBRMaterialConfig where
  toJSON (PBRMaterialConfig id name color opacity transparent metalness roughness envMapIntensity emissive emissiveIntensity normalScale displacementScale displacementBias aoMapIntensity maps textureRepeat textureOffset textureRotation side flatShading wireframe depthWrite depthTest) =
    object
      [ "id" .= id
      , "name" .= name
      , "color" .= color
      , "opacity" .= opacity
      , "transparent" .= transparent
      , "metalness" .= metalness
      , "roughness" .= roughness
      , "envMapIntensity" .= envMapIntensity
      , "emissive" .= emissive
      , "emissiveIntensity" .= emissiveIntensity
      , "normalScale" .= normalScale
      , "displacementScale" .= displacementScale
      , "displacementBias" .= displacementBias
      , "aoMapIntensity" .= aoMapIntensity
      , "maps" .= maps
      , "textureRepeat" .= textureRepeat
      , "textureOffset" .= textureOffset
      , "textureRotation" .= textureRotation
      , "side" .= side
      , "flatShading" .= flatShading
      , "wireframe" .= wireframe
      , "depthWrite" .= depthWrite
      , "depthTest" .= depthTest
      ]

instance FromJSON PBRMaterialConfig where
  parseJSON = withObject "PBRMaterialConfig" $ \o ->
    PBRMaterialConfig
      <$> o .: "id"
      <*> o .: "name"
      <*> o .: "color"
      <*> o .: "opacity"
      <*> o .: "transparent"
      <*> o .: "metalness"
      <*> o .: "roughness"
      <*> o .: "envMapIntensity"
      <*> o .: "emissive"
      <*> o .: "emissiveIntensity"
      <*> o .: "normalScale"
      <*> o .: "displacementScale"
      <*> o .: "displacementBias"
      <*> o .: "aoMapIntensity"
      <*> o .: "maps"
      <*> o .: "textureRepeat"
      <*> o .: "textureOffset"
      <*> o .: "textureRotation"
      <*> o .: "side"
      <*> o .: "flatShading"
      <*> o .: "wireframe"
      <*> o .: "depthWrite"
      <*> o .: "depthTest"

-- | Stored Material
data StoredMaterial = StoredMaterial
  { storedMaterialId :: Text
  , storedMaterialName :: Text
  , storedMaterialConfig :: PBRMaterialConfig
  , storedMaterialPresetName :: Maybe Text
  , storedMaterialCreatedAt :: Int
  , storedMaterialModifiedAt :: Int
  }
  deriving (Eq, Show, Generic)

instance ToJSON StoredMaterial where
  toJSON (StoredMaterial id name config presetName createdAt modifiedAt) =
    let
      baseFields = ["id" .= id, "name" .= name, "config" .= config, "createdAt" .= createdAt, "modifiedAt" .= modifiedAt]
      withPresetName = case presetName of
        Just p -> ("presetName" .= p) : baseFields
        Nothing -> baseFields
    in object withPresetName

instance FromJSON StoredMaterial where
  parseJSON = withObject "StoredMaterial" $ \o ->
    StoredMaterial
      <$> o .: "id"
      <*> o .: "name"
      <*> o .: "config"
      <*> o .:? "presetName"
      <*> o .: "createdAt"
      <*> o .: "modifiedAt"

-- | Stored SVG Document (simplified - only fields needed for pure queries)
data StoredSVGDocument = StoredSVGDocument
  { storedSvgDocumentId :: Text
  , storedSvgDocumentName :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON StoredSVGDocument where
  toJSON (StoredSVGDocument id name) = object ["id" .= id, "name" .= name]

instance FromJSON StoredSVGDocument where
  parseJSON = withObject "StoredSVGDocument" $ \o ->
    StoredSVGDocument <$> o .: "id" <*> o .: "name"

-- | Stored Mesh Particle (simplified - only fields needed for pure queries)
data StoredMeshParticle = StoredMeshParticle
  { storedMeshParticleId :: Text
  , storedMeshParticleName :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON StoredMeshParticle where
  toJSON (StoredMeshParticle id name) = object ["id" .= id, "name" .= name]

instance FromJSON StoredMeshParticle where
  parseJSON = withObject "StoredMeshParticle" $ \o ->
    StoredMeshParticle <$> o .: "id" <*> o .: "name"

-- | Stored Sprite Sheet (simplified - only fields needed for pure queries)
data StoredSpriteSheet = StoredSpriteSheet
  { storedSpriteSheetId :: Text
  , storedSpriteSheetName :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON StoredSpriteSheet where
  toJSON (StoredSpriteSheet id name) = object ["id" .= id, "name" .= name]

instance FromJSON StoredSpriteSheet where
  parseJSON = withObject "StoredSpriteSheet" $ \o ->
    StoredSpriteSheet <$> o .: "id" <*> o .: "name"

-- | Asset State (for pure queries)
data AssetState = AssetState
  { assetStateMaterials :: HashMap Text StoredMaterial
  , assetStateSelectedMaterialId :: Maybe Text
  , assetStateSvgDocuments :: HashMap Text StoredSVGDocument
  , assetStateSelectedSvgId :: Maybe Text
  , assetStateMeshParticles :: HashMap Text StoredMeshParticle
  , assetStateSelectedMeshParticleId :: Maybe Text
  , assetStateSpriteSheets :: HashMap Text StoredSpriteSheet
  , assetStateSelectedSpriteSheetId :: Maybe Text
  , assetStateIsLoadingMaterial :: Bool
  , assetStateIsLoadingSvg :: Bool
  , assetStateIsLoadingMesh :: Bool
  , assetStateIsLoadingSpriteSheet :: Bool
  , assetStateIsLoadingEnvironment :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON AssetState where
  toJSON (AssetState materials selectedMaterialId svgDocuments selectedSvgId meshParticles selectedMeshParticleId spriteSheets selectedSpriteSheetId isLoadingMaterial isLoadingSvg isLoadingMesh isLoadingSpriteSheet isLoadingEnvironment) =
    let
      baseFields = ["materials" .= materials, "svgDocuments" .= svgDocuments, "meshParticles" .= meshParticles, "spriteSheets" .= spriteSheets, "isLoadingMaterial" .= isLoadingMaterial, "isLoadingSvg" .= isLoadingSvg, "isLoadingMesh" .= isLoadingMesh, "isLoadingSpriteSheet" .= isLoadingSpriteSheet, "isLoadingEnvironment" .= isLoadingEnvironment]
      withSelectedMaterialId = case selectedMaterialId of
        Just id -> ("selectedMaterialId" .= id) : baseFields
        Nothing -> baseFields
      withSelectedSvgId = case selectedSvgId of
        Just id -> ("selectedSvgId" .= id) : withSelectedMaterialId
        Nothing -> withSelectedMaterialId
      withSelectedMeshParticleId = case selectedMeshParticleId of
        Just id -> ("selectedMeshParticleId" .= id) : withSelectedSvgId
        Nothing -> withSelectedSvgId
      withSelectedSpriteSheetId = case selectedSpriteSheetId of
        Just id -> ("selectedSpriteSheetId" .= id) : withSelectedMeshParticleId
        Nothing -> withSelectedMeshParticleId
    in object withSelectedSpriteSheetId

instance FromJSON AssetState where
  parseJSON = withObject "AssetState" $ \o ->
    AssetState
      <$> o .:? "materials" .!= HM.empty
      <*> o .:? "selectedMaterialId"
      <*> o .:? "svgDocuments" .!= HM.empty
      <*> o .:? "selectedSvgId"
      <*> o .:? "meshParticles" .!= HM.empty
      <*> o .:? "selectedMeshParticleId"
      <*> o .:? "spriteSheets" .!= HM.empty
      <*> o .:? "selectedSpriteSheetId"
      <*> o .:? "isLoadingMaterial" .!= False
      <*> o .:? "isLoadingSvg" .!= False
      <*> o .:? "isLoadingMesh" .!= False
      <*> o .:? "isLoadingSpriteSheet" .!= False
      <*> o .:? "isLoadingEnvironment" .!= False

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // pure // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Get material list
-- Pure function: takes asset state, returns list of materials
materialList ::
  AssetState ->
  [StoredMaterial]
materialList state = HM.elems (assetStateMaterials state)

-- | Get selected material
-- Pure function: takes asset state, returns Maybe material
selectedMaterial ::
  AssetState ->
  Maybe StoredMaterial
selectedMaterial state =
  case assetStateSelectedMaterialId state of
    Just id -> HM.lookup id (assetStateMaterials state)
    Nothing -> Nothing

-- | Get SVG document list
-- Pure function: takes asset state, returns list of SVG documents
svgDocumentList ::
  AssetState ->
  [StoredSVGDocument]
svgDocumentList state = HM.elems (assetStateSvgDocuments state)

-- | Get selected SVG document
-- Pure function: takes asset state, returns Maybe SVG document
selectedSvgDocument ::
  AssetState ->
  Maybe StoredSVGDocument
selectedSvgDocument state =
  case assetStateSelectedSvgId state of
    Just id -> HM.lookup id (assetStateSvgDocuments state)
    Nothing -> Nothing

-- | Get mesh particle list
-- Pure function: takes asset state, returns list of mesh particles
meshParticleList ::
  AssetState ->
  [StoredMeshParticle]
meshParticleList state = HM.elems (assetStateMeshParticles state)

-- | Get selected mesh particle
-- Pure function: takes asset state, returns Maybe mesh particle
selectedMeshParticle ::
  AssetState ->
  Maybe StoredMeshParticle
selectedMeshParticle state =
  case assetStateSelectedMeshParticleId state of
    Just id -> HM.lookup id (assetStateMeshParticles state)
    Nothing -> Nothing

-- | Get sprite sheet list
-- Pure function: takes asset state, returns list of sprite sheets
spriteSheetList ::
  AssetState ->
  [StoredSpriteSheet]
spriteSheetList state = HM.elems (assetStateSpriteSheets state)

-- | Get selected sprite sheet
-- Pure function: takes asset state, returns Maybe sprite sheet
selectedSpriteSheet ::
  AssetState ->
  Maybe StoredSpriteSheet
selectedSpriteSheet state =
  case assetStateSelectedSpriteSheetId state of
    Just id -> HM.lookup id (assetStateSpriteSheets state)
    Nothing -> Nothing

-- | Check if any asset is loading
-- Pure function: takes asset state, returns boolean
isLoading ::
  AssetState ->
  Bool
isLoading state =
  assetStateIsLoadingMaterial state
    || assetStateIsLoadingSvg state
    || assetStateIsLoadingMesh state
    || assetStateIsLoadingSpriteSheet state
    || assetStateIsLoadingEnvironment state

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // pure // calculations
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default material config
-- Pure function: takes id and name, returns default config
-- Note: In TypeScript, this function also accepts Partial<PBRMaterialConfig> overrides.
-- For Haskell, we create the default config. Override merging can be handled on TypeScript side
-- or we can add a separate function for merging overrides later.
createDefaultMaterialConfig ::
  Text ->
  Text ->
  PBRMaterialConfig
createDefaultMaterialConfig id name =
  PBRMaterialConfig
    { pbrMaterialConfigId = id
    , pbrMaterialConfigName = name
    , pbrMaterialConfigColor = "#ffffff"
    , pbrMaterialConfigOpacity = 1.0
    , pbrMaterialConfigTransparent = False
    , pbrMaterialConfigMetalness = 0.0
    , pbrMaterialConfigRoughness = 0.5
    , pbrMaterialConfigEnvMapIntensity = 1.0
    , pbrMaterialConfigEmissive = "#000000"
    , pbrMaterialConfigEmissiveIntensity = 0.0
    , pbrMaterialConfigNormalScale = 1.0
    , pbrMaterialConfigDisplacementScale = 0.0
    , pbrMaterialConfigDisplacementBias = 0.0
    , pbrMaterialConfigAoMapIntensity = 1.0
    , pbrMaterialConfigMaps =
        TextureMaps
          { textureMapsAlbedo = Nothing
          , textureMapsNormal = Nothing
          , textureMapsRoughness = Nothing
          , textureMapsMetalness = Nothing
          , textureMapsAo = Nothing
          , textureMapsEmissive = Nothing
          , textureMapsHeight = Nothing
          , textureMapsOpacity = Nothing
          }
    , pbrMaterialConfigTextureRepeat = Vec2 {vec2X = 1.0, vec2Y = 1.0}
    , pbrMaterialConfigTextureOffset = Vec2 {vec2X = 0.0, vec2Y = 0.0}
    , pbrMaterialConfigTextureRotation = 0.0
    , pbrMaterialConfigSide = MaterialSideFront
    , pbrMaterialConfigFlatShading = False
    , pbrMaterialConfigWireframe = False
    , pbrMaterialConfigDepthWrite = True
    , pbrMaterialConfigDepthTest = True
    }
