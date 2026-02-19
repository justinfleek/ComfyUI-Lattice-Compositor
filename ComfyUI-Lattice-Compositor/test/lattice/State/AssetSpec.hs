-- |
-- Module      : Lattice.State.AssetSpec
-- Description : Test suite for Asset State management functions
-- 
-- Tests pure state management functions migrated from assetStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.AssetSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.State.Asset
  ( materialList
  , selectedMaterial
  , svgDocumentList
  , selectedSvgDocument
  , meshParticleList
  , selectedMeshParticle
  , spriteSheetList
  , selectedSpriteSheet
  , isLoading
  , createDefaultMaterialConfig
  , AssetState(..)
  , StoredMaterial(..)
  , StoredSVGDocument(..)
  , StoredMeshParticle(..)
  , StoredSpriteSheet(..)
  , PBRMaterialConfig(..)
  , TextureMaps(..)
  , Vec2(..)
  , MaterialSide(..)
  )

-- ============================================================================
-- TEST DATA HELPERS
-- ============================================================================

-- | Create test material config
createTestMaterialConfig :: Text -> Text -> PBRMaterialConfig
createTestMaterialConfig id name =
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

-- | Create test stored material
createTestStoredMaterial :: Text -> Text -> StoredMaterial
createTestStoredMaterial id name =
  StoredMaterial
    { storedMaterialId = id
    , storedMaterialName = name
    , storedMaterialConfig = createTestMaterialConfig id name
    , storedMaterialPresetName = Nothing
    , storedMaterialCreatedAt = 1000
    , storedMaterialModifiedAt = 1000
    }

-- | Create test asset state
createTestAssetState ::
  HashMap Text StoredMaterial ->
  Maybe Text ->
  HashMap Text StoredSVGDocument ->
  Maybe Text ->
  HashMap Text StoredMeshParticle ->
  Maybe Text ->
  HashMap Text StoredSpriteSheet ->
  Maybe Text ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  AssetState
createTestAssetState materials selectedMaterialId svgDocuments selectedSvgId meshParticles selectedMeshParticleId spriteSheets selectedSpriteSheetId isLoadingMaterial isLoadingSvg isLoadingMesh isLoadingSpriteSheet isLoadingEnvironment =
  AssetState
    { assetStateMaterials = materials
    , assetStateSelectedMaterialId = selectedMaterialId
    , assetStateSvgDocuments = svgDocuments
    , assetStateSelectedSvgId = selectedSvgId
    , assetStateMeshParticles = meshParticles
    , assetStateSelectedMeshParticleId = selectedMeshParticleId
    , assetStateSpriteSheets = spriteSheets
    , assetStateSelectedSpriteSheetId = selectedSpriteSheetId
    , assetStateIsLoadingMaterial = isLoadingMaterial
    , assetStateIsLoadingSvg = isLoadingSvg
    , assetStateIsLoadingMesh = isLoadingMesh
    , assetStateIsLoadingSpriteSheet = isLoadingSpriteSheet
    , assetStateIsLoadingEnvironment = isLoadingEnvironment
    }

-- ============================================================================
-- TESTS
-- ============================================================================

spec :: TestTree
spec = testGroup "Asset State Functions"
  [ testGroup "Pure Queries (Getters)"
      [ testCase "materialList - returns list of materials" $ do
          let material1 = createTestStoredMaterial (T.pack "mat1") (T.pack "Material 1")
          let material2 = createTestStoredMaterial (T.pack "mat2") (T.pack "Material 2")
          let materials = HM.fromList [(T.pack "mat1", material1), (T.pack "mat2", material2)]
          let state = createTestAssetState materials Nothing HM.empty Nothing HM.empty Nothing HM.empty Nothing False False False False False
          let result = materialList state
          length result @?= 2
      
      , testCase "selectedMaterial - returns selected material" $ do
          let material1 = createTestStoredMaterial (T.pack "mat1") (T.pack "Material 1")
          let materials = HM.fromList [(T.pack "mat1", material1)]
          let state = createTestAssetState materials (Just (T.pack "mat1")) HM.empty Nothing HM.empty Nothing HM.empty Nothing False False False False False
          case selectedMaterial state of
            Just mat -> storedMaterialId mat @?= T.pack "mat1"
            Nothing -> assertBool "Expected material" False
      
      , testCase "selectedMaterial - returns Nothing when no selection" $ do
          let state = createTestAssetState HM.empty Nothing HM.empty Nothing HM.empty Nothing HM.empty Nothing False False False False False
          selectedMaterial state @?= Nothing
      
      , testCase "isLoading - returns True when any asset is loading" $ do
          let state = createTestAssetState HM.empty Nothing HM.empty Nothing HM.empty Nothing HM.empty Nothing True False False False False
          isLoading state @?= True
      
      , testCase "isLoading - returns False when nothing is loading" $ do
          let state = createTestAssetState HM.empty Nothing HM.empty Nothing HM.empty Nothing HM.empty Nothing False False False False False
          isLoading state @?= False
      ]
  
  , testGroup "Pure Calculations"
      [ testCase "createDefaultMaterialConfig - creates default config" $ do
          let config = createDefaultMaterialConfig (T.pack "test-id") (T.pack "Test Material")
          pbrMaterialConfigId config @?= T.pack "test-id"
          pbrMaterialConfigName config @?= T.pack "Test Material"
          pbrMaterialConfigColor config @?= T.pack "#ffffff"
          pbrMaterialConfigOpacity config @?= 1.0
          pbrMaterialConfigMetalness config @?= 0.0
          pbrMaterialConfigRoughness config @?= 0.5
      ]
  ]
