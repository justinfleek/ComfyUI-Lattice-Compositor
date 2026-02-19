-- |
-- Module      : Lattice.State.ProjectSpec
-- Description : Test suite for Project State management functions
-- 
-- Tests pure state management functions migrated from projectStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.ProjectSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)
import Test.Tasty.QuickCheck (testProperty, (===))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.State.Project
  ( getOpenCompositions
  , getBreadcrumbPath
  , getActiveComposition
  , getActiveCompositionLayers
  , getWidth
  , getHeight
  , getFrameCount
  , getFps
  , getDuration
  , getBackgroundColor
  , getCurrentTime
  , hasProject
  , findUsedAssetIds
  , getExtensionForAsset
  , createDefaultProject
  )
import Lattice.Types.Project
  ( LatticeProject(..)
  , ProjectMeta(..)
  , Composition(..)
  , CompositionSettings(..)
  , AssetReference(..)
  , AssetType(..)
  , AssetSource(..)
  )
import Lattice.Types.Layer
  ( Layer(..)
  , LayerType(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // test // data // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a simple test project
createTestProject :: LatticeProject
createTestProject =
  let
    mainCompId = "comp_main"
    testCompSettings = CompositionSettings
      { compositionSettingsWidth = 1920.0
      , compositionSettingsHeight = 1080.0
      , compositionSettingsFrameCount = 81.0
      , compositionSettingsFps = 16.0
      , compositionSettingsDuration = 5.0625
      , compositionSettingsBackgroundColor = "#1a1a1a"
      , compositionSettingsAutoResizeToContent = False
      , compositionSettingsFrameBlendingEnabled = False
      , compositionSettingsColorSettings = Nothing
      , compositionSettingsMotionBlur = Nothing
      , compositionSettingsShutterAngle = Nothing
      , compositionSettingsMotionBlurSamples = Nothing
      }
    testComp = Composition
      { compositionId = mainCompId
      , compositionName = "Main Comp"
      , compositionSettings = testCompSettings
      , compositionLayers = []
      , compositionCurrentFrame = 0.0
      , compositionIsNestedComp = False
      , compositionParentCompositionId = Nothing
      , compositionWorkflowId = Nothing
      , compositionWorkflowInputs = Nothing
      , compositionWorkflowOutputs = Nothing
      , compositionTemplateConfig = Nothing
      , compositionGlobalLight = Nothing
      , compositionMarkers = Nothing
      }
  in
    LatticeProject
      { latticeProjectVersion = "1.0.0"
      , latticeProjectSchemaVersion = Just 1.0
      , latticeProjectMeta = ProjectMeta
          { projectMetaName = "Test Project"
          , projectMetaCreated = "2026-01-01T00:00:00Z"
          , projectMetaModified = "2026-01-01T00:00:00Z"
          , projectMetaAuthor = Nothing
          }
      , latticeProjectCompositions = HM.singleton mainCompId testComp
      , latticeProjectMainCompositionId = mainCompId
      , latticeProjectComposition = testCompSettings
      , latticeProjectAssets = HM.empty
      , latticeProjectDataAssets = Nothing
      , latticeProjectLayers = []
      , latticeProjectCurrentFrame = 0.0
      , latticeProjectSnapConfig = Nothing
      , latticeProjectExportSettings = Nothing
      }

-- | Create a test project with multiple compositions
createMultiCompProject :: LatticeProject
createMultiCompProject =
  let
    mainCompId = "comp_main"
    nestedCompId = "comp_nested"
    
    mainCompSettings = CompositionSettings
      { compositionSettingsWidth = 1920.0
      , compositionSettingsHeight = 1080.0
      , compositionSettingsFrameCount = 81.0
      , compositionSettingsFps = 16.0
      , compositionSettingsDuration = 5.0625
      , compositionSettingsBackgroundColor = "#1a1a1a"
      , compositionSettingsAutoResizeToContent = False
      , compositionSettingsFrameBlendingEnabled = False
      , compositionSettingsColorSettings = Nothing
      , compositionSettingsMotionBlur = Nothing
      , compositionSettingsShutterAngle = Nothing
      , compositionSettingsMotionBlurSamples = Nothing
      }
    
    nestedCompSettings = CompositionSettings
      { compositionSettingsWidth = 1280.0
      , compositionSettingsHeight = 720.0
      , compositionSettingsFrameCount = 60.0
      , compositionSettingsFps = 24.0
      , compositionSettingsDuration = 2.5
      , compositionSettingsBackgroundColor = "#000000"
      , compositionSettingsAutoResizeToContent = False
      , compositionSettingsFrameBlendingEnabled = False
      , compositionSettingsColorSettings = Nothing
      , compositionSettingsMotionBlur = Nothing
      , compositionSettingsShutterAngle = Nothing
      , compositionSettingsMotionBlurSamples = Nothing
      }
    
    mainComp = Composition
      { compositionId = mainCompId
      , compositionName = "Main Comp"
      , compositionSettings = mainCompSettings
      , compositionLayers = []
      , compositionCurrentFrame = 0.0
      , compositionIsNestedComp = False
      , compositionParentCompositionId = Nothing
      , compositionWorkflowId = Nothing
      , compositionWorkflowInputs = Nothing
      , compositionWorkflowOutputs = Nothing
      , compositionTemplateConfig = Nothing
      , compositionGlobalLight = Nothing
      , compositionMarkers = Nothing
      }
    
    nestedComp = Composition
      { compositionId = nestedCompId
      , compositionName = "Nested Comp"
      , compositionSettings = nestedCompSettings
      , compositionLayers = []
      , compositionCurrentFrame = 0.0
      , compositionIsNestedComp = True
      , compositionParentCompositionId = Just mainCompId
      , compositionWorkflowId = Nothing
      , compositionWorkflowInputs = Nothing
      , compositionWorkflowOutputs = Nothing
      , compositionTemplateConfig = Nothing
      , compositionGlobalLight = Nothing
      , compositionMarkers = Nothing
      }
  in
    LatticeProject
      { latticeProjectVersion = "1.0.0"
      , latticeProjectSchemaVersion = Just 1.0
      , latticeProjectMeta = ProjectMeta
          { projectMetaName = "Multi Comp Project"
          , projectMetaCreated = "2026-01-01T00:00:00Z"
          , projectMetaModified = "2026-01-01T00:00:00Z"
          , projectMetaAuthor = Nothing
          }
      , latticeProjectCompositions = HM.fromList [(mainCompId, mainComp), (nestedCompId, nestedComp)]
      , latticeProjectMainCompositionId = mainCompId
      , latticeProjectComposition = mainCompSettings
      , latticeProjectAssets = HM.empty
      , latticeProjectDataAssets = Nothing
      , latticeProjectLayers = []
      , latticeProjectCurrentFrame = 0.0
      , latticeProjectSnapConfig = Nothing
      , latticeProjectExportSettings = Nothing
      }

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec = testGroup "Lattice.State.Project"
  [ testGroup "Composition Getters"
    [ testCase "getOpenCompositions - single composition" $ do
        let project = createTestProject
        let openIds = ["comp_main"]
        let comps = getOpenCompositions project openIds
        length comps @?= 1
        case comps of
          [comp] -> compositionName comp @?= "Main Comp"
          _ -> assertBool "Should have exactly one composition" False
    
    , testCase "getOpenCompositions - multiple compositions" $ do
        let project = createMultiCompProject
        let openIds = ["comp_main", "comp_nested"]
        let comps = getOpenCompositions project openIds
        length comps @?= 2
    
    , testCase "getOpenCompositions - invalid ID" $ do
        let project = createTestProject
        let openIds = ["nonexistent"]
        let comps = getOpenCompositions project openIds
        length comps @?= 0
    
    , testCase "getBreadcrumbPath - single breadcrumb" $ do
        let project = createTestProject
        let breadcrumbs = ["comp_main"]
        let path = getBreadcrumbPath project breadcrumbs
        length path @?= 1
        case path of
          [(id_, name)] -> do
            id_ @?= "comp_main"
            name @?= "Main Comp"
          _ -> assertBool "Should have exactly one breadcrumb" False
    
    , testCase "getBreadcrumbPath - multiple breadcrumbs" $ do
        let project = createMultiCompProject
        let breadcrumbs = ["comp_main", "comp_nested"]
        let path = getBreadcrumbPath project breadcrumbs
        length path @?= 2
    
    , testCase "getActiveComposition - valid ID" $ do
        let project = createTestProject
        let mComp = getActiveComposition project "comp_main"
        assertBool "Should return composition" (mComp /= Nothing)
        case mComp of
          Just comp -> compositionName comp @?= "Main Comp"
          Nothing -> assertBool "Should not be Nothing" False
    
    , testCase "getActiveComposition - invalid ID" $ do
        let project = createTestProject
        let mComp = getActiveComposition project "nonexistent"
        mComp @?= Nothing
    
    , testCase "getActiveCompositionLayers - valid ID" $ do
        let project = createTestProject
        let layers = getActiveCompositionLayers project "comp_main"
        length layers @?= 0  -- Empty layers in test project
    ]
  
  , testGroup "Property Getters"
    [ testCase "getWidth - valid composition" $ do
        let project = createTestProject
        let width = getWidth project "comp_main"
        width @?= 1920.0
    
    , testCase "getWidth - invalid composition (default)" $ do
        let project = createTestProject
        let width = getWidth project "nonexistent"
        width @?= 1024.0  -- Default value
    
    , testCase "getHeight - valid composition" $ do
        let project = createTestProject
        let height = getHeight project "comp_main"
        height @?= 1080.0
    
    , testCase "getHeight - invalid composition (default)" $ do
        let project = createTestProject
        let height = getHeight project "nonexistent"
        height @?= 1024.0  -- Default value
    
    , testCase "getFrameCount - valid composition" $ do
        let project = createTestProject
        let frameCount = getFrameCount project "comp_main"
        frameCount @?= 81.0
    
    , testCase "getFrameCount - invalid composition (default)" $ do
        let project = createTestProject
        let frameCount = getFrameCount project "nonexistent"
        frameCount @?= 81.0  -- Default value
    
    , testCase "getFps - valid composition" $ do
        let project = createTestProject
        let fps = getFps project "comp_main"
        fps @?= 16.0
    
    , testCase "getFps - invalid composition (default)" $ do
        let project = createTestProject
        let fps = getFps project "nonexistent"
        fps @?= 16.0  -- Default value
    
    , testCase "getDuration - valid composition" $ do
        let project = createTestProject
        let duration = getDuration project "comp_main"
        duration @?= 5.0625
    
    , testCase "getDuration - invalid composition (default)" $ do
        let project = createTestProject
        let duration = getDuration project "nonexistent"
        duration @?= 5.0  -- Default value
    
    , testCase "getBackgroundColor - valid composition" $ do
        let project = createTestProject
        let bgColor = getBackgroundColor project "comp_main"
        bgColor @?= "#1a1a1a"
    
    , testCase "getBackgroundColor - invalid composition (default)" $ do
        let project = createTestProject
        let bgColor = getBackgroundColor project "nonexistent"
        bgColor @?= "#050505"  -- Default value
    
    , testCase "getCurrentTime - valid composition" $ do
        let project = createTestProject
        let currentTime = getCurrentTime project "comp_main"
        currentTime @?= 0.0  -- currentFrame 0 / fps 16 = 0
    
    , testCase "getCurrentTime - invalid composition" $ do
        let project = createTestProject
        let currentTime = getCurrentTime project "nonexistent"
        currentTime @?= 0.0
    ]
  
  , testGroup "State Queries"
    [ testCase "hasProject - with source image" $ do
        hasProject (Just "data:image/png;base64,...") @?= True
    
    , testCase "hasProject - without source image" $ do
        hasProject Nothing @?= False
        hasProject (Just "") @?= True  -- Non-null string is truthy
    ]
  
  , testGroup "Asset Utilities"
    [ testCase "findUsedAssetIds - empty project" $ do
        let project = createTestProject
        let assetIds = findUsedAssetIds project
        length assetIds @?= 0
    
    , testCase "getExtensionForAsset - from filename" $ do
        let asset = AssetReference
              { assetReferenceId = "test-asset"
              , assetReferenceType = AssetTypeImage
              , assetReferenceSource = AssetSourceFile
              , assetReferenceNodeId = Nothing
              , assetReferenceWidth = 1920.0
              , assetReferenceHeight = 1080.0
              , assetReferenceData = "data:image/png;base64,..."
              , assetReferenceFilename = Just "test.png"
              }
        getExtensionForAsset asset @?= "png"
    
    , testCase "getExtensionForAsset - from type (image)" $ do
        let asset = AssetReference
              { assetReferenceId = "test-asset"
              , assetReferenceType = AssetTypeImage
              , assetReferenceSource = AssetSourceFile
              , assetReferenceNodeId = Nothing
              , assetReferenceWidth = 1920.0
              , assetReferenceHeight = 1080.0
              , assetReferenceData = "data:image/png;base64,..."
              , assetReferenceFilename = Nothing
              }
        getExtensionForAsset asset @?= "png"
    
    , testCase "getExtensionForAsset - from type (video)" $ do
        let asset = AssetReference
              { assetReferenceId = "test-asset"
              , assetReferenceType = AssetTypeVideo
              , assetReferenceSource = AssetSourceFile
              , assetReferenceNodeId = Nothing
              , assetReferenceWidth = 1920.0
              , assetReferenceHeight = 1080.0
              , assetReferenceData = "data:video/mp4;base64,..."
              , assetReferenceFilename = Nothing
              }
        getExtensionForAsset asset @?= "mp4"
    
    , testCase "getExtensionForAsset - from type (model)" $ do
        let asset = AssetReference
              { assetReferenceId = "test-asset"
              , assetReferenceType = AssetTypeModel
              , assetReferenceSource = AssetSourceFile
              , assetReferenceNodeId = Nothing
              , assetReferenceWidth = 1920.0
              , assetReferenceHeight = 1080.0
              , assetReferenceData = "data:model/gltf;base64,..."
              , assetReferenceFilename = Nothing
              }
        getExtensionForAsset asset @?= "glb"
    ]
  
  , testGroup "Project Creation"
    [ testCase "createDefaultProject - basic structure" $ do
        let project = createDefaultProject "comp_main"
        latticeProjectVersion project @?= "1.0.0"
        latticeProjectMainCompositionId project @?= "comp_main"
        HM.size (latticeProjectCompositions project) @?= 1
    
    , testCase "createDefaultProject - composition exists" $ do
        let project = createDefaultProject "comp_main"
        let mComp = HM.lookup "comp_main" (latticeProjectCompositions project)
        assertBool "Composition should exist" (mComp /= Nothing)
        case mComp of
          Just comp -> compositionName comp @?= "Main Comp"
          Nothing -> assertBool "Should not be Nothing" False
    
    , testCase "createDefaultProject - default settings" $ do
        let project = createDefaultProject "comp_main"
        let mComp = HM.lookup "comp_main" (latticeProjectCompositions project)
        case mComp of
          Just comp -> do
            let settings = compositionSettings comp
            compositionSettingsWidth settings @?= 1920.0
            compositionSettingsHeight settings @?= 1080.0
            compositionSettingsFrameCount settings @?= 81.0
            compositionSettingsFps settings @?= 16.0
          Nothing -> assertBool "Should not be Nothing" False
    ]
  ]
