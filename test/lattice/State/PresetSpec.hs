-- |
-- Module      : Lattice.State.PresetSpec
-- Description : Test suite for preset state management
--

module Lattice.State.PresetSpec (spec) where

import Data.Text (Text)
import Lattice.State.Preset
  ( allPresets
  , filterByCategory
  , filterParticlePresets
  , filterPathEffectPresets
  , filterCameraShakePresets
  , filterCameraTrajectoryPresets
  , filterTextStylePresets
  , filterAnimationPresets
  , searchPresets
  , filterUserPresets
  , getPresetById
  , createPresetCollection
  , PresetCategory(..)
  , Preset(..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // test // helpers
-- ════════════════════════════════════════════════════════════════════════════

createTestPreset :: Text -> PresetCategory -> Bool -> Preset
createTestPreset id_ category isBuiltIn =
  Preset
    { presetId = id_
    , presetName = "Test Preset"
    , presetCategory = category
    , presetDescription = Just "Test description"
    , presetTags = Just ["test", "preset"]
    , presetIsBuiltIn = isBuiltIn
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Preset"
    [ testGroup
        "allPresets"
        [ testCase "allPresets - combines all preset lists" $ do
            let builtInParticle = [createTestPreset "p1" PresetCategoryParticle True]
            let builtInPathEffect = [createTestPreset "pe1" PresetCategoryPathEffect True]
            let userPresets = [createTestPreset "u1" PresetCategoryParticle False]
            let result = allPresets builtInParticle builtInPathEffect userPresets
            assertEqual "Should return 3 presets" 3 (length result)
        , testCase "allPresets - handles empty lists" $ do
            let result = allPresets [] [] []
            assertEqual "Should return empty list" [] result
        ]
    , testGroup
        "filterByCategory"
        [ testCase "filterByCategory - filters particle presets" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , createTestPreset "pe1" PresetCategoryPathEffect False
                  ]
            let result = filterByCategory PresetCategoryParticle presets
            assertEqual "Should return 1 particle preset" 1 (length result)
            case result of
              [] -> assertBool "Should not be empty" False
              (p : _) -> assertEqual "Should be particle category" PresetCategoryParticle (presetCategory p)
        , testCase "filterByCategory - returns empty for non-existent category" $ do
            let presets = [createTestPreset "p1" PresetCategoryParticle False]
            let result = filterByCategory PresetCategoryPathEffect presets
            assertEqual "Should return empty list" [] result
        ]
    , testGroup
        "filterParticlePresets"
        [ testCase "filterParticlePresets - filters particle presets" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , createTestPreset "pe1" PresetCategoryPathEffect False
                  ]
            let result = filterParticlePresets presets
            assertEqual "Should return 1 particle preset" 1 (length result)
        ]
    , testGroup
        "filterPathEffectPresets"
        [ testCase "filterPathEffectPresets - filters path effect presets" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , createTestPreset "pe1" PresetCategoryPathEffect False
                  ]
            let result = filterPathEffectPresets presets
            assertEqual "Should return 1 path effect preset" 1 (length result)
        ]
    , testGroup
        "filterCameraShakePresets"
        [ testCase "filterCameraShakePresets - filters camera shake presets" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , createTestPreset "cs1" PresetCategoryCameraShake False
                  ]
            let result = filterCameraShakePresets presets
            assertEqual "Should return 1 camera shake preset" 1 (length result)
        ]
    , testGroup
        "filterCameraTrajectoryPresets"
        [ testCase "filterCameraTrajectoryPresets - filters camera trajectory presets" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , createTestPreset "ct1" PresetCategoryCameraTrajectory False
                  ]
            let result = filterCameraTrajectoryPresets presets
            assertEqual "Should return 1 camera trajectory preset" 1 (length result)
        ]
    , testGroup
        "filterTextStylePresets"
        [ testCase "filterTextStylePresets - filters text style presets" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , createTestPreset "ts1" PresetCategoryTextStyle False
                  ]
            let result = filterTextStylePresets presets
            assertEqual "Should return 1 text style preset" 1 (length result)
        ]
    , testGroup
        "filterAnimationPresets"
        [ testCase "filterAnimationPresets - filters animation presets" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , createTestPreset "a1" PresetCategoryAnimation False
                  ]
            let result = filterAnimationPresets presets
            assertEqual "Should return 1 animation preset" 1 (length result)
        ]
    , testGroup
        "searchPresets"
        [ testCase "searchPresets - searches by name" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , Preset "p2" "Other Preset" PresetCategoryParticle Nothing Nothing False
                  ]
            let result = searchPresets "Test" Nothing presets
            assertEqual "Should find 1 preset" 1 (length result)
        , testCase "searchPresets - searches by description" $ do
            let presets = [createTestPreset "p1" PresetCategoryParticle False]
            let result = searchPresets "description" Nothing presets
            assertEqual "Should find 1 preset" 1 (length result)
        , testCase "searchPresets - searches by tags" $ do
            let presets = [createTestPreset "p1" PresetCategoryParticle False]
            let result = searchPresets "test" Nothing presets
            assertEqual "Should find 1 preset" 1 (length result)
        , testCase "searchPresets - filters by category" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , createTestPreset "pe1" PresetCategoryPathEffect False
                  ]
            let result = searchPresets "Test" (Just PresetCategoryParticle) presets
            assertEqual "Should find 1 preset" 1 (length result)
        ]
    , testGroup
        "filterUserPresets"
        [ testCase "filterUserPresets - filters out built-in presets" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle True
                  , createTestPreset "u1" PresetCategoryParticle False
                  ]
            let result = filterUserPresets presets
            assertEqual "Should return 1 user preset" 1 (length result)
            case result of
              [] -> assertBool "Should not be empty" False
              (p : _) -> assertBool "Should be user preset" (not (presetIsBuiltIn p))
        ]
    , testGroup
        "getPresetById"
        [ testCase "getPresetById - returns preset when exists" $ do
            let preset = createTestPreset "p1" PresetCategoryParticle False
            let presets = [preset]
            let result = getPresetById "p1" presets
            assertBool "Should return preset" (result == Just preset)
        , testCase "getPresetById - returns Nothing for non-existent ID" $ do
            let presets = [createTestPreset "p1" PresetCategoryParticle False]
            let result = getPresetById "nonexistent" presets
            assertEqual "Should return Nothing" Nothing result
        ]
    , testGroup
        "createPresetCollection"
        [ testCase "createPresetCollection - creates collection with user presets when no IDs" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle True
                  , createTestPreset "u1" PresetCategoryParticle False
                  ]
            let result = createPresetCollection 1 Nothing presets 1234567890
            assertEqual "Should have 1 preset" 1 (length (presetCollectionPresets result))
            assertEqual "Should have correct version" 1 (presetCollectionVersion result)
        , testCase "createPresetCollection - filters by IDs when provided" $ do
            let presets =
                  [ createTestPreset "p1" PresetCategoryParticle False
                  , createTestPreset "p2" PresetCategoryParticle False
                  ]
            let result = createPresetCollection 1 (Just ["p1"]) presets 1234567890
            assertEqual "Should have 1 preset" 1 (length (presetCollectionPresets result))
        ]
    ]
