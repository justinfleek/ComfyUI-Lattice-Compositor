-- |
-- Module      : Lattice.State.EffectSpec
-- Description : Test suite for effect state management
--

module Lattice.State.EffectSpec (spec) where

import Data.Aeson (Value(..), object, (.=))
import Lattice.State.Effect
  ( hasStylesInClipboard
  , getStylesFromClipboard
  , getStylePresetNames
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Effect"
    [ testGroup
        "hasStylesInClipboard"
        [ testCase "hasStylesInClipboard - returns True when clipboard has styles" $ do
            let clipboard = Just (object [("enabled", True)])
            let result = hasStylesInClipboard clipboard
            assertBool "Should return True" result
        , testCase "hasStylesInClipboard - returns False when clipboard is empty" $ do
            let result = hasStylesInClipboard Nothing
            assertBool "Should return False" (not result)
        ]
    , testGroup
        "getStylesFromClipboard"
        [ testCase "getStylesFromClipboard - returns styles when present" $ do
            let clipboard = Just (object [("enabled", True)])
            let result = getStylesFromClipboard clipboard
            assertBool "Should return styles" (result == clipboard)
        , testCase "getStylesFromClipboard - returns Nothing when empty" $ do
            let result = getStylesFromClipboard Nothing
            assertEqual "Should return Nothing" Nothing result
        ]
    , testGroup
        "getStylePresetNames"
        [ testCase "getStylePresetNames - returns all preset names" $ do
            let result = getStylePresetNames
            assertEqual "Should return 7 preset names" 7 (length result)
        , testCase "getStylePresetNames - includes expected presets" $ do
            let result = getStylePresetNames
            assertBool "Should include soft-shadow" ("soft-shadow" `elem` result)
            assertBool "Should include hard-shadow" ("hard-shadow" `elem` result)
            assertBool "Should include neon-glow" ("neon-glow" `elem` result)
        ]
    ]
