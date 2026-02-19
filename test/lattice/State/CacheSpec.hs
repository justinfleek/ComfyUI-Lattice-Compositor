-- |
-- Module      : Lattice.State.CacheSpec
-- Description : Test suite for cache state management
--

module Lattice.State.CacheSpec (spec) where

import Data.Aeson (object, (.=), Value(..))
import Data.Text (Text)
import Lattice.State.Cache (computeProjectHash)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Cache"
    [ testGroup
        "computeProjectHash"
        [ testCase "computeProjectHash - returns consistent hash for same input" $ do
            let compId = "comp1"
            let modified = "2024-01-01T00:00:00Z"
            let layerCount = 2
            let layerIds = ["layer1", "layer2"]
            let settings = object []
            let hash1 = computeProjectHash compId modified layerCount layerIds settings
            let hash2 = computeProjectHash compId modified layerCount layerIds settings
            assertEqual "Same input should produce same hash" hash1 hash2
        , testCase "computeProjectHash - returns different hash for different layer count" $ do
            let compId = "comp1"
            let modified = "2024-01-01T00:00:00Z"
            let layerIds = ["layer1", "layer2"]
            let settings = object []
            let hash1 = computeProjectHash compId modified 2 layerIds settings
            let hash2 = computeProjectHash compId modified 3 layerIds settings
            assertEqual "Different layer count should produce different hash" False (hash1 == hash2)
        , testCase "computeProjectHash - returns different hash for different layer IDs" $ do
            let compId = "comp1"
            let modified = "2024-01-01T00:00:00Z"
            let layerCount = 2
            let settings = object []
            let hash1 = computeProjectHash compId modified layerCount ["layer1", "layer2"] settings
            let hash2 = computeProjectHash compId modified layerCount ["layer3", "layer4"] settings
            assertEqual "Different layer IDs should produce different hash" False (hash1 == hash2)
        , testCase "computeProjectHash - returns different hash for different modified timestamp" $ do
            let compId = "comp1"
            let layerCount = 2
            let layerIds = ["layer1", "layer2"]
            let settings = object []
            let hash1 = computeProjectHash compId "2024-01-01T00:00:00Z" layerCount layerIds settings
            let hash2 = computeProjectHash compId "2024-01-02T00:00:00Z" layerCount layerIds settings
            assertEqual "Different modified timestamp should produce different hash" False (hash1 == hash2)
        , testCase "computeProjectHash - handles empty composition" $ do
            let compId = "comp1"
            let modified = "2024-01-01T00:00:00Z"
            let layerCount = 0
            let layerIds = []
            let settings = object []
            let hash = computeProjectHash compId modified layerCount layerIds settings
            assertEqual "Should produce valid hash for empty composition" False (hash == "")
        , testCase "computeProjectHash - handles empty layer IDs" $ do
            let compId = "comp1"
            let modified = "2024-01-01T00:00:00Z"
            let layerCount = 0
            let layerIds = []
            let settings = object []
            let hash = computeProjectHash compId modified layerCount layerIds settings
            assertEqual "Should produce valid hash" False (hash == "")
        ]
    ]
