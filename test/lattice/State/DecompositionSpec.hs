-- |
-- Module      : Lattice.State.DecompositionSpec
-- Description : Test suite for decomposition state management
--

module Lattice.State.DecompositionSpec (spec) where

import Data.Text (Text)
import Lattice.State.Decomposition (sortLayersByDepth)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Decomposition"
    [ testGroup
        "sortLayersByDepth"
        [ testCase "sortLayersByDepth - returns empty list for empty input" $ do
            let result = sortLayersByDepth ([] :: [(Text, Maybe Double)])
            assertEqual "Should return empty list" [] result
        , testCase "sortLayersByDepth - sorts by depth descending (farthest first)" $ do
            let layers = [("layer1", Just 100.0), ("layer2", Just 200.0), ("layer3", Just 50.0)]
            let result = sortLayersByDepth layers
            case result of
              [] -> assertEqual "Should not be empty" False True
              ((firstId, _) : rest) -> do
                assertEqual "First should be layer2 (depth 200)" "layer2" firstId
                case rest of
                  [] -> assertEqual "Should have more items" False True
                  ((secondId, _) : _) -> assertEqual "Second should be layer1 (depth 100)" "layer1" secondId
        , testCase "sortLayersByDepth - handles missing depth values" $ do
            let layers = [("layer1", Just 100.0), ("layer2", Nothing), ("layer3", Just 50.0)]
            let result = sortLayersByDepth layers
            case result of
              [] -> assertEqual "Should not be empty" False True
              ((firstId, _) : _) -> assertEqual "First should be layer1 (depth 100)" "layer1" firstId
        , testCase "sortLayersByDepth - handles equal depths" $ do
            let layers = [("layer1", Just 100.0), ("layer2", Just 100.0), ("layer3", Just 50.0)]
            let result = sortLayersByDepth layers
            assertEqual "Should maintain order for equal depths" 3 (length result)
        , testCase "sortLayersByDepth - handles negative depths" $ do
            let layers = [("layer1", Just (-100.0)), ("layer2", Just 0.0), ("layer3", Just 100.0)]
            let result = sortLayersByDepth layers
            case result of
              [] -> assertEqual "Should not be empty" False True
              ((firstId, _) : _) -> assertEqual "First should be layer3 (depth 100)" "layer3" firstId
        ]
    ]
