-- |
-- Module      : Lattice.State.LayerDefaultsSpec
-- Description : Test suite for layer defaults state management
--

module Lattice.State.LayerDefaultsSpec (spec) where

import Lattice.State.LayerDefaults
  ( createDefaultTPoseKeypoints
  , Keypoint(..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.LayerDefaults"
    [ testGroup
        "createDefaultTPoseKeypoints"
        [ testCase "createDefaultTPoseKeypoints - returns exactly 18 keypoints" $ do
            let result = createDefaultTPoseKeypoints
            assertEqual "Should return 18 keypoints" 18 (length result)
        , testCase "createDefaultTPoseKeypoints - all keypoints have confidence 1.0" $ do
            let result = createDefaultTPoseKeypoints
            let allConfidenceOne = all (\k -> keypointConfidence k == 1.0) result
            assertBool "All keypoints should have confidence 1.0" allConfidenceOne
        , testCase "createDefaultTPoseKeypoints - all coordinates in normalized range" $ do
            let result = createDefaultTPoseKeypoints
            let allInRange = all (\k -> keypointX k >= 0.0 && keypointX k <= 1.0 && keypointY k >= 0.0 && keypointY k <= 1.0) result
            assertBool "All coordinates should be in normalized range (0-1)" allInRange
        , testCase "createDefaultTPoseKeypoints - nose keypoint at correct position" $ do
            let result = createDefaultTPoseKeypoints
            case result of
              [] -> assertBool "Should have keypoints" False
              (nose : _) -> do
                assertEqual "Nose x should be 0.5" 0.5 (keypointX nose)
                assertEqual "Nose y should be 0.1" 0.1 (keypointY nose)
        , testCase "createDefaultTPoseKeypoints - neck keypoint at correct position" $ do
            let result = createDefaultTPoseKeypoints
            case result of
              [] -> assertBool "Should have keypoints" False
              (_ : neck : _) -> do
                assertEqual "Neck x should be 0.5" 0.5 (keypointX neck)
                assertEqual "Neck y should be 0.2" 0.2 (keypointY neck)
        ]
    ]
