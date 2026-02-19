-- |
-- Module      : Lattice.State.VideoSpec
-- Description : Test suite for video state management
--

module Lattice.State.VideoSpec (spec) where

import Lattice.State.Video
  ( calculateTimeStretch
  , calculateVideoFrameCount
  , calculateStretchedDuration
  , checkFpsMismatch
  , calculateVideoOutPoint
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Video"
    [ testGroup
        "calculateTimeStretch"
        [ testCase "calculateTimeStretch - 30fps video, 24fps comp = 125%" $ do
            let result = calculateTimeStretch 30.0 24.0
            assertEqual "Should calculate 125%" 125.0 result
        , testCase "calculateTimeStretch - 24fps video, 30fps comp = 80%" $ do
            let result = calculateTimeStretch 24.0 30.0
            assertEqual "Should calculate 80%" 80.0 result
        , testCase "calculateTimeStretch - same fps = 100%" $ do
            let result = calculateTimeStretch 24.0 24.0
            assertEqual "Should calculate 100%" 100.0 result
        , testCase "calculateTimeStretch - handles zero fps" $ do
            let result = calculateTimeStretch 30.0 0.0
            assertEqual "Should return 100% for zero fps" 100.0 result
        ]
    , testGroup
        "calculateVideoFrameCount"
        [ testCase "calculateVideoFrameCount - 1 second at 24fps = 24 frames" $ do
            let result = calculateVideoFrameCount 1.0 24.0
            assertEqual "Should calculate 24 frames" 24 result
        , testCase "calculateVideoFrameCount - 2.5 seconds at 30fps = 75 frames" $ do
            let result = calculateVideoFrameCount 2.5 30.0
            assertEqual "Should calculate 75 frames" 75 result
        , testCase "calculateVideoFrameCount - handles zero duration" $ do
            let result = calculateVideoFrameCount 0.0 24.0
            assertEqual "Should return 0 frames" 0 result
        , testCase "calculateVideoFrameCount - handles zero fps" $ do
            let result = calculateVideoFrameCount 1.0 0.0
            assertEqual "Should return 0 frames" 0 result
        ]
    , testGroup
        "calculateStretchedDuration"
        [ testCase "calculateStretchedDuration - 1s video at 30fps, conformed to 24fps = 1.25s" $ do
            let result = calculateStretchedDuration 1.0 30.0 24.0
            assertEqual "Should calculate 1.25s" 1.25 result
        , testCase "calculateStretchedDuration - 1s video at 24fps, conformed to 30fps = 0.8s" $ do
            let result = calculateStretchedDuration 1.0 24.0 30.0
            assertEqual "Should calculate 0.8s" 0.8 result
        , testCase "calculateStretchedDuration - same fps = same duration" $ do
            let result = calculateStretchedDuration 1.0 24.0 24.0
            assertEqual "Should return same duration" 1.0 result
        ]
    , testGroup
        "checkFpsMismatch"
        [ testCase "checkFpsMismatch - 30fps vs 24fps with 0.5 threshold = True" $ do
            let result = checkFpsMismatch 30.0 24.0 0.5
            assertBool "Should detect mismatch" result
        , testCase "checkFpsMismatch - 24.1fps vs 24fps with 0.5 threshold = False" $ do
            let result = checkFpsMismatch 24.1 24.0 0.5
            assertBool "Should not detect mismatch" (not result)
        , testCase "checkFpsMismatch - same fps = False" $ do
            let result = checkFpsMismatch 24.0 24.0 0.5
            assertBool "Should not detect mismatch" (not result)
        , testCase "checkFpsMismatch - exactly at threshold = False" $ do
            let result = checkFpsMismatch 24.5 24.0 0.5
            assertBool "Should not detect mismatch at threshold" (not result)
        ]
    , testGroup
        "calculateVideoOutPoint"
        [ testCase "calculateVideoOutPoint - video 100 frames, comp 200 frames = 99" $ do
            let result = calculateVideoOutPoint 100 200
            assertEqual "Should return 99" 99 result
        , testCase "calculateVideoOutPoint - video 200 frames, comp 100 frames = 99" $ do
            let result = calculateVideoOutPoint 200 100
            assertEqual "Should return 99" 99 result
        , testCase "calculateVideoOutPoint - same frame count = frameCount - 1" $ do
            let result = calculateVideoOutPoint 100 100
            assertEqual "Should return 99" 99 result
        , testCase "calculateVideoOutPoint - handles zero frames" $ do
            let result = calculateVideoOutPoint 0 100
            assertEqual "Should return 0" 0 result
        ]
    ]
