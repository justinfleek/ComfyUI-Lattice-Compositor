-- |
-- Module      : Lattice.Services.TimelineSnapSpec
-- Description : Test suite for timeline snap service
--

module Lattice.Services.TimelineSnapSpec (spec) where

import Data.Text (Text)
import Lattice.Services.TimelineSnap
  ( getBeatFrames
  , getPeakFrames
  , isNearBeat
  , getSnapColor
  , AudioAnalysis(..)
  , PeakData(..)
  , SnapType(..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.Services.TimelineSnap"
    [ testGroup
        "getBeatFrames"
        [ testCase "getBeatFrames - returns onsets when audio analysis present" $ do
            let analysis = AudioAnalysis [10.0, 20.0, 30.0]
            let result = getBeatFrames (Just analysis)
            assertEqual "Should return onsets" [10.0, 20.0, 30.0] result
        , testCase "getBeatFrames - returns empty list when audio analysis is Nothing" $ do
            let result = getBeatFrames Nothing
            assertEqual "Should return empty list" [] result
        ]
    , testGroup
        "getPeakFrames"
        [ testCase "getPeakFrames - returns indices when peak data present" $ do
            let peakData = PeakData [5.0, 15.0, 25.0]
            let result = getPeakFrames (Just peakData)
            assertEqual "Should return indices" [5.0, 15.0, 25.0] result
        , testCase "getPeakFrames - returns empty list when peak data is Nothing" $ do
            let result = getPeakFrames Nothing
            assertEqual "Should return empty list" [] result
        ]
    , testGroup
        "isNearBeat"
        [ testCase "isNearBeat - returns True when frame is near beat" $ do
            let analysis = AudioAnalysis [10.0, 20.0, 30.0]
            let result = isNearBeat 12.0 (Just analysis) 3.0
            assertBool "Should return True" result
        , testCase "isNearBeat - returns False when frame is far from beat" $ do
            let analysis = AudioAnalysis [10.0, 20.0, 30.0]
            let result = isNearBeat 50.0 (Just analysis) 3.0
            assertBool "Should return False" (not result)
        , testCase "isNearBeat - returns False when audio analysis is Nothing" $ do
            let result = isNearBeat 10.0 Nothing 3.0
            assertBool "Should return False" (not result)
        ]
    , testGroup
        "getSnapColor"
        [ testCase "getSnapColor - returns correct color for frame" $ do
            let result = getSnapColor SnapTypeFrame
            assertEqual "Should return #666" "#666" result
        , testCase "getSnapColor - returns correct color for keyframe" $ do
            let result = getSnapColor SnapTypeKeyframe
            assertEqual "Should return #7c9cff" "#7c9cff" result
        , testCase "getSnapColor - returns correct color for beat" $ do
            let result = getSnapColor SnapTypeBeat
            assertEqual "Should return #ffc107" "#ffc107" result
        , testCase "getSnapColor - returns correct color for playhead" $ do
            let result = getSnapColor SnapTypePlayhead
            assertEqual "Should return #ff4444" "#ff4444" result
        ]
    ]
