-- |
-- Module      : Lattice.State.AnimationSpec
-- Description : Test suite for animation state management
--

module Lattice.State.AnimationSpec (spec) where

import Lattice.State.Animation
  ( hasWorkArea
  , effectiveStartFrame
  , getCurrentFrame
  , getFrameCount
  , getFps
  , getEffectiveEndFrame
  , getCurrentTime
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Animation"
    [ testGroup
        "hasWorkArea"
        [ testCase "hasWorkArea - returns True when both are defined" $ do
            let result = hasWorkArea (Just 10) (Just 100)
            assertBool "Should return True" result
        , testCase "hasWorkArea - returns False when start is Nothing" $ do
            let result = hasWorkArea Nothing (Just 100)
            assertBool "Should return False" (not result)
        , testCase "hasWorkArea - returns False when end is Nothing" $ do
            let result = hasWorkArea (Just 10) Nothing
            assertBool "Should return False" (not result)
        , testCase "hasWorkArea - returns False when both are Nothing" $ do
            let result = hasWorkArea Nothing Nothing
            assertBool "Should return False" (not result)
        ]
    , testGroup
        "effectiveStartFrame"
        [ testCase "effectiveStartFrame - returns work area start when defined" $ do
            let result = effectiveStartFrame (Just 10)
            assertEqual "Should return 10" 10 result
        , testCase "effectiveStartFrame - returns 0 when Nothing" $ do
            let result = effectiveStartFrame Nothing
            assertEqual "Should return 0" 0 result
        , testCase "effectiveStartFrame - returns 0 when negative" $ do
            let result = effectiveStartFrame (Just (-5))
            assertEqual "Should return 0" 0 result
        ]
    , testGroup
        "getCurrentFrame"
        [ testCase "getCurrentFrame - returns current frame" $ do
            let result = getCurrentFrame 50
            assertEqual "Should return 50" 50 result
        ]
    , testGroup
        "getFrameCount"
        [ testCase "getFrameCount - returns frame count" $ do
            let result = getFrameCount 300
            assertEqual "Should return 300" 300 result
        ]
    , testGroup
        "getFps"
        [ testCase "getFps - returns FPS" $ do
            let result = getFps 30.0
            assertEqual "Should return 30.0" 30.0 result
        ]
    , testGroup
        "getEffectiveEndFrame"
        [ testCase "getEffectiveEndFrame - returns work area end when defined" $ do
            let result = getEffectiveEndFrame (Just 100) 300
            assertEqual "Should return 100" 100 result
        , testCase "getEffectiveEndFrame - returns frameCount - 1 when Nothing" $ do
            let result = getEffectiveEndFrame Nothing 300
            assertEqual "Should return 299" 299 result
        , testCase "getEffectiveEndFrame - returns frameCount - 1 when negative" $ do
            let result = getEffectiveEndFrame (Just (-5)) 300
            assertEqual "Should return 299" 299 result
        , testCase "getEffectiveEndFrame - handles zero frame count" $ do
            let result = getEffectiveEndFrame Nothing 0
            assertEqual "Should return 0" 0 result
        ]
    , testGroup
        "getCurrentTime"
        [ testCase "getCurrentTime - calculates time correctly" $ do
            let result = getCurrentTime 60 30.0
            assertEqual "Should return 2.0" 2.0 result
        , testCase "getCurrentTime - handles zero FPS" $ do
            let result = getCurrentTime 60 0.0
            assertEqual "Should return 0.0" 0.0 result
        , testCase "getCurrentTime - handles negative FPS" $ do
            let result = getCurrentTime 60 (-30.0)
            assertEqual "Should return 0.0" 0.0 result
        ]
    ]
