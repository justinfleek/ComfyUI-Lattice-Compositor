-- |
-- Module      : Lattice.State.PhysicsSpec
-- Description : Test suite for physics state management
--

module Lattice.State.PhysicsSpec (spec) where

import Lattice.State.Physics
  ( radiansToDegrees
  , degreesToRadians
  , calculateBakeFrameRange
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Physics"
    [ testGroup
        "radiansToDegrees"
        [ testCase "radiansToDegrees - converts 0 radians to 0 degrees" $ do
            let result = radiansToDegrees 0.0
            assertEqual "Should return 0" 0.0 result
        , testCase "radiansToDegrees - converts π radians to 180 degrees" $ do
            let result = radiansToDegrees pi
            assertEqual "Should return 180" 180.0 result
        , testCase "radiansToDegrees - converts π/2 radians to 90 degrees" $ do
            let result = radiansToDegrees (pi / 2)
            assertEqual "Should return 90" 90.0 result
        , testCase "radiansToDegrees - converts 2π radians to 360 degrees" $ do
            let result = radiansToDegrees (2 * pi)
            assertEqual "Should return 360" 360.0 result
        ]
    , testGroup
        "degreesToRadians"
        [ testCase "degreesToRadians - converts 0 degrees to 0 radians" $ do
            let result = degreesToRadians 0.0
            assertEqual "Should return 0" 0.0 result
        , testCase "degreesToRadians - converts 180 degrees to π radians" $ do
            let result = degreesToRadians 180.0
            assertEqual "Should return π" pi result
        , testCase "degreesToRadians - converts 90 degrees to π/2 radians" $ do
            let result = degreesToRadians 90.0
            assertEqual "Should return π/2" (pi / 2) result
        , testCase "degreesToRadians - converts 360 degrees to 2π radians" $ do
            let result = degreesToRadians 360.0
            assertEqual "Should return 2π" (2 * pi) result
        ]
    , testGroup
        "calculateBakeFrameRange"
        [ testCase "calculateBakeFrameRange - uses defaults when Nothing" $ do
            let result = calculateBakeFrameRange Nothing Nothing 100
            assertEqual "Should return (0, 99)" (0, 99) result
        , testCase "calculateBakeFrameRange - uses provided start and end" $ do
            let result = calculateBakeFrameRange (Just 10) (Just 50) 100
            assertEqual "Should return (10, 50)" (10, 50) result
        , testCase "calculateBakeFrameRange - clamps startFrame to 0" $ do
            let result = calculateBakeFrameRange (Just (-10)) (Just 50) 100
            assertEqual "Should clamp start to 0" (0, 50) result
        , testCase "calculateBakeFrameRange - clamps endFrame to maxFrame" $ do
            let result = calculateBakeFrameRange (Just 10) (Just 150) 100
            assertEqual "Should clamp end to 99" (10, 99) result
        , testCase "calculateBakeFrameRange - ensures endFrame >= startFrame" $ do
            let result = calculateBakeFrameRange (Just 50) (Just 30) 100
            assertEqual "Should clamp end to start" (50, 50) result
        , testCase "calculateBakeFrameRange - handles zero frame count" $ do
            let result = calculateBakeFrameRange Nothing Nothing 0
            assertEqual "Should return (0, 0)" (0, 0) result
        ]
    ]
