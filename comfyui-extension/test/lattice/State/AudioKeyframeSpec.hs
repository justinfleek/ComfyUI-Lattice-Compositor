-- |
-- Module      : Lattice.State.AudioKeyframeSpec
-- Description : Test suite for audio keyframe state management
--

module Lattice.State.AudioKeyframeSpec (spec) where

import Lattice.State.AudioKeyframe
  ( applySmoothing
  , interpolateKeyframeValue
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual)

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: TestTree
spec =
  testGroup
    "Lattice.State.AudioKeyframe"
    [ testGroup
        "applySmoothing"
        [ testCase "applySmoothing - returns empty list for empty input" $ do
            let result = applySmoothing [] 0.5
            assertEqual "Should return empty list" [] result
        , testCase "applySmoothing - returns single element unchanged" $ do
            let result = applySmoothing [10.0] 0.5
            assertEqual "Should return single element" [10.0] result
        , testCase "applySmoothing - applies smoothing with factor 0.5" $ do
            let values = [10.0, 20.0, 30.0]
            let result = applySmoothing values 0.5
            case result of
              [] -> assertEqual "Should not be empty" False True
              (first : _) -> assertEqual "Should have correct first value" 10.0 first
            assertEqual "Should have correct length" 3 (length result)
        , testCase "applySmoothing - factor 0 returns original values" $ do
            let values = [10.0, 20.0, 30.0]
            let result = applySmoothing values 0.0
            assertEqual "Should return original values" values result
        , testCase "applySmoothing - factor 1 returns constant first value" $ do
            let values = [10.0, 20.0, 30.0]
            let result = applySmoothing values 1.0
            assertEqual "Should return constant first value" [10.0, 10.0, 10.0] result
        , testCase "applySmoothing - clamps factor to 0-1 range" $ do
            let values = [10.0, 20.0]
            let resultNegative = applySmoothing values (-0.5)
            let resultOverOne = applySmoothing values 1.5
            assertEqual "Should clamp negative factor" (applySmoothing values 0.0) resultNegative
            assertEqual "Should clamp factor > 1" (applySmoothing values 1.0) resultOverOne
        ]
    , testGroup
        "interpolateKeyframeValue"
        [ testCase "interpolateKeyframeValue - returns default for empty keyframes" $ do
            let result = interpolateKeyframeValue 10 [] 0.0
            assertEqual "Should return default" 0.0 result
        , testCase "interpolateKeyframeValue - returns exact match value" $ do
            let keyframes = [(0, 10.0), (10, 20.0), (20, 30.0)]
            let result = interpolateKeyframeValue 10 keyframes 0.0
            assertEqual "Should return exact match" 20.0 result
        , testCase "interpolateKeyframeValue - interpolates between keyframes" $ do
            let keyframes = [(0, 10.0), (20, 30.0)]
            let result = interpolateKeyframeValue 10 keyframes 0.0
            assertEqual "Should interpolate to 20.0" 20.0 result
        , testCase "interpolateKeyframeValue - returns next value when no previous" $ do
            let keyframes = [(10, 20.0), (20, 30.0)]
            let result = interpolateKeyframeValue 5 keyframes 0.0
            assertEqual "Should return next value" 20.0 result
        , testCase "interpolateKeyframeValue - returns previous value when no next" $ do
            let keyframes = [(0, 10.0), (10, 20.0)]
            let result = interpolateKeyframeValue 15 keyframes 0.0
            assertEqual "Should return previous value" 20.0 result
        , testCase "interpolateKeyframeValue - handles zero frame difference" $ do
            let keyframes = [(10, 20.0), (10, 30.0)]
            let result = interpolateKeyframeValue 10 keyframes 0.0
            assertEqual "Should return first match" 20.0 result
        , testCase "interpolateKeyframeValue - handles unsorted keyframes" $ do
            let keyframes = [(20, 30.0), (0, 10.0), (10, 20.0)]
            let result = interpolateKeyframeValue 5 keyframes 0.0
            assertEqual "Should handle unsorted keyframes" 15.0 result
        ]
    ]
