-- |
-- Module      : Lattice.Utils.InterpolationSpec
-- Description : Test suite for interpolation utilities
--

module Lattice.Utils.InterpolationSpec (spec) where

import Data.Text (Text)
import Lattice.Utils.Interpolation
  ( normalizeHexColor
  , parseHexComponent
  , interpolateColor
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual)

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: TestTree
spec =
  testGroup
    "Lattice.Utils.Interpolation"
    [ testGroup
        "normalizeHexColor"
        [ testCase "normalizeHexColor - expands #rgb to #rrggbb" $ do
            let result = normalizeHexColor "#abc"
            assertEqual "Should expand to #aabbcc" "#aabbcc" result
        , testCase "normalizeHexColor - expands #rgba to #rrggbbaa" $ do
            let result = normalizeHexColor "#abcd"
            assertEqual "Should expand to #aabbccdd" "#aabbccdd" result
        , testCase "normalizeHexColor - leaves #rrggbb unchanged" $ do
            let result = normalizeHexColor "#aabbcc"
            assertEqual "Should remain unchanged" "#aabbcc" result
        , testCase "normalizeHexColor - leaves #rrggbbaa unchanged" $ do
            let result = normalizeHexColor "#aabbccdd"
            assertEqual "Should remain unchanged" "#aabbccdd" result
        , testCase "normalizeHexColor - returns #000000 for invalid input" $ do
            let result = normalizeHexColor "invalid"
            assertEqual "Should return #000000" "#000000" result
        ]
    , testGroup
        "parseHexComponent"
        [ testCase "parseHexComponent - parses valid hex component" $ do
            let result = parseHexComponent "#aabbcc" 1 3
            assertEqual "Should parse aa as 170" 170 result
        , testCase "parseHexComponent - returns 0 for invalid component" $ do
            let result = parseHexComponent "#invalid" 1 3
            assertEqual "Should return 0" 0 result
        ]
    , testGroup
        "interpolateColor"
        [ testCase "interpolateColor - interpolates between two colors" $ do
            let result = interpolateColor "#000000" "#ffffff" 0.5
            assertEqual "Should interpolate to gray" "#808080" result
        , testCase "interpolateColor - returns first color at t=0" $ do
            let result = interpolateColor "#ff0000" "#0000ff" 0.0
            assertEqual "Should return first color" "#ff0000" result
        , testCase "interpolateColor - returns second color at t=1" $ do
            let result = interpolateColor "#ff0000" "#0000ff" 1.0
            assertEqual "Should return second color" "#0000ff" result
        , testCase "interpolateColor - handles rgba colors" $ do
            let result = interpolateColor "#ff0000ff" "#0000ff00" 0.5
            assertEqual "Should interpolate rgba" "#80808080" result
        ]
    ]
