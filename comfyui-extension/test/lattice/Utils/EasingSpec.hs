-- |
-- Test suite for Lattice.Utils.Easing
--

module Lattice.Utils.EasingSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Utils.Easing

spec :: TestTree
spec = testGroup "Lattice.Utils.Easing"
  [ testGroup "Linear"
    [ testCase "linear - t=0" $
        linear 0.0 @?= 0.0
    , testCase "linear - t=1" $
        linear 1.0 @?= 1.0
    , testCase "linear - t=0.5" $
        linear 0.5 @?= 0.5
    ]
  , testGroup "Sine"
    [ testCase "easeInSine - t=0" $
        easeInSine 0.0 @?= 0.0
    , testCase "easeInSine - t=1" $
        easeInSine 1.0 @?= 1.0
    , testCase "easeOutSine - t=0" $
        easeOutSine 0.0 @?= 0.0
    , testCase "easeOutSine - t=1" $
        easeOutSine 1.0 @?= 1.0
    ]
  , testGroup "Quad"
    [ testCase "easeInQuad - t=0" $
        easeInQuad 0.0 @?= 0.0
    , testCase "easeInQuad - t=1" $
        easeInQuad 1.0 @?= 1.0
    , testCase "easeOutQuad - t=0" $
        easeOutQuad 0.0 @?= 0.0
    , testCase "easeOutQuad - t=1" $
        easeOutQuad 1.0 @?= 1.0
    ]
  , testGroup "Cubic"
    [ testCase "easeInCubic - t=0" $
        easeInCubic 0.0 @?= 0.0
    , testCase "easeInCubic - t=1" $
        easeInCubic 1.0 @?= 1.0
    ]
  , testGroup "Helper Functions"
    [ testCase "getEasing - linear" $
        getEasing "linear" 0.5 @?= 0.5
    , testCase "getEasing - unknown" $
        getEasing "unknown" 0.5 @?= 0.5  -- Falls back to linear
    , testCase "applyEasing - valid easing" $
        applyEasing 0.5 "easeInQuad" @?= 0.25
    , testCase "interpolateWithEasing - linear" $
        interpolateWithEasing 0.0 100.0 0.5 "linear" @?= 50.0
    ]
  ]
