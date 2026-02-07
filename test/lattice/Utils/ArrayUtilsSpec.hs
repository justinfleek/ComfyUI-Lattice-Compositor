-- |
-- Test suite for Lattice.Utils.ArrayUtils
--

module Lattice.Utils.ArrayUtilsSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Utils.ArrayUtils

spec :: TestTree
spec = testGroup "Lattice.Utils.ArrayUtils"
  [ testGroup "Normalize"
    [ testCase "normalize - with max value" $
        normalize [1, 2, 3] (Just 3.0) @?= [1/3, 2/3, 1.0]
    , testCase "normalize - without max value" $
        normalize [1, 2, 3] Nothing @?= [1/3, 2/3, 1.0]
    , testCase "normalize - empty array" $
        normalize [] Nothing @?= []
    ]
  , testGroup "Mean"
    [ testCase "mean - normal array" $
        mean [1, 2, 3, 4, 5] @?= 3.0
    , testCase "mean - empty array" $
        mean [] @?= 0.0
    , testCase "mean - single element" $
        mean [42.0] @?= 42.0
    ]
  , testGroup "Lerp"
    [ testCase "lerp - t=0" $
        lerp 0.0 100.0 0.0 @?= 0.0
    , testCase "lerp - t=1" $
        lerp 0.0 100.0 1.0 @?= 100.0
    , testCase "lerp - t=0.5" $
        lerp 0.0 100.0 0.5 @?= 50.0
    ]
  , testGroup "MapRange"
    [ testCase "mapRange - normal mapping" $
        mapRange 5.0 0.0 10.0 0.0 100.0 @?= 50.0
    , testCase "mapRange - at minimum" $
        mapRange 0.0 0.0 10.0 0.0 100.0 @?= 0.0
    , testCase "mapRange - at maximum" $
        mapRange 10.0 0.0 10.0 0.0 100.0 @?= 100.0
    ]
  ]
