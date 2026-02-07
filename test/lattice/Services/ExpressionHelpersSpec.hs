-- |
-- Test suite for Lattice.Services.ExpressionHelpers
--

module Lattice.Services.ExpressionHelpersSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.ExpressionHelpers

spec :: TestTree
spec = testGroup "Lattice.Services.ExpressionHelpers"
  [ testGroup "subtractValues"
    [ testCase "subtract numbers" $
        subtractValues (ValueNumber 5.0) (ValueNumber 2.0) @?= ValueNumber 3.0
    , testCase "subtract arrays" $
        subtractValues (ValueArray [5, 7, 9]) (ValueArray [1, 2, 3]) @?= ValueArray [4, 5, 6]
    , testCase "subtract mismatched types" $
        subtractValues (ValueNumber 5.0) (ValueArray [1, 2]) @?= ValueNumber 0.0
    , testCase "subtract mismatched array lengths" $
        subtractValues (ValueArray [5, 6, 7]) (ValueArray [1, 2]) @?= ValueArray [4, 4, 7]
    ]
  , testGroup "addValues"
    [ testCase "add numbers" $
        addValues (ValueNumber 2.0) (ValueNumber 3.0) @?= ValueNumber 5.0
    , testCase "add arrays" $
        addValues (ValueArray [1, 2, 3]) (ValueArray [4, 5, 6]) @?= ValueArray [5, 7, 9]
    , testCase "add number to array" $
        addValues (ValueNumber 2.0) (ValueArray [1, 2]) @?= ValueNumber 2.0
    , testCase "add array to number" $
        addValues (ValueArray [1, 2]) (ValueNumber 3.0) @?= ValueNumber 3.0
    ]
  , testGroup "scaleValue"
    [ testCase "scale number" $
        scaleValue (ValueNumber 3.0) 2.0 @?= ValueNumber 6.0
    , testCase "scale array" $
        scaleValue (ValueArray [1, 2, 3]) 2.0 @?= ValueArray [2, 4, 6]
    , testCase "scale by zero" $
        scaleValue (ValueArray [1, 2, 3]) 0.0 @?= ValueArray [0, 0, 0]
    ]
  , testGroup "lerpValues"
    [ testCase "lerp numbers t=0" $
        lerpValues (ValueNumber 0.0) (ValueNumber 10.0) 0.0 @?= ValueNumber 0.0
    , testCase "lerp numbers t=1" $
        lerpValues (ValueNumber 0.0) (ValueNumber 10.0) 1.0 @?= ValueNumber 10.0
    , testCase "lerp numbers t=0.5" $
        lerpValues (ValueNumber 0.0) (ValueNumber 10.0) 0.5 @?= ValueNumber 5.0
    , testCase "lerp arrays t=0.5" $
        lerpValues (ValueArray [0, 0]) (ValueArray [10, 20]) 0.5 @?= ValueArray [5, 10]
    , testCase "lerp mismatched types" $
        lerpValues (ValueNumber 5.0) (ValueArray [1, 2]) 0.5 @?= ValueNumber 5.0
    , testCase "lerp mismatched array lengths" $
        lerpValues (ValueArray [0, 0, 0]) (ValueArray [10, 20]) 0.5 @?= ValueArray [5, 10, 0]
    ]
  ]
