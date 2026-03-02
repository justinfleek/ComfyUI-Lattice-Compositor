-- |
-- Test suite for Lattice.Services.VectorMath
--

module Lattice.Services.VectorMathSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.VectorMath

spec :: TestTree
spec = testGroup "Lattice.Services.VectorMath"
  [ testGroup "vectorAdd"
    [ testCase "add two vectors" $
        vectorAdd [1, 2, 3] [4, 5, 6] @?= [5, 7, 9]
    , testCase "add mismatched lengths" $
        vectorAdd [1, 2] [3, 4, 5] @?= [4, 6, 5]
    , testCase "add empty vectors" $
        vectorAdd [] [] @?= []
    ]
  , testGroup "vectorSub"
    [ testCase "subtract two vectors" $
        vectorSub [5, 7, 9] [1, 2, 3] @?= [4, 5, 6]
    , testCase "subtract mismatched lengths" $
        vectorSub [5, 6, 7] [1, 2] @?= [4, 4, 7]
    ]
  , testGroup "vectorMul"
    [ testCase "scalar times vector" $
        vectorMul (Left 2.0) (Right [1, 2, 3]) @?= [2, 4, 6]
    , testCase "vector times scalar" $
        vectorMul (Right [1, 2, 3]) (Left 3.0) @?= [3, 6, 9]
    , testCase "vector times vector" $
        vectorMul (Right [1, 2, 3]) (Right [2, 3, 4]) @?= [2, 6, 12]
    ]
  , testGroup "vectorDiv"
    [ testCase "vector divided by scalar" $
        vectorDiv (Right [4, 6, 8]) (Left 2.0) @?= [2, 3, 4]
    , testCase "scalar divided by vector" $
        vectorDiv (Left 12.0) (Right [2, 3, 4]) @?= [6, 4, 3]
    , testCase "vector divided by vector" $
        vectorDiv (Right [4, 6, 8]) (Right [2, 2, 2]) @?= [2, 3, 4]
    , testCase "division by zero protection" $
        vectorDiv (Right [1, 2, 3]) (Left 0.0) @?= [1, 2, 3]  -- Divides by 1 instead
    ]
  , testGroup "vectorNormalize"
    [ testCase "normalize unit vector" $
        vectorNormalize [1, 0, 0] @?= [1, 0, 0]
    , testCase "normalize 3-4-5 triangle" $ do
        let normalized = vectorNormalize [3, 4, 0]
        length normalized @?= 3
        abs (head normalized - 0.6) < 0.01 @?= True
        abs (normalized !! 1 - 0.8) < 0.01 @?= True
    , testCase "normalize zero vector" $
        vectorNormalize [0, 0, 0] @?= [0, 0, 0]
    ]
  , testGroup "vectorDot"
    [ testCase "dot product perpendicular" $
        vectorDot [1, 0] [0, 1] @?= 0.0
    , testCase "dot product parallel" $
        vectorDot [1, 0] [2, 0] @?= 2.0
    , testCase "dot product 3D" $
        vectorDot [1, 2, 3] [4, 5, 6] @?= 32.0  -- 1*4 + 2*5 + 3*6
    ]
  , testGroup "vectorCross"
    [ testCase "cross product i x j = k" $
        vectorCross [1, 0, 0] [0, 1, 0] @?= [0, 0, 1]
    , testCase "cross product j x i = -k" $
        vectorCross [0, 1, 0] [1, 0, 0] @?= [0, 0, -1]
    , testCase "cross product parallel vectors" $
        vectorCross [1, 2, 3] [2, 4, 6] @?= [0, 0, 0]
    ]
  , testGroup "vectorLength"
    [ testCase "length of unit vector" $
        vectorLength [1, 0, 0] Nothing @?= 1.0
    , testCase "length of 3-4-5 triangle" $
        vectorLength [3, 4, 0] Nothing @?= 5.0
    , testCase "distance between points" $
        vectorLength [0, 0] (Just [3, 4]) @?= 5.0
    , testCase "distance zero" $
        vectorLength [1, 2, 3] (Just [1, 2, 3]) @?= 0.0
    ]
  , testGroup "vectorClamp"
    [ testCase "clamp with scalar bounds" $
        vectorClamp [0, 5, 10] (Left 2.0) (Left 8.0) @?= [2, 5, 8]
    , testCase "clamp with vector bounds" $
        vectorClamp [0, 5, 10] (Right [1, 2, 3]) (Right [7, 8, 9]) @?= [1, 5, 9]
    ]
  , testGroup "noise"
    [ testCase "noise 1D deterministic" $ do
        let n1 = noise (Left 1.0)
            n2 = noise (Left 1.0)
        n1 @?= n2  -- Same input should give same output
    , testCase "noise 3D deterministic" $ do
        let n1 = noise (Right [1.0, 2.0, 3.0])
            n2 = noise (Right [1.0, 2.0, 3.0])
        n1 @?= n2
    , testCase "noise range" $ do
        let n = noise (Left 42.0)
        n >= -1 && n <= 1 @?= True
    ]
  , testGroup "degreeTrig"
    [ testCase "degreeSin 90" $
        abs (degreeSin 90 - 1.0) < 0.01 @?= True
    , testCase "degreeCos 0" $
        abs (degreeCos 0 - 1.0) < 0.01 @?= True
    , testCase "degreeTan 45" $
        abs (degreeTan 45 - 1.0) < 0.1 @?= True
    , testCase "degreeAsin 1" $
        abs (degreeAsin 1 - 90.0) < 0.01 @?= True
    , testCase "degreeAcos 0" $
        abs (degreeAcos 0 - 90.0) < 0.01 @?= True
    , testCase "degreeAtan2 1 0" $
        abs (degreeAtan2 1 0 - 90.0) < 0.01 @?= True
    ]
  ]
