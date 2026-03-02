-- |
-- Test suite for Lattice.Services.CoordinateConversion
--

module Lattice.Services.CoordinateConversionSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.CoordinateConversion

-- Helper to create a simple transform
simpleTransform :: LayerTransform
simpleTransform = LayerTransform
  { layerTransformPosition = [0, 0, 0]
  , layerTransformScale = [100, 100, 100]
  , layerTransformRotation = [0, 0, 0]
  , layerTransformAnchor = [0, 0, 0]
  }

spec :: TestTree
spec = testGroup "Lattice.Services.CoordinateConversion"
  [ testGroup "lookAt"
    [ testCase "lookAt - same point" $
        lookAt [0, 0, 0] [0, 0, 0] @?= [0, 0, 0]
    , testCase "lookAt - forward along Z" $
        lookAt [0, 0, 0] [0, 0, 1] @?= [0, 0, 0]
    , testCase "lookAt - right along X" $ do
        let result = lookAt [0, 0, 0] [1, 0, 0]
        abs (head result - 0) < 0.1 @?= True  -- Pitch should be ~0
        abs (result !! 1 - 90) < 0.1 @?= True  -- Yaw should be ~90
    ]
  , testGroup "orientToPathFromTangent"
    [ testCase "orientToPath - forward tangent" $
        orientToPathFromTangent [0, 0, 1] @?= [0, 0, 0]
    , testCase "orientToPath - right tangent" $ do
        let result = orientToPathFromTangent [1, 0, 0]
        abs (result !! 1 - 90) < 0.1 @?= True  -- Yaw should be ~90
    ]
  , testGroup "toCompLocal"
    [ testCase "toCompLocal - identity transform" $
        toCompLocal [1, 2, 3] simpleTransform @?= [1, 2, 3]
    , testCase "toCompLocal - with position offset" $ do
        let transform = simpleTransform { layerTransformPosition = [10, 20, 30] }
        toCompLocal [1, 2, 3] transform @?= [11, 22, 33]
    , testCase "toCompLocal - with scale" $ do
        let transform = simpleTransform { layerTransformScale = [200, 200, 200] }
        toCompLocal [1, 2, 3] transform @?= [2, 4, 6]
    , testCase "toCompLocal - 2D point" $
        toCompLocal [1, 2] simpleTransform @?= [1, 2]
    ]
  , testGroup "fromCompLocal"
    [ testCase "fromCompLocal - identity transform" $
        fromCompLocal [1, 2, 3] simpleTransform @?= [1, 2, 3]
    , testCase "fromCompLocal - with position offset" $ do
        let transform = simpleTransform { layerTransformPosition = [10, 20, 30] }
        fromCompLocal [11, 22, 33] transform @?= [1, 2, 3]
    , testCase "fromCompLocal - with scale" $ do
        let transform = simpleTransform { layerTransformScale = [200, 200, 200] }
        fromCompLocal [2, 4, 6] transform @?= [1, 2, 3]
    , testCase "fromCompLocal - roundtrip" $ do
        let transform = simpleTransform
            { layerTransformPosition = [10, 20, 30]
            , layerTransformScale = [150, 150, 150]
            , layerTransformRotation = [45, 0, 0]
            }
            point = [5, 6, 7]
            comp = toCompLocal point transform
            back = fromCompLocal comp transform
        -- Should get back close to original (within floating point error)
        abs (head back - head point) < 0.01 @?= True
        abs (back !! 1 - point !! 1) < 0.01 @?= True
    ]
  , testGroup "toWorldLocal"
    [ testCase "toWorldLocal - 2D point becomes 3D" $
        length (toWorldLocal [1, 2] simpleTransform) @?= 3
    , testCase "toWorldLocal - 3D point unchanged" $
        length (toWorldLocal [1, 2, 3] simpleTransform) @?= 3
    ]
  , testGroup "fromWorldLocal"
    [ testCase "fromWorldLocal - 2D point becomes 3D" $
        length (fromWorldLocal [1, 2] simpleTransform) @?= 3
    , testCase "fromWorldLocal - 3D point unchanged" $
        length (fromWorldLocal [1, 2, 3] simpleTransform) @?= 3
    ]
  ]
