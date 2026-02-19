-- |
-- Test suite for Lattice.Utils.TypeGuards
--

module Lattice.Utils.TypeGuardsSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Utils.TypeGuards
import Data.Aeson (Value(..), object, (.=))
import qualified Data.Text as T

spec :: TestTree
spec = testGroup "Lattice.Utils.TypeGuards"
  [ testGroup "Primitive Guards"
    [ testCase "isObject - object" $
        isObject (object [("key", String "value")]) @?= True
    , testCase "isObject - string" $
        isObject (String "value") @?= False
    , testCase "isFiniteNumber - valid number" $
        isFiniteNumber (Number 42) @?= True
    , testCase "isFiniteNumber - string" $
        isFiniteNumber (String "42") @?= False
    , testCase "isNonEmptyString - valid string" $
        isNonEmptyString (String "hello") @?= True
    , testCase "isNonEmptyString - empty string" $
        isNonEmptyString (String "") @?= False
    , testCase "isArray - array" $
        isArray (Array []) @?= True
    , testCase "isArray - object" $
        isArray (object []) @?= False
    ]
  , testGroup "Geometry Guards"
    [ testCase "hasXY - valid Vec2" $
        hasXY (object [("x", Number 10), ("y", Number 20)]) @?= True
    , testCase "hasXY - missing y" $
        hasXY (object [("x", Number 10)]) @?= False
    , testCase "hasXYZ - valid Vec3" $
        hasXYZ (object [("x", Number 10), ("y", Number 20), ("z", Number 30)]) @?= True
    , testCase "isBoundingBox - valid box" $
        isBoundingBox (object [("x", Number 10), ("y", Number 20), ("width", Number 100), ("height", Number 200)]) @?= True
    ]
  , testGroup "Color Guards"
    [ testCase "isRGBColor - valid RGB" $
        isRGBColor (object [("r", Number 255), ("g", Number 128), ("b", Number 64)]) @?= True
    , testCase "isRGBColor - out of range" $
        isRGBColor (object [("r", Number 300), ("g", Number 128), ("b", Number 64)]) @?= False
    , testCase "isRGBAColor - valid RGBA" $
        isRGBAColor (object [("r", Number 255), ("g", Number 128), ("b", Number 64), ("a", Number 0.5)]) @?= True
    ]
  , testGroup "Array Guards"
    [ testCase "isNumberArray - valid array" $
        isNumberArray (Array [Number 1, Number 2, Number 3]) @?= True
    , testCase "isNumberArray - mixed array" $
        isNumberArray (Array [Number 1, String "two", Number 3]) @?= False
    , testCase "isVec2Array - valid array" $
        isVec2Array (Array [object [("x", Number 1), ("y", Number 2)], object [("x", Number 3), ("y", Number 4)]]) @?= True
    ]
  , testGroup "Transform Guards"
    [ testCase "hasPosition - valid position" $
        hasPosition (object [("position", object [("value", object [("x", Number 10), ("y", Number 20)])])]) @?= True
    , testCase "hasScale - valid scale" $
        hasScale (object [("scale", object [("value", object [("x", Number 1.5), ("y", Number 2.0)])])]) @?= True
    , testCase "hasRotation - valid rotation" $
        hasRotation (object [("rotation", object [("value", Number 45)])]) @?= True
    ]
  , testGroup "Layer Data Guards"
    [ testCase "hasAssetId - with assetId" $
        hasAssetId (object [("assetId", String "asset123")]) @?= True
    , testCase "hasAssetId - null assetId" $
        hasAssetId (object [("assetId", Null)]) @?= True
    , testCase "hasDimensions - valid dimensions" $
        hasDimensions (object [("width", Number 100), ("height", Number 200)]) @?= True
    , testCase "hasDimensions - zero height" $
        hasDimensions (object [("width", Number 100), ("height", Number 0)]) @?= False
    ]
  ]
