-- |
-- Module      : Lattice.Types.PrimitivesSpec
-- Description : JSON roundtrip tests for Primitives types
-- 
-- Tests that all Primitives types can be serialized to JSON and
-- deserialized back to the same value (roundtrip property)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.PrimitivesSpec (spec) where

import Data.Aeson (encode, decode)
import Data.Either (isRight)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, (@?=))
import Test.Tasty.QuickCheck (testProperty, (===))
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , Position2DOr3D(..)
  , RGBAColor(..)
  , RGBA255Color(..)
  , HexColor(..)
  , ColorValue(..)
  , Rect(..)
  , EntityId(..)
  , NullableEntityId(..)
  , BlendMode(..)
  , QualityMode(..)
  , validateFinite
  , validateNormalized01
  , validatePositiveInt
  , validateNonNegativeInt
  , validateFrameNumber
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec = testGroup "Lattice.Types.Primitives JSON Roundtrip Tests"
  [ testGroup "Vec2"
    [ testProperty "Vec2 roundtrip" $ \x y ->
        let v = Vec2 x y
        in if validateFinite x && validateFinite y
          then Just v === decode (encode v)
          else True  -- Skip invalid values
    , testCase "Vec2 example" $ do
        let v = Vec2 10.5 20.3
        let json = encode v
        let decoded = decode json :: Maybe Vec2
        assertBool "Vec2 should decode" (decoded == Just v)
    ]
  , testGroup "Vec3"
    [ testProperty "Vec3 roundtrip" $ \x y z ->
        let v = Vec3 x y z
        in if validateFinite x && validateFinite y && validateFinite z
          then Just v === decode (encode v)
          else True
    , testCase "Vec3 example" $ do
        let v = Vec3 10.5 20.3 30.7
        let json = encode v
        let decoded = decode json :: Maybe Vec3
        assertBool "Vec3 should decode" (decoded == Just v)
    ]
  , testGroup "RGBAColor"
    [ testProperty "RGBAColor roundtrip" $ \r g b a ->
        let c = RGBAColor r g b a
        in if validateNormalized01 r && validateNormalized01 g &&
              validateNormalized01 b && validateNormalized01 a
          then Just c === decode (encode c)
          else True
    , testCase "RGBAColor example" $ do
        let c = RGBAColor 1.0 0.5 0.0 1.0
        let json = encode c
        let decoded = decode json :: Maybe RGBAColor
        assertBool "RGBAColor should decode" (decoded == Just c)
    ]
  , testGroup "BlendMode"
    [ testCase "BlendMode roundtrip - normal" $ do
        let bm = BlendModeNormal
        let json = encode bm
        let decoded = decode json :: Maybe BlendMode
        decoded @?= Just BlendModeNormal
    , testCase "BlendMode roundtrip - multiply" $ do
        let bm = BlendModeMultiply
        let json = encode bm
        let decoded = decode json :: Maybe BlendMode
        decoded @?= Just BlendModeMultiply
    ]
  , testGroup "EntityId"
    [ testCase "EntityId roundtrip" $ do
        let eid = EntityId "test-id-123"
        let json = encode eid
        let decoded = decode json :: Maybe EntityId
        decoded @?= Just (EntityId "test-id-123")
    ]
  , testGroup "Rect"
    [ testProperty "Rect roundtrip" $ \x y w h ->
        let r = Rect x y w h
        in if validateFinite x && validateFinite y &&
              validateFinite w && validateFinite h &&
              validateFinite w && validateFinite h
          then Just r === decode (encode r)
          else True
    , testCase "Rect example" $ do
        let r = Rect 0.0 0.0 1920.0 1080.0
        let json = encode r
        let decoded = decode json :: Maybe Rect
        assertBool "Rect should decode" (decoded == Just r)
    ]
  , testGroup "Integer Validation"
    [ testCase "validatePositiveInt - positive" $
        validatePositiveInt 5 @?= True
    , testCase "validatePositiveInt - zero" $
        validatePositiveInt 0 @?= False
    , testCase "validatePositiveInt - negative" $
        validatePositiveInt (-1) @?= False
    , testCase "validateNonNegativeInt - positive" $
        validateNonNegativeInt 5 @?= True
    , testCase "validateNonNegativeInt - zero" $
        validateNonNegativeInt 0 @?= True
    , testCase "validateNonNegativeInt - negative" $
        validateNonNegativeInt (-1) @?= False
    , testCase "validateFrameNumber - positive" $
        validateFrameNumber 100 @?= True
    , testCase "validateFrameNumber - zero" $
        validateFrameNumber 0 @?= True
    , testCase "validateFrameNumber - negative" $
        validateFrameNumber (-1) @?= False
    ]
  ]
