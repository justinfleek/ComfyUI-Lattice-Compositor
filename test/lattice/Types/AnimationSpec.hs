-- |
-- Module      : Lattice.Types.AnimationSpec
-- Description : JSON roundtrip tests for Animation types
-- 
-- Tests that AnimatableProperty and related types can be serialized
-- to JSON and deserialized back correctly
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.AnimationSpec (spec) where

import Data.Aeson (encode, decode)
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertFailure, (@?=))
import Test.Tasty.QuickCheck (testProperty, (===))
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , Keyframe(..)
  , PropertyValue(..)
  , InterpolationType(..)
  , BaseInterpolationType(..)
  , EasingType(..)
  , BezierHandle(..)
  , ControlMode(..)
  , PropertyType(..)
  , validateKeyframesSorted
  , maxKeyframesPerProperty
  , maxExpressionParams
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , RGBAColor(..)
  , validateFinite
  , validateNormalized01
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec = testGroup "Lattice.Types.Animation JSON Roundtrip Tests"
  [ testGroup "AnimatableProperty"
    [ testCase "AnimatableProperty number roundtrip" $ do
        let prop = AnimatableProperty
              { animatablePropertyId = "prop-1"
              , animatablePropertyName = "test"
              , animatablePropertyType = PropertyTypeNumber
              , animatablePropertyValue = 42.0
              , animatablePropertyAnimated = False
              , animatablePropertyKeyframes = []
              , animatablePropertyGroup = Nothing
              , animatablePropertyExpression = Nothing
              }
        let json = encode prop
        let decoded = decode json :: Maybe (AnimatableProperty Double)
        assertBool "AnimatableProperty should decode" (decoded == Just prop)
    ]
  , testGroup "Keyframe"
    [ testCase "Keyframe number roundtrip" $ do
        let kf = Keyframe
              { keyframeId = "kf-1"
              , keyframeFrame = 10.0
              , keyframeValue = 50.0
              , keyframeInterpolation = InterpolationBase InterpolationLinear
              , keyframeInHandle = BezierHandle 0 0 True
              , keyframeOutHandle = BezierHandle 0 0 True
              , keyframeControlMode = ControlSmooth
              , keyframeSpatialInTangent = Nothing
              , keyframeSpatialOutTangent = Nothing
              }
        let json = encode kf
        let decoded = decode json :: Maybe (Keyframe Double)
        assertBool "Keyframe should decode" (decoded == Just kf)
    ]
  , testGroup "PropertyValue"
    [ testCase "PropertyValue number roundtrip" $ do
        let pv = PropertyValueNumber 42.0
        let json = encode pv
        let decoded = decode json :: Maybe PropertyValue
        assertBool "PropertyValue number should decode" (decoded == Just pv)
    , testCase "PropertyValue Vec2 roundtrip" $ do
        let pv = PropertyValueVec2 (Vec2 10.0 20.0)
        let json = encode pv
        let decoded = decode json :: Maybe PropertyValue
        assertBool "PropertyValue Vec2 should decode" (decoded == Just pv)
    , testCase "PropertyValue Vec3 roundtrip" $ do
        let pv = PropertyValueVec3 (Vec3 10.0 20.0 30.0)
        let json = encode pv
        let decoded = decode json :: Maybe PropertyValue
        assertBool "PropertyValue Vec3 should decode" (decoded == Just pv)
    , testCase "PropertyValue RGBA roundtrip" $ do
        let pv = PropertyValueRGBA (RGBAColor 1.0 0.5 0.0 1.0)
        let json = encode pv
        let decoded = decode json :: Maybe PropertyValue
        assertBool "PropertyValue RGBA should decode" (decoded == Just pv)
    ]
  , testGroup "InterpolationType"
    [ testCase "InterpolationType roundtrip - linear" $ do
        let it = InterpolationBase InterpolationLinear
        let json = encode it
        let decoded = decode json :: Maybe InterpolationType
        decoded @?= Just (InterpolationBase InterpolationLinear)
    , testCase "InterpolationType roundtrip - bezier" $ do
        let it = InterpolationBase InterpolationBezier
        let json = encode it
        let decoded = decode json :: Maybe InterpolationType
        decoded @?= Just (InterpolationBase InterpolationBezier)
    ]
  , testGroup "Validation Functions"
    [ testCase "validateKeyframesSorted - empty list" $
        validateKeyframesSorted [] @?= Right []
    , testCase "validateKeyframesSorted - single keyframe" $ do
        let kf = Keyframe "kf-1" 10.0 (5.0 :: Double) (InterpolationBase InterpolationLinear) (BezierHandle 0 0 True) (BezierHandle 0 0 True) ControlSmooth Nothing Nothing
        validateKeyframesSorted [kf] @?= Right [kf]
    , testCase "validateKeyframesSorted - sorted keyframes" $ do
        let kf1 = Keyframe "kf-1" 10.0 (5.0 :: Double) (InterpolationBase InterpolationLinear) (BezierHandle 0 0 True) (BezierHandle 0 0 True) ControlSmooth Nothing Nothing
        let kf2 = Keyframe "kf-2" 20.0 (10.0 :: Double) (InterpolationBase InterpolationLinear) (BezierHandle 0 0 True) (BezierHandle 0 0 True) ControlSmooth Nothing Nothing
        validateKeyframesSorted [kf1, kf2] @?= Right [kf1, kf2]
    , testCase "validateKeyframesSorted - unsorted keyframes" $ do
        let kf1 = Keyframe "kf-1" 20.0 (5.0 :: Double) (InterpolationBase InterpolationLinear) (BezierHandle 0 0 True) (BezierHandle 0 0 True) ControlSmooth Nothing Nothing
        let kf2 = Keyframe "kf-2" 10.0 (10.0 :: Double) (InterpolationBase InterpolationLinear) (BezierHandle 0 0 True) (BezierHandle 0 0 True) ControlSmooth Nothing Nothing
        case validateKeyframesSorted [kf1, kf2] of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for unsorted keyframes"
    , testCase "maxKeyframesPerProperty constant" $
        maxKeyframesPerProperty @?= 10000
    , testCase "maxExpressionParams constant" $
        maxExpressionParams @?= 1000
    ]
  ]
