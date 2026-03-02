-- |
-- Module      : Lattice.Types.LayerDataSpec
-- Description : JSON roundtrip tests for LayerData types
-- 
-- Tests that simple layer data types can be serialized to JSON and
-- deserialized back correctly
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.LayerDataSpec (spec) where

import Data.Aeson (encode, decode)
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, (@?=))
import Lattice.Types.LayerData
  ( NullLayerData(..)
  , ControlLayerData(..)
  , IconShape(..)
  , EffectLayerData(..)
  , SolidLayerData(..)
  , GroupLayerData(..)
  , LightLayerData(..)
  , LightType(..)
  , FalloffType(..)
  )

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: TestTree
spec = testGroup "Lattice.Types.LayerData JSON Roundtrip Tests"
  [ testGroup "NullLayerData"
    [ testCase "NullLayerData roundtrip" $ do
        let ld = NullLayerData
        let json = encode ld
        let decoded = decode json :: Maybe NullLayerData
        decoded @?= Just NullLayerData
    ]
  , testGroup "ControlLayerData"
    [ testCase "ControlLayerData roundtrip" $ do
        let ld = ControlLayerData
        let json = encode ld
        let decoded = decode json :: Maybe ControlLayerData
        decoded @?= Just ControlLayerData
    ]
  , testGroup "EffectLayerData"
    [ testCase "EffectLayerData roundtrip" $ do
        let ld = EffectLayerData
        let json = encode ld
        let decoded = decode json :: Maybe EffectLayerData
        decoded @?= Just EffectLayerData
    ]
  , testGroup "SolidLayerData"
    [ testCase "SolidLayerData roundtrip" $ do
        let ld = SolidLayerData
              { solidLayerDataSize = Vec2 1920.0 1080.0
              , solidLayerDataColor = RGBAColor 1.0 0.0 0.0 1.0
              }
        let json = encode ld
        let decoded = decode json :: Maybe SolidLayerData
        decoded @?= Just ld
    ]
  , testGroup "GroupLayerData"
    [ testCase "GroupLayerData roundtrip" $ do
        let ld = GroupLayerData
        let json = encode ld
        let decoded = decode json :: Maybe GroupLayerData
        decoded @?= Just GroupLayerData
    ]
  , testGroup "LightLayerData"
    [ testCase "LightLayerData roundtrip" $ do
        let ld = LightLayerData
              { lightLayerDataType = "directional"
              , lightLayerDataColor = RGBAColor 1.0 1.0 1.0 1.0
              , lightLayerDataIntensity = 100.0
              , lightLayerDataPosition = Vec3 0.0 0.0 0.0
              , lightLayerDataDirection = Vec3 0.0 0.0 -1.0
              , lightLayerDataCastsShadows = True
              , lightLayerDataShadowSoftness = 50.0
              , lightLayerDataShadowColor = RGBAColor 0.0 0.0 0.0 0.5
              }
        let json = encode ld
        let decoded = decode json :: Maybe LightLayerData
        assertBool "LightLayerData should decode" (decoded == Just ld)
    ]
  ]
