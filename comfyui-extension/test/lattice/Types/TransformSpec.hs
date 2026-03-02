-- |
-- Module      : Lattice.Types.TransformSpec
-- Description : JSON roundtrip tests for Transform types
-- 
-- Tests that LayerTransform and related types can be serialized
-- to JSON and deserialized back correctly
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.TransformSpec (spec) where

import Data.Aeson (encode, decode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool)
import Lattice.Types.Transform
  ( LayerTransform(..)
  , MotionBlurType(..)
  )
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , PropertyValue(..)
  , InterpolationType(..)
  , EasingFunction(..)
  )
import Lattice.Types.Primitives
  ( Position2DOr3D(..)
  , Vec3(..)
  )

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: TestTree
spec = testGroup "Lattice.Types.Transform JSON Roundtrip Tests"
  [ testGroup "LayerTransform"
    [ testCase "LayerTransform basic roundtrip" $ do
        let pos = AnimatableProperty
              { animatablePropertyId = "pos-1"
              , animatablePropertyValue = PropertyValuePosition2DOr3D (Position2DOr3D2D 10.0 20.0)
              , animatablePropertyKeyframes = []
              , animatablePropertyInterpolation = InterpolationTypeLinear
              , animatablePropertyEasing = EasingFunctionLinear
              }
        let origin = AnimatableProperty
              { animatablePropertyId = "origin-1"
              , animatablePropertyValue = PropertyValuePosition2DOr3D (Position2DOr3D2D 0.0 0.0)
              , animatablePropertyKeyframes = []
              , animatablePropertyInterpolation = InterpolationTypeLinear
              , animatablePropertyEasing = EasingFunctionLinear
              }
        let scale = AnimatableProperty
              { animatablePropertyId = "scale-1"
              , animatablePropertyValue = PropertyValuePosition2DOr3D (Position2DOr3D3D (Vec3 100.0 100.0 100.0))
              , animatablePropertyKeyframes = []
              , animatablePropertyInterpolation = InterpolationTypeLinear
              , animatablePropertyEasing = EasingFunctionLinear
              }
        let rotation = AnimatableProperty
              { animatablePropertyId = "rot-1"
              , animatablePropertyValue = PropertyValueNumber 0.0
              , animatablePropertyKeyframes = []
              , animatablePropertyInterpolation = InterpolationTypeLinear
              , animatablePropertyEasing = EasingFunctionLinear
              }
        let transform = LayerTransform
              { layerTransformPosition = pos
              , layerTransformOrigin = origin
              , layerTransformAnchorPoint = Nothing
              , layerTransformScale = scale
              , layerTransformPositionX = Nothing
              , layerTransformPositionY = Nothing
              , layerTransformPositionZ = Nothing
              , layerTransformScaleX = Nothing
              , layerTransformScaleY = Nothing
              , layerTransformScaleZ = Nothing
              , layerTransformRotation = rotation
              , layerTransformOrientation = Nothing
              , layerTransformRotationX = Nothing
              , layerTransformRotationY = Nothing
              , layerTransformRotationZ = Nothing
              , layerTransformSeparateDimensions = Nothing
              }
        let json = encode transform
        let decoded = decode json :: Maybe LayerTransform
        assertBool "LayerTransform should decode" (decoded == Just transform)
    ]
  , testGroup "MotionBlurType"
    [ testCase "MotionBlurType roundtrip - standard" $ do
        let mbt = MotionBlurTypeStandard
        let json = encode mbt
        let decoded = decode json :: Maybe MotionBlurType
        assertBool "MotionBlurType should decode" (decoded == Just MotionBlurTypeStandard)
    ]
  ]
