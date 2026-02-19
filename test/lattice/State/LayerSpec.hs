-- |
-- Module      : Lattice.State.LayerSpec
-- Description : Test suite for Layer State management functions
-- 
-- Tests pure state management functions migrated from layerStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.LayerSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.State.Layer
  ( getLayerById
  , getLayerChildren
  , getLayerDescendants
  , getVisibleLayers
  , getDisplayedLayers
  , getRootLayers
  , getCameraLayers
  , getSelectedLayers
  , getSelectedLayer
  , isSplineAnimated
  , hasSplinePointKeyframes
  , samplePathPoints
  , approximateBezierLength
  , evaluateCubicBezier
  , evaluateCubicBezierDerivative
  )
import Lattice.Types.Layer
  ( Layer(..)
  , LayerType(..)
  , LayerTransform(..)
  , BlendMode(..)
  )
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  )
import Lattice.Types.Layer
  ( LayerData(..)
  )
import Lattice.Types.LayerDataSpline
  ( SplineData(..)
  , ControlPoint(..)
  , ControlPointType(..)
  , ControlPointHandle(..)
  , AnimatableControlPoint(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // test // data // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a simple test layer
createTestLayer :: Text -> LayerType -> Layer
createTestLayer layerId layerType_ =
  Layer
    { layerId = layerId
    , layerName = "Test Layer"
    , layerType = layerType_
    , layerVisible = True
    , layerLocked = False
    , layerIsolate = False
    , layerMinimized = Nothing
    , layerThreeD = False
    , layerAutoOrient = Nothing
    , layerFollowPath = Nothing
    , layerAudioPathAnimation = Nothing
    , layerMotionBlur = False
    , layerMotionBlurSettings = Nothing
    , layerFlattenTransform = Nothing
    , layerQuality = Nothing
    , layerEffectsEnabled = True
    , layerFrameBlending = Nothing
    , layerEffectLayer = False
    , layerAdjustmentLayer = False
    , layerAudioEnabled = False
    , layerLabelColor = Nothing
    , layerMaterialOptions = Nothing
    , layerStartFrame = 0.0
    , layerEndFrame = 80.0
    , layerInPoint = Nothing
    , layerOutPoint = Nothing
    , layerTimeStretch = Nothing
    , layerStretchAnchor = Nothing
    , layerParentId = Nothing
    , layerBlendMode = BlendModeNormal
    , layerOpacity = AnimatableProperty "opacity" 100.0 "number" False []
    , layerTransform = LayerTransform
        { layerTransformPosition = AnimatableProperty "position" (Vec2 0.0 0.0) "vector2" False []
        , layerTransformOrigin = Nothing
        , layerTransformAnchorPoint = Nothing
        , layerTransformScale = AnimatableProperty "scale" (Vec2 100.0 100.0) "vector2" False []
        , layerTransformPositionX = Nothing
        , layerTransformPositionY = Nothing
        , layerTransformPositionZ = Nothing
        , layerTransformScaleX = Nothing
        , layerTransformScaleY = Nothing
        , layerTransformScaleZ = Nothing
        , layerTransformRotation = AnimatableProperty "rotation" 0.0 "number" False []
        , layerTransformOrientation = Nothing
        , layerTransformRotationX = Nothing
        , layerTransformRotationY = Nothing
        , layerTransformRotationZ = Nothing
        }
    , layerAudio = Nothing
    , layerMasks = Nothing
    , layerMatteType = Nothing
    , layerMatteLayerId = Nothing
    , layerMatteCompositionId = Nothing
    , layerPreserveTransparency = False
    , layerTrackMatteType = Nothing
    , layerTrackMatteLayerId = Nothing
    , layerTrackMatteCompositionId = Nothing
    , layerProperties = []
    , layerEffects = []
    , layerLayerStyles = Nothing
    , layerData = Nothing
    }

-- | Create a test spline layer with animation
createTestSplineLayer :: Text -> Bool -> Layer
createTestSplineLayer layerId animated =
  let
    baseLayer = createTestLayer layerId LayerTypeSpline
    splineData = SplineData
      { splineDataPathData = ""
      , splineDataControlPoints = []
      , splineDataClosed = False
      , splineDataStrokeType = Nothing
      , splineDataStroke = "#ffffff"
      , splineDataStrokeGradient = Nothing
      , splineDataStrokeWidth = 1.0
      , splineDataStrokeOpacity = Nothing
      , splineDataLineCap = Nothing
      , splineDataLineJoin = Nothing
      , splineDataStrokeMiterLimit = Nothing
      , splineDataDashArray = Nothing
      , splineDataDashOffset = Nothing
      , splineDataFill = Nothing
      , splineDataFillOpacity = Nothing
      , splineDataTrimStart = Nothing
      , splineDataTrimEnd = Nothing
      , splineDataTrimOffset = Nothing
      , splineDataPathEffects = Nothing
      , splineDataAnimatedControlPoints = if animated then Just [] else Nothing
      , splineDataAnimated = if animated then Just True else Nothing
      , splineDataLOD = Nothing
      , splineDataWarpPins = Nothing
      , splineDataPuppetPins = Nothing
      , splineDataAudioReactive = Nothing
      }
  in
    baseLayer { layerData = Just (LayerDataSpline splineData) }

-- ════════════════════════════════════════════════════════════════════════════
--                                               // hierarchy // query // tests
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec = testGroup "Layer State Functions"
  [ testGroup "Hierarchy Queries"
      [ testCase "getLayerById - finds existing layer" $ do
          let layers = [createTestLayer "layer1" LayerTypeNull, createTestLayer "layer2" LayerTypeNull]
          case getLayerById layers "layer1" of
            Just layer -> layerId layer @?= "layer1"
            Nothing -> assertBool "Layer should be found" False
      
      , testCase "getLayerById - returns Nothing for non-existent layer" $ do
          let layers = [createTestLayer "layer1" LayerTypeNull]
          getLayerById layers "nonexistent" @?= Nothing
      
      , testCase "getLayerChildren - returns children of parent" $ do
          let
            parent = createTestLayer "parent" LayerTypeNull
            child1 = (createTestLayer "child1" LayerTypeNull) { layerParentId = Just "parent" }
            child2 = (createTestLayer "child2" LayerTypeNull) { layerParentId = Just "parent" }
            unrelated = createTestLayer "unrelated" LayerTypeNull
            layers = [parent, child1, child2, unrelated]
          let children = getLayerChildren layers "parent"
          length children @?= 2
          assertBool "child1 should be in children" (any ((== "child1") . layerId) children)
          assertBool "child2 should be in children" (any ((== "child2") . layerId) children)
      
      , testCase "getLayerDescendants - returns all descendants recursively" $ do
          let
            parent = createTestLayer "parent" LayerTypeNull
            child1 = (createTestLayer "child1" LayerTypeNull) { layerParentId = Just "parent" }
            grandchild = (createTestLayer "grandchild" LayerTypeNull) { layerParentId = Just "child1" }
            layers = [parent, child1, grandchild]
          let descendants = getLayerDescendants layers "parent"
          length descendants @?= 2
          assertBool "child1 should be in descendants" (any ((== "child1") . layerId) descendants)
          assertBool "grandchild should be in descendants" (any ((== "grandchild") . layerId) descendants)
      
      , testCase "getVisibleLayers - filters visible layers" $ do
          let
            visible1 = createTestLayer "visible1" LayerTypeNull
            visible2 = createTestLayer "visible2" LayerTypeNull
            hidden = (createTestLayer "hidden" LayerTypeNull) { layerVisible = False }
            layers = [visible1, visible2, hidden]
          let visible = getVisibleLayers layers
          length visible @?= 2
          assertBool "All returned layers should be visible" (all layerVisible visible)
      
      , testCase "getDisplayedLayers - respects hideMinimized flag" $ do
          let
            normal = createTestLayer "normal" LayerTypeNull
            minimized = (createTestLayer "minimized" LayerTypeNull) { layerMinimized = Just True }
            layers = [normal, minimized]
          let displayed = getDisplayedLayers layers True
          length displayed @?= 1
          assertBool "Should exclude minimized layer" (not (any ((== Just True) . layerMinimized) displayed))
      
      , testCase "getRootLayers - returns layers with no parent" $ do
          let
            root1 = createTestLayer "root1" LayerTypeNull
            root2 = createTestLayer "root2" LayerTypeNull
            child = (createTestLayer "child" LayerTypeNull) { layerParentId = Just "root1" }
            layers = [root1, root2, child]
          let roots = getRootLayers layers
          length roots @?= 2
          assertBool "All returned layers should have no parent" (all ((== Nothing) . layerParentId) roots)
      
      , testCase "getCameraLayers - filters camera layers" $ do
          let
            camera1 = createTestLayer "camera1" LayerTypeCamera
            camera2 = createTestLayer "camera2" LayerTypeCamera
            nullLayer = createTestLayer "null" LayerTypeNull
            layers = [camera1, camera2, nullLayer]
          let cameras = getCameraLayers layers
          length cameras @?= 2
          assertBool "All returned layers should be cameras" (all ((== LayerTypeCamera) . layerType) cameras)
      
      , testCase "getSelectedLayers - returns selected layers" $ do
          let
            layer1 = createTestLayer "layer1" LayerTypeNull
            layer2 = createTestLayer "layer2" LayerTypeNull
            layer3 = createTestLayer "layer3" LayerTypeNull
            layers = [layer1, layer2, layer3]
            selectedIds = HS.fromList ["layer1", "layer3"]
          let selected = getSelectedLayers layers selectedIds
          length selected @?= 2
          assertBool "layer1 should be selected" (any ((== "layer1") . layerId) selected)
          assertBool "layer3 should be selected" (any ((== "layer3") . layerId) selected)
      
      , testCase "getSelectedLayer - returns single selected layer" $ do
          let
            layer1 = createTestLayer "layer1" LayerTypeNull
            layer2 = createTestLayer "layer2" LayerTypeNull
            layers = [layer1, layer2]
            selectedIds = HS.fromList ["layer1"]
          case getSelectedLayer layers selectedIds of
            Just layer -> layerId layer @?= "layer1"
            Nothing -> assertBool "Should return layer1" False
      
      , testCase "getSelectedLayer - returns Nothing for multiple selections" $ do
          let
            layer1 = createTestLayer "layer1" LayerTypeNull
            layer2 = createTestLayer "layer2" LayerTypeNull
            layers = [layer1, layer2]
            selectedIds = HS.fromList ["layer1", "layer2"]
          getSelectedLayer layers selectedIds @?= Nothing
      ]
  
  , testGroup "Spline Queries"
      [ testCase "isSplineAnimated - returns True for animated spline" $ do
          let layer = createTestSplineLayer "spline1" True
          isSplineAnimated layer @?= True
      
      , testCase "isSplineAnimated - returns False for non-animated spline" $ do
          let layer = createTestSplineLayer "spline1" False
          isSplineAnimated layer @?= False
      
      , testCase "isSplineAnimated - returns False for non-spline layer" $ do
          let layer = createTestLayer "null" LayerTypeNull
          isSplineAnimated layer @?= False
      ]
  
  , testGroup "Path Calculations"
      [ testCase "evaluateCubicBezier - evaluates at t=0" $ do
          let
            p0 = Vec2 0.0 0.0
            p1 = Vec2 1.0 0.0
            p2 = Vec2 1.0 1.0
            p3 = Vec2 0.0 1.0
            result = evaluateCubicBezier p0 p1 p2 p3 0.0
          result @?= p0
      
      , testCase "evaluateCubicBezier - evaluates at t=1" $ do
          let
            p0 = Vec2 0.0 0.0
            p1 = Vec2 1.0 0.0
            p2 = Vec2 1.0 1.0
            p3 = Vec2 0.0 1.0
            result = evaluateCubicBezier p0 p1 p2 p3 1.0
          result @?= p3
      
      , testCase "approximateBezierLength - returns positive length" $ do
          let
            p0 = Vec2 0.0 0.0
            p1 = Vec2 1.0 0.0
            p2 = Vec2 1.0 1.0
            p3 = Vec2 0.0 1.0
            length = approximateBezierLength p0 p1 p2 p3 10
          assertBool "Length should be positive" (length > 0)
      
      , testCase "evaluateCubicBezierDerivative - returns normalized tangent" $ do
          let
            p0 = Vec2 0.0 0.0
            p1 = Vec2 1.0 0.0
            p2 = Vec2 1.0 1.0
            p3 = Vec2 0.0 1.0
            tangent = evaluateCubicBezierDerivative p0 p1 p2 p3 0.5
          -- Tangent should be normalized (length ≈ 1)
          let Vec2 tx ty = tangent
          let len = sqrt (tx * tx + ty * ty)
          assertBool "Tangent should be normalized" (abs (len - 1.0) < 0.001)
      ]
  ]
