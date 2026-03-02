-- |
-- Module      : Lattice.State.SelectionSpec
-- Description : Test suite for Selection State management functions
-- 
-- Tests pure state management functions migrated from selectionStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.SelectionSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.State.Selection
  ( hasSelection
  , hasMultipleSelected
  , hasKeyframeSelection
  , hasControlPointSelection
  , singleSelectedLayerId
  , selectedControlPointCount
  , isLayerSelected
  , isKeyframeSelected
  , isControlPointSelected
  , getSelectedControlPointsForLayer
  , computeRangeSelection
  , computeLayerAboveSelection
  , computeLayerBelowSelection
  , ControlPointSelection(..)
  )

-- ============================================================================
-- TEST DATA HELPERS
-- ============================================================================

-- | Create test control point selection
createTestControlPointSelection :: Text -> Int -> Maybe Text -> ControlPointSelection
createTestControlPointSelection layerId pointIndex mGroupId =
  ControlPointSelection layerId pointIndex mGroupId

-- ============================================================================
-- TESTS
-- ============================================================================

spec :: TestTree
spec = testGroup "Selection State Functions"
  [ testGroup "Pure Queries (Getters)"
      [ testCase "hasSelection - returns True when layers selected" $ do
          let selectedIds = HS.fromList ["layer1", "layer2"]
          hasSelection selectedIds @?= True
      
      , testCase "hasSelection - returns False when no layers selected" $ do
          let selectedIds = HS.empty
          hasSelection selectedIds @?= False
      
      , testCase "hasMultipleSelected - returns True for multiple selections" $ do
          let selectedIds = HS.fromList ["layer1", "layer2"]
          hasMultipleSelected selectedIds @?= True
      
      , testCase "hasMultipleSelected - returns False for single selection" $ do
          let selectedIds = HS.fromList ["layer1"]
          hasMultipleSelected selectedIds @?= False
      
      , testCase "hasKeyframeSelection - returns True when keyframes selected" $ do
          let selectedIds = HS.fromList ["kf1", "kf2"]
          hasKeyframeSelection selectedIds @?= True
      
      , testCase "hasKeyframeSelection - returns False when no keyframes selected" $ do
          let selectedIds = HS.empty
          hasKeyframeSelection selectedIds @?= False
      
      , testCase "hasControlPointSelection - returns True when control points selected" $ do
          let points = [createTestControlPointSelection "layer1" 0 Nothing]
          hasControlPointSelection points @?= True
      
      , testCase "hasControlPointSelection - returns False when no control points selected" $ do
          let points = []
          hasControlPointSelection points @?= False
      
      , testCase "singleSelectedLayerId - returns ID for single selection" $ do
          let selectedIds = HS.fromList ["layer1"]
          singleSelectedLayerId selectedIds @?= Just "layer1"
      
      , testCase "singleSelectedLayerId - returns Nothing for multiple selections" $ do
          let selectedIds = HS.fromList ["layer1", "layer2"]
          singleSelectedLayerId selectedIds @?= Nothing
      
      , testCase "selectedControlPointCount - returns correct count" $ do
          let points = 
                [ createTestControlPointSelection "layer1" 0 Nothing
                , createTestControlPointSelection "layer1" 1 Nothing
                , createTestControlPointSelection "layer2" 0 Nothing
                ]
          selectedControlPointCount points @?= 3
      ]
  
  , testGroup "Pure Query Actions"
      [ testCase "isLayerSelected - returns True for selected layer" $ do
          let selectedIds = HS.fromList ["layer1", "layer2"]
          isLayerSelected selectedIds "layer1" @?= True
      
      , testCase "isLayerSelected - returns False for unselected layer" $ do
          let selectedIds = HS.fromList ["layer1"]
          isLayerSelected selectedIds "layer2" @?= False
      
      , testCase "isKeyframeSelected - returns True for selected keyframe" $ do
          let selectedIds = HS.fromList ["kf1", "kf2"]
          isKeyframeSelected selectedIds "kf1" @?= True
      
      , testCase "isKeyframeSelected - returns False for unselected keyframe" $ do
          let selectedIds = HS.fromList ["kf1"]
          isKeyframeSelected selectedIds "kf2" @?= False
      
      , testCase "isControlPointSelected - returns True for selected point" $ do
          let points = [createTestControlPointSelection "layer1" 0 Nothing]
          isControlPointSelected points "layer1" 0 @?= True
      
      , testCase "isControlPointSelected - returns False for unselected point" $ do
          let points = [createTestControlPointSelection "layer1" 0 Nothing]
          isControlPointSelected points "layer1" 1 @?= False
      
      , testCase "getSelectedControlPointsForLayer - filters by layer ID" $ do
          let points =
                [ createTestControlPointSelection "layer1" 0 Nothing
                , createTestControlPointSelection "layer1" 1 Nothing
                , createTestControlPointSelection "layer2" 0 Nothing
                ]
          let filtered = getSelectedControlPointsForLayer points "layer1"
          length filtered @?= 2
          assertBool "All returned points should be from layer1" 
            (all ((== "layer1") . controlPointSelectionLayerId) filtered)
      ]
  
  , testGroup "Pure Calculation Helpers"
      [ testCase "computeRangeSelection - selects range between two IDs" $ do
          let orderedIds = ["layer1", "layer2", "layer3", "layer4"]
          case computeRangeSelection "layer1" "layer3" orderedIds of
            Just result -> result @?= ["layer1", "layer2", "layer3"]
            Nothing -> assertBool "Should return range" False
      
      , testCase "computeRangeSelection - handles reversed order" $ do
          let orderedIds = ["layer1", "layer2", "layer3", "layer4"]
          case computeRangeSelection "layer3" "layer1" orderedIds of
            Just result -> result @?= ["layer1", "layer2", "layer3"]
            Nothing -> assertBool "Should return range" False
      
      , testCase "computeRangeSelection - returns Nothing for invalid IDs" $ do
          let orderedIds = ["layer1", "layer2"]
          computeRangeSelection "nonexistent" "layer1" orderedIds @?= Nothing
      
      , testCase "computeLayerAboveSelection - selects layer above" $ do
          let selectedIds = HS.fromList ["layer2"]
          let orderedIds = ["layer1", "layer2", "layer3"]
          case computeLayerAboveSelection selectedIds orderedIds of
            Just result -> result @?= "layer1"
            Nothing -> assertBool "Should return layer above" False
      
      , testCase "computeLayerAboveSelection - returns first layer when no selection" $ do
          let selectedIds = HS.empty
          let orderedIds = ["layer1", "layer2", "layer3"]
          case computeLayerAboveSelection selectedIds orderedIds of
            Just result -> result @?= "layer1"
            Nothing -> assertBool "Should return first layer" False
      
      , testCase "computeLayerAboveSelection - returns Nothing at top" $ do
          let selectedIds = HS.fromList ["layer1"]
          let orderedIds = ["layer1", "layer2", "layer3"]
          computeLayerAboveSelection selectedIds orderedIds @?= Nothing
      
      , testCase "computeLayerBelowSelection - selects layer below" $ do
          let selectedIds = HS.fromList ["layer2"]
          let orderedIds = ["layer1", "layer2", "layer3"]
          case computeLayerBelowSelection selectedIds orderedIds of
            Just result -> result @?= "layer3"
            Nothing -> assertBool "Should return layer below" False
      
      , testCase "computeLayerBelowSelection - returns last layer when no selection" $ do
          let selectedIds = HS.empty
          let orderedIds = ["layer1", "layer2", "layer3"]
          case computeLayerBelowSelection selectedIds orderedIds of
            Just result -> result @?= "layer3"
            Nothing -> assertBool "Should return last layer" False
      
      , testCase "computeLayerBelowSelection - returns Nothing at bottom" $ do
          let selectedIds = HS.fromList ["layer3"]
          let orderedIds = ["layer1", "layer2", "layer3"]
          computeLayerBelowSelection selectedIds orderedIds @?= Nothing
      ]
  ]
