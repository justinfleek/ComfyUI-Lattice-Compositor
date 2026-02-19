-- |
-- Module      : Lattice.State.UISpec
-- Description : Test suite for UI State management functions
-- 
-- Tests pure state management functions migrated from uiStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.UISpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Lattice.State.UI
  ( isCurveEditorVisible
  , shouldHideMinimizedLayers
  , UIState(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // test // data // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Create test UI state
createTestUIState :: Bool -> Bool -> UIState
createTestUIState curveEditorVisible hideMinimizedLayers =
  UIState
    { uiStateCurveEditorVisible = curveEditorVisible
    , uiStateHideMinimizedLayers = hideMinimizedLayers
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // tests
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec = testGroup "UI State Functions"
  [ testGroup "Pure Queries (Getters)"
      [ testCase "isCurveEditorVisible - returns True when visible" $ do
          let state = createTestUIState True False
          isCurveEditorVisible state @?= True
      
      , testCase "isCurveEditorVisible - returns False when not visible" $ do
          let state = createTestUIState False False
          isCurveEditorVisible state @?= False
      
      , testCase "shouldHideMinimizedLayers - returns True when hide is enabled" $ do
          let state = createTestUIState False True
          shouldHideMinimizedLayers state @?= True
      
      , testCase "shouldHideMinimizedLayers - returns False when hide is disabled" $ do
          let state = createTestUIState False False
          shouldHideMinimizedLayers state @?= False
      ]
  ]
