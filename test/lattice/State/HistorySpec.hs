-- |
-- Module      : Lattice.State.HistorySpec
-- Description : Test suite for History State management functions
-- 
-- Tests pure state management functions migrated from historyStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.HistorySpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Lattice.State.History
  ( canUndo
  , canRedo
  , currentIndex
  , stackSize
  , HistoryState(..)
  )

-- ============================================================================
-- TEST DATA HELPERS
-- ============================================================================

-- | Create test history state
createTestHistoryState :: Int -> Int -> HistoryState
createTestHistoryState index stackSize = HistoryState {historyStateIndex = index, historyStateStackSize = stackSize}

-- ============================================================================
-- TESTS
-- ============================================================================

spec :: TestTree
spec = testGroup "History State Functions"
  [ testGroup "Pure Queries (Getters)"
      [ testCase "canUndo - returns True when index > 0" $ do
          let state = createTestHistoryState 1 5
          canUndo state @?= True
      
      , testCase "canUndo - returns False when index is 0" $ do
          let state = createTestHistoryState 0 5
          canUndo state @?= False
      
      , testCase "canUndo - returns False when index is negative" $ do
          let state = createTestHistoryState (-1) 5
          canUndo state @?= False
      
      , testCase "canRedo - returns True when index < stackSize - 1" $ do
          let state = createTestHistoryState 2 5
          canRedo state @?= True
      
      , testCase "canRedo - returns False when index is at end" $ do
          let state = createTestHistoryState 4 5
          canRedo state @?= False
      
      , testCase "canRedo - returns False when index is beyond end" $ do
          let state = createTestHistoryState 5 5
          canRedo state @?= False
      
      , testCase "currentIndex - returns index" $ do
          let state = createTestHistoryState 3 5
          currentIndex state @?= 3
      
      , testCase "stackSize - returns stack size" $ do
          let state = createTestHistoryState 2 10
          stackSize state @?= 10
      ]
  ]
