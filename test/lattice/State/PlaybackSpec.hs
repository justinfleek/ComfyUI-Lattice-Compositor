-- |
-- Module      : Lattice.State.PlaybackSpec
-- Description : Test suite for Playback State management functions
-- 
-- Tests pure state management functions migrated from playbackStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.PlaybackSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.State.Playback
  ( playing
  , hasWorkArea
  , effectiveStartFrame
  , effectiveEndFrame
  , clampFrame
  , stepForwardFrame
  , stepBackwardFrame
  , PlaybackState(..)
  )

-- ============================================================================
-- TEST DATA HELPERS
-- ============================================================================

-- | Create test playback state
createTestPlaybackState :: Bool -> Maybe Double -> Maybe Double -> PlaybackState
createTestPlaybackState isPlaying mStart mEnd =
  PlaybackState isPlaying mStart mEnd

-- ============================================================================
-- TESTS
-- ============================================================================

spec :: TestTree
spec = testGroup "Playback State Functions"
  [ testGroup "Pure Queries (Getters)"
      [ testCase "playing - returns True when playing" $ do
          let state = createTestPlaybackState True Nothing Nothing
          playing state @?= True
      
      , testCase "playing - returns False when not playing" $ do
          let state = createTestPlaybackState False Nothing Nothing
          playing state @?= False
      
      , testCase "hasWorkArea - returns True when work area is set" $ do
          let state = createTestPlaybackState False (Just 10.0) (Just 50.0)
          hasWorkArea state @?= True
      
      , testCase "hasWorkArea - returns False when work area is not set" $ do
          let state = createTestPlaybackState False Nothing Nothing
          hasWorkArea state @?= False
      
      , testCase "effectiveStartFrame - returns workAreaStart when set" $ do
          let state = createTestPlaybackState False (Just 10.0) Nothing
          effectiveStartFrame state @?= 10.0
      
      , testCase "effectiveStartFrame - returns 0 when workAreaStart not set" $ do
          let state = createTestPlaybackState False Nothing Nothing
          effectiveStartFrame state @?= 0.0
      
      , testCase "effectiveEndFrame - returns workAreaEnd when set" $ do
          let state = createTestPlaybackState False Nothing (Just 50.0)
          effectiveEndFrame state 100.0 @?= 50.0
      
      , testCase "effectiveEndFrame - returns frameCount - 1 when workAreaEnd not set" $ do
          let state = createTestPlaybackState False Nothing Nothing
          effectiveEndFrame state 100.0 @?= 99.0
      ]
  
  , testGroup "Pure Calculations"
      [ testCase "clampFrame - clamps frame to valid range" $ do
          clampFrame 50.0 100.0 @?= 50.0
          clampFrame (-10.0) 100.0 @?= 0.0
          clampFrame 150.0 100.0 @?= 99.0
      
      , testCase "stepForwardFrame - increments frame" $ do
          stepForwardFrame 10.0 100.0 @?= 11.0
      
      , testCase "stepForwardFrame - clamps to max" $ do
          stepForwardFrame 99.0 100.0 @?= 99.0
      
      , testCase "stepBackwardFrame - decrements frame" $ do
          stepBackwardFrame 10.0 @?= 9.0
      
      , testCase "stepBackwardFrame - clamps to min" $ do
          stepBackwardFrame 0.0 @?= 0.0
      ]
  ]
