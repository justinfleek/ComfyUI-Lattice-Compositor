-- |
-- Module      : Lattice.State.MarkerSpec
-- Description : Test suite for Marker State management functions
-- 
-- Tests pure state management functions migrated from markerStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.MarkerSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.State.Marker
  ( framesEqual
  , getMarkers
  , getMarker
  , getMarkerAtFrame
  , getMarkersInRange
  , getNextMarker
  , getPreviousMarker
  )
import Lattice.Types.Project (Marker(..))

-- ============================================================================
-- TEST DATA HELPERS
-- ============================================================================

-- | Create test marker
createTestMarker :: Text -> Double -> Text -> Text -> Marker
createTestMarker id frame label color =
  Marker
    { markerId = id
    , markerFrame = frame
    , markerLabel = label
    , markerColor = color
    , markerDuration = Nothing
    , markerComment = Nothing
    }

-- ============================================================================
-- TESTS
-- ============================================================================

spec :: TestTree
spec = testGroup "Marker State Functions"
  [ testGroup "Pure Helper Functions"
      [ testCase "framesEqual - returns True for equal finite frames" $ do
          framesEqual 10.0 10.0 @?= True
      
      , testCase "framesEqual - returns False for different frames" $ do
          framesEqual 10.0 20.0 @?= False
      ]
  
  , testGroup "Pure Queries"
      [ testCase "getMarkers - returns sorted markers" $ do
          let marker1 = createTestMarker (T.pack "m1") 30.0 (T.pack "Marker 1") (T.pack "#ff0000")
          let marker2 = createTestMarker (T.pack "m2") 10.0 (T.pack "Marker 2") (T.pack "#00ff00")
          let marker3 = createTestMarker (T.pack "m3") 20.0 (T.pack "Marker 3") (T.pack "#0000ff")
          let markers = [marker1, marker2, marker3]
          let result = getMarkers markers
          length result @?= 3
          case result of
            [m1, m2, m3] -> do
              markerFrame m1 @?= 10.0
              markerFrame m2 @?= 20.0
              markerFrame m3 @?= 30.0
            _ -> assertBool "Expected 3 markers" False
      
      , testCase "getMarker - finds marker by ID" $ do
          let marker1 = createTestMarker (T.pack "m1") 10.0 (T.pack "Marker 1") (T.pack "#ff0000")
          let marker2 = createTestMarker (T.pack "m2") 20.0 (T.pack "Marker 2") (T.pack "#00ff00")
          let markers = [marker1, marker2]
          case getMarker markers (T.pack "m2") of
            Just m -> markerId m @?= T.pack "m2"
            Nothing -> assertBool "Expected marker" False
      
      , testCase "getMarker - returns Nothing when not found" $ do
          let markers = [createTestMarker (T.pack "m1") 10.0 (T.pack "Marker 1") (T.pack "#ff0000")]
          getMarker markers (T.pack "nonexistent") @?= Nothing
      
      , testCase "getMarkerAtFrame - finds marker at frame" $ do
          let marker1 = createTestMarker (T.pack "m1") 10.0 (T.pack "Marker 1") (T.pack "#ff0000")
          let marker2 = createTestMarker (T.pack "m2") 20.0 (T.pack "Marker 2") (T.pack "#00ff00")
          let markers = [marker1, marker2]
          case getMarkerAtFrame markers 20.0 of
            Just m -> markerId m @?= T.pack "m2"
            Nothing -> assertBool "Expected marker" False
      
      , testCase "getMarkersInRange - filters markers in range" $ do
          let marker1 = createTestMarker (T.pack "m1") 10.0 (T.pack "Marker 1") (T.pack "#ff0000")
          let marker2 = createTestMarker (T.pack "m2") 20.0 (T.pack "Marker 2") (T.pack "#00ff00")
          let marker3 = createTestMarker (T.pack "m3") 30.0 (T.pack "Marker 3") (T.pack "#0000ff")
          let markers = [marker1, marker2, marker3]
          let result = getMarkersInRange markers 15.0 25.0
          length result @?= 1
          case result of
            [m] -> markerId m @?= T.pack "m2"
            _ -> assertBool "Expected 1 marker" False
      
      , testCase "getNextMarker - finds next marker after frame" $ do
          let marker1 = createTestMarker (T.pack "m1") 10.0 (T.pack "Marker 1") (T.pack "#ff0000")
          let marker2 = createTestMarker (T.pack "m2") 20.0 (T.pack "Marker 2") (T.pack "#00ff00")
          let marker3 = createTestMarker (T.pack "m3") 30.0 (T.pack "Marker 3") (T.pack "#0000ff")
          let markers = [marker1, marker2, marker3]
          case getNextMarker markers 15.0 of
            Just m -> markerId m @?= T.pack "m2"
            Nothing -> assertBool "Expected marker" False
      
      , testCase "getNextMarker - returns Nothing when no next marker" $ do
          let markers = [createTestMarker (T.pack "m1") 10.0 (T.pack "Marker 1") (T.pack "#ff0000")]
          getNextMarker markers 20.0 @?= Nothing
      
      , testCase "getPreviousMarker - finds previous marker before frame" $ do
          let marker1 = createTestMarker (T.pack "m1") 10.0 (T.pack "Marker 1") (T.pack "#ff0000")
          let marker2 = createTestMarker (T.pack "m2") 20.0 (T.pack "Marker 2") (T.pack "#00ff00")
          let marker3 = createTestMarker (T.pack "m3") 30.0 (T.pack "Marker 3") (T.pack "#0000ff")
          let markers = [marker1, marker2, marker3]
          case getPreviousMarker markers 25.0 of
            Just m -> markerId m @?= T.pack "m2"
            Nothing -> assertBool "Expected marker" False
      
      , testCase "getPreviousMarker - returns Nothing when no previous marker" $ do
          let markers = [createTestMarker (T.pack "m1") 10.0 (T.pack "Marker 1") (T.pack "#ff0000")]
          getPreviousMarker markers 5.0 @?= Nothing
      ]
  ]
