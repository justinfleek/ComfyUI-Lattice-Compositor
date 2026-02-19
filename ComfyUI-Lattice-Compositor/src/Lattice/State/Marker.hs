-- |
-- Module      : Lattice.State.Marker
-- Description : Pure state management functions for marker store
-- 
-- Migrated from ui/src/stores/markerStore.ts
-- Pure query and helper functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Marker
  ( -- Pure helper
    framesEqual
  -- Pure queries
  , getMarkers
  , getMarker
  , getMarkerAtFrame
  , getMarkersInRange
  , getNextMarker
  , getPreviousMarker
  -- Types
  , Marker(..)
  ) where

import Data.List (find, sortBy)
import Data.Ord (comparing)
import Data.Text (Text)
import Lattice.Types.Project (Marker(..))
import Lattice.Utils.NumericSafety
  ( ensureFiniteD
  )

-- ============================================================================
-- PURE HELPER FUNCTIONS
-- ============================================================================

-- | Compare two frame values safely, handling NaN
-- Returns False if either value is not finite
framesEqual ::
  Double ->
  Double ->
  Bool
framesEqual a b =
  let
    finiteA = ensureFiniteD a 0.0
    finiteB = ensureFiniteD b 0.0
  in
    finiteA == finiteB && a == finiteA && b == finiteB

-- ============================================================================
-- PURE QUERIES
-- ============================================================================

-- | Get all markers from composition
-- Pure function: takes list of markers, returns sorted list
getMarkers ::
  [Marker] ->
  [Marker]
getMarkers markers = sortMarkers markers

-- | Get a marker by ID
-- Pure function: takes list of markers and marker ID, returns Maybe marker
getMarker ::
  [Marker] ->
  Text ->
  Maybe Marker
getMarker markers targetId = find (\m -> markerId m == targetId) markers

-- | Get marker at a specific frame
-- Pure function: takes list of markers and frame, returns Maybe marker
getMarkerAtFrame ::
  [Marker] ->
  Double ->
  Maybe Marker
getMarkerAtFrame markers frame =
  find (\m -> framesEqual (markerFrame m) frame) markers

-- | Get all markers within a frame range
-- Pure function: takes list of markers, start frame, end frame, returns filtered list
getMarkersInRange ::
  [Marker] ->
  Double ->
  Double ->
  [Marker]
getMarkersInRange markers startFrame endFrame =
  filter
    (\m ->
       let frame = markerFrame m
       in frame >= startFrame && frame <= endFrame)
    markers

-- | Get the next marker after a given frame
-- Pure function: takes list of markers and frame, returns Maybe marker
getNextMarker ::
  [Marker] ->
  Double ->
  Maybe Marker
getNextMarker markers frame =
  let
    sortedMarkers = sortMarkers markers
    nextMarkers = filter (\m -> markerFrame m > frame) sortedMarkers
  in
    case nextMarkers of
      [] -> Nothing
      (m : _) -> Just m

-- | Get the previous marker before a given frame
-- Pure function: takes list of markers and frame, returns Maybe marker
getPreviousMarker ::
  [Marker] ->
  Double ->
  Maybe Marker
getPreviousMarker markers frame =
  let
    sortedMarkers = sortMarkers markers
    previousMarkers = filter (\m -> markerFrame m < frame) sortedMarkers
  in
    case reverse previousMarkers of
      [] -> Nothing
      (m : _) -> Just m

-- ============================================================================
-- INTERNAL HELPERS
-- ============================================================================

-- | Sort markers by frame
sortMarkers ::
  [Marker] ->
  [Marker]
sortMarkers markers = sortBy (comparing markerFrame) markers
