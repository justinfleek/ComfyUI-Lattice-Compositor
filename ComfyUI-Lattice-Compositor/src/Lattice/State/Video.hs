-- |
-- Module      : Lattice.State.Video
-- Description : Pure state management functions for video store
-- 
-- Migrated from ui/src/stores/videoStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Video
  ( -- Calculation functions
    calculateTimeStretch
  , calculateVideoFrameCount
  , calculateStretchedDuration
  , checkFpsMismatch
  , calculateVideoOutPoint
  ) where

import Lattice.Utils.NumericSafety (ensureFiniteD)

-- ============================================================================
-- CALCULATION FUNCTIONS
-- ============================================================================

-- | Calculate time stretch percentage from video fps and composition fps
-- Pure function: takes video fps and composition fps, returns stretch percentage
-- Formula: (videoFps / compFps) * 100
calculateTimeStretch :: Double -> Double -> Double
calculateTimeStretch videoFps compFps =
  let
    safeVideoFps = ensureFiniteD videoFps 16.0
    safeCompFps = ensureFiniteD compFps 16.0
    -- Ensure compFps is positive to avoid division by zero
    validCompFps = if safeCompFps > 0 then safeCompFps else 16.0
  in
    if safeVideoFps > 0 && validCompFps > 0
      then (safeVideoFps / validCompFps) * 100.0
      else 100.0

-- | Calculate frame count from duration and fps
-- Pure function: takes duration and fps, returns frame count
-- Formula: ceiling(duration * fps)
calculateVideoFrameCount :: Double -> Double -> Int
calculateVideoFrameCount duration fps =
  let
    safeDuration = ensureFiniteD duration 0.0
    safeFps = ensureFiniteD fps 16.0
    validFps = if safeFps > 0 then safeFps else 16.0
  in
    if safeDuration >= 0 && validFps > 0
      then ceiling (safeDuration * validFps)
      else 0

-- | Calculate stretched duration when conforming fps
-- Pure function: takes duration, video fps, and composition fps, returns stretched duration
-- Formula: duration * (videoFps / compFps)
calculateStretchedDuration :: Double -> Double -> Double -> Double
calculateStretchedDuration duration videoFps compFps =
  let
    safeDuration = ensureFiniteD duration 0.0
    safeVideoFps = ensureFiniteD videoFps 16.0
    safeCompFps = ensureFiniteD compFps 16.0
    validVideoFps = if safeVideoFps > 0 then safeVideoFps else 16.0
    validCompFps = if safeCompFps > 0 then safeCompFps else 16.0
  in
    if safeDuration >= 0 && validVideoFps > 0 && validCompFps > 0
      then safeDuration * (validVideoFps / validCompFps)
      else safeDuration

-- | Check if fps differs significantly
-- Pure function: takes video fps, composition fps, and threshold, returns boolean
-- Formula: abs(videoFps - compFps) > threshold
checkFpsMismatch :: Double -> Double -> Double -> Bool
checkFpsMismatch videoFps compFps threshold =
  let
    safeVideoFps = ensureFiniteD videoFps 16.0
    safeCompFps = ensureFiniteD compFps 16.0
    safeThreshold = ensureFiniteD threshold 0.5
  in
    abs (safeVideoFps - safeCompFps) > safeThreshold

-- | Calculate out point for video layer
-- Pure function: takes video frame count and composition frame count, returns out point
-- Formula: min(videoFrameCount - 1, compFrameCount - 1)
calculateVideoOutPoint :: Int -> Int -> Int
calculateVideoOutPoint videoFrameCount compFrameCount =
  let
    -- Ensure non-negative
    safeVideoFrames = if videoFrameCount > 0 then videoFrameCount else 0
    safeCompFrames = if compFrameCount > 0 then compFrameCount else 0
    videoOutPoint = safeVideoFrames - 1
    compOutPoint = safeCompFrames - 1
  in
    min videoOutPoint compOutPoint
