-- |
-- Module      : Lattice.State.Physics
-- Description : Pure state management functions for physics store
-- 
-- Migrated from ui/src/stores/physicsStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Physics
  ( -- Helper functions
    radiansToDegrees
  , degreesToRadians
  -- Calculation functions
  , calculateBakeFrameRange
  ) where

import Lattice.Utils.NumericSafety (ensureFiniteD)

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Convert angle from radians to degrees
-- Pure function: takes angle in radians, returns angle in degrees
-- Formula: angle * (180 / π)
radiansToDegrees :: Double -> Double
radiansToDegrees radians =
  let
    safeRadians = ensureFiniteD radians 0.0
  in
    safeRadians * (180.0 / pi)

-- | Convert angle from degrees to radians
-- Pure function: takes angle in degrees, returns angle in radians
-- Formula: angle * (π / 180)
degreesToRadians :: Double -> Double
degreesToRadians degrees =
  let
    safeDegrees = ensureFiniteD degrees 0.0
  in
    safeDegrees * (pi / 180.0)

-- ============================================================================
-- CALCULATION FUNCTIONS
-- ============================================================================

-- | Calculate start and end frame for baking given options and composition frame count
-- Pure function: takes startFrame option, endFrame option, composition frame count, returns (startFrame, endFrame)
-- Validates and clamps to valid range [0, compFrameCount - 1]
calculateBakeFrameRange :: Maybe Int -> Maybe Int -> Int -> (Int, Int)
calculateBakeFrameRange mStartFrame mEndFrame compFrameCount =
  let
    -- Ensure compFrameCount is positive
    safeCompFrameCount = if compFrameCount > 0 then compFrameCount else 1
    maxFrame = safeCompFrameCount - 1
    
    -- Validate and clampD startFrame
    startFrame = case mStartFrame of
      Nothing -> 0
      Just sf -> if sf >= 0 && sf <= maxFrame then sf else 0
    
    -- Validate and clampD endFrame
    endFrame = case mEndFrame of
      Nothing -> maxFrame
      Just ef -> if ef >= startFrame && ef <= maxFrame then ef else maxFrame
  in
    (startFrame, endFrame)
