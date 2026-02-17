-- |
-- Module      : Lattice.State.AudioKeyframe
-- Description : Pure state management functions for audio keyframe store
-- 
-- Migrated from ui/src/stores/audioKeyframeStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.AudioKeyframe
  ( -- Helper functions
    applySmoothing
  , interpolateKeyframeValue
  ) where

import Data.List (find, sortBy)
import Data.Ord (comparing)
import Lattice.Utils.NumericSafety (ensureFinite)

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Apply exponential smoothing to amplitude values
-- Pure function: takes value array and smoothing factor, returns smoothed array
-- Formula: smoothed[i] = factor * smoothed[i-1] + (1 - factor) * values[i]
applySmoothing :: [Double] -> Double -> [Double]
applySmoothing values factor =
  let
    safeFactor = ensureFinite factor 0.0
    clampedFactor = if safeFactor < 0 then 0.0 else if safeFactor > 1 then 1.0 else safeFactor
  in
    case values of
      [] -> []
      (first : rest) ->
        let
          safeFirst = ensureFinite first 0.0
          smoothed = scanl smoothNext safeFirst rest
          smoothNext prev curr =
            let
              safeCurr = ensureFinite curr 0.0
            in
              clampedFactor * prev + (1.0 - clampedFactor) * safeCurr
        in
          smoothed

-- | Interpolate value between keyframes at a specific frame
-- Pure function: takes target frame, keyframes list (frame, value), default value, returns interpolated value
-- Uses linear interpolation between previous and next keyframe
interpolateKeyframeValue :: Int -> [(Int, Double)] -> Double -> Double
interpolateKeyframeValue targetFrame keyframes defaultValue =
  let
    -- Find exact match first
    exactMatch = find (\(frame, _) -> frame == targetFrame) keyframes
  in
    case exactMatch of
      Just (_, value) -> ensureFinite value defaultValue
      Nothing ->
        let
          -- Sort keyframes by frame
          sortedKeyframes = sortBy (comparing fst) keyframes
          
          -- Find previous keyframe (frame <= targetFrame)
          previousKeyframes = filter (\(frame, _) -> frame <= targetFrame) sortedKeyframes
          previousKf = case reverse previousKeyframes of
            [] -> Nothing
            (kf : _) -> Just kf
          
          -- Find next keyframe (frame > targetFrame)
          nextKeyframes = filter (\(frame, _) -> frame > targetFrame) sortedKeyframes
          nextKf = case nextKeyframes of
            [] -> Nothing
            (kf : _) -> Just kf
        in
          case (previousKf, nextKf) of
            (Nothing, Nothing) -> defaultValue
            (Nothing, Just (_, nextValue)) -> ensureFinite nextValue defaultValue
            (Just (_, prevValue), Nothing) -> ensureFinite prevValue defaultValue
            (Just (prevFrame, prevValue), Just (nextFrame, nextValue)) ->
              let
                safePrevValue = ensureFinite prevValue defaultValue
                safeNextValue = ensureFinite nextValue defaultValue
                frameDiff = nextFrame - prevFrame
              in
                if frameDiff == 0
                  then safePrevValue
                  else
                    let
                      t = fromIntegral (targetFrame - prevFrame) / fromIntegral frameDiff
                      clampedT = if t < 0 then 0.0 else if t > 1 then 1.0 else t
                    in
                      safePrevValue + clampedT * (safeNextValue - safePrevValue)
