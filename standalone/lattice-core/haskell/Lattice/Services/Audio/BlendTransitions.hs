{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Audio.BlendTransitions
Description : IPAdapter Blend Transitions
Copyright   : (c) Lattice, 2026
License     : MIT

Pure mathematical functions for blending between values/images:
- Step blend (hard cut)
- Linear blend (crossfade)
- Smooth blend (smoothstep crossfade)

Used for IPAdapter weight scheduling and general audio-reactive transitions.

Source: ui/src/services/audioReactiveMapping.ts (createIPAdapterSchedule)
-}

module Lattice.Services.Audio.BlendTransitions
  ( -- * Types
    BlendMode(..)
    -- * Core Blend Functions
  , stepBlend, linearBlend, smoothBlend
  , applyBlendMode
    -- * Weight Calculation
  , twoImageWeights
  , cycleBlendIndices
    -- * Transition Progress
  , transitionProgress
  , isTransitionComplete
    -- * Full Calculation
  , calculateIPAdapterWeights
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Blend mode for transitions
data BlendMode
  = Step    -- ^ Hard cut at 50%
  | Linear  -- ^ Linear crossfade
  | Smooth  -- ^ Smoothstep crossfade
  deriving (Eq, Show)

-- ────────────────────────────────────────────────────────────────────────────
-- Core Blend Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Step blend: hard cut at 50%.
--
--   progress < 0.5: returns 0
--   progress >= 0.5: returns 1
--
--   Use for instant transitions on beat.
stepBlend :: Double -> Double
stepBlend progress = if progress >= 0.5 then 1 else 0

-- | Linear blend: direct crossfade.
--
--   Returns progress clamped to [0, 1].
linearBlend :: Double -> Double
linearBlend progress = max 0 (min 1 progress)

-- | Smooth blend: smoothstep crossfade.
--
--   Uses 3t² - 2t³ curve for natural-feeling transitions.
smoothBlend :: Double -> Double
smoothBlend progress =
  let t = max 0 (min 1 progress)
  in t * t * (3 - 2 * t)

-- | Apply blend mode to get blend factor.
applyBlendMode :: Double -> BlendMode -> Double
applyBlendMode progress mode = case mode of
  Step -> stepBlend progress
  Linear -> linearBlend progress
  Smooth -> smoothBlend progress

-- ────────────────────────────────────────────────────────────────────────────
-- Weight Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate weights for two-image transition.
--
--   blend: Blend factor [0, 1]
--   minWeight: Minimum weight floor (for IPAdapter stability)
--
--   Returns: (currentWeight, nextWeight)
twoImageWeights :: Double -> Double -> (Double, Double)
twoImageWeights blend minWeight =
  let current = max minWeight (1 - blend)
      next = max minWeight blend
  in (current, next)

-- | Calculate blend factor for N-image cycling.
--
--   imageCount: Total number of images in cycle
--   progress: Overall progress through all images [0, N]
--
--   Returns: (currentIndex, nextIndex, blendFactor)
cycleBlendIndices :: Int -> Double -> (Int, Int, Double)
cycleBlendIndices imageCount progress
  | imageCount == 0 = (0, 0, 0)
  | otherwise =
      let current = floor progress `mod` imageCount
          next = (current + 1) `mod` imageCount
          blend = progress - fromIntegral (floor progress :: Int)
      in (current, next, blend)

-- ────────────────────────────────────────────────────────────────────────────
-- Transition Progress
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate transition progress.
--
--   currentFrame: Current frame number
--   transitionStartFrame: Frame when transition started
--   transitionLength: Total transition length in frames
--
--   Returns: Progress [0, 1] clamped
transitionProgress :: Int -> Int -> Int -> Double
transitionProgress currentFrame transitionStartFrame transitionLength
  | transitionLength == 0 = 1
  | otherwise =
      let elapsed = currentFrame - transitionStartFrame
          progress = fromIntegral elapsed / fromIntegral transitionLength
      in max 0 (min 1 progress)

-- | Check if transition is complete.
isTransitionComplete :: Double -> Bool
isTransitionComplete progress = progress >= 1

-- ────────────────────────────────────────────────────────────────────────────
-- Full Transition Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate IPAdapter-style weights for frame.
--
--   Returns: (weightFunction, newCurrentIndex, isComplete)
--
--   The weight function takes an image index and returns its weight.
calculateIPAdapterWeights :: Int -> Int -> Int -> Int -> Int -> BlendMode -> Double
                         -> (Int -> Double, Int, Bool)
calculateIPAdapterWeights currentFrame transitionStartFrame transitionLength
                          currentIndex imageCount blendMode minWeight
  | imageCount == 0 = (const 0, 0, True)
  | otherwise =
      let progress = transitionProgress currentFrame transitionStartFrame transitionLength
          complete = isTransitionComplete progress
          blend = applyBlendMode progress blendMode
          nextIndex = (currentIndex + 1) `mod` imageCount
          (currentWeight, nextWeight) = twoImageWeights blend minWeight

          weights i
            | i == currentIndex = currentWeight
            | i == nextIndex = nextWeight
            | otherwise = minWeight

          newIndex = if complete then nextIndex else currentIndex
      in (weights, newIndex, complete)
