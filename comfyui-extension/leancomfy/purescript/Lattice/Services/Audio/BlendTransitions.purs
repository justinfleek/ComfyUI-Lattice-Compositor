-- | Lattice.Services.Audio.BlendTransitions - IPAdapter Blend Transitions
-- |
-- | Pure mathematical functions for blending between values/images:
-- | - Step blend (hard cut)
-- | - Linear blend (crossfade)
-- | - Smooth blend (smoothstep crossfade)
-- |
-- | Used for IPAdapter weight scheduling and general audio-reactive transitions.
-- |
-- | Source: ui/src/services/audioReactiveMapping.ts (createIPAdapterSchedule)

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

import Prelude
import Data.Int (floor, toNumber)
import Math (max, min) as Math

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Blend mode for transitions
data BlendMode
  = Step    -- ^ Hard cut at 50%
  | Linear  -- ^ Linear crossfade
  | Smooth  -- ^ Smoothstep crossfade

derive instance eqBlendMode :: Eq BlendMode

--------------------------------------------------------------------------------
-- Core Blend Functions
--------------------------------------------------------------------------------

-- | Step blend: hard cut at 50%.
-- |
-- | progress < 0.5: returns 0
-- | progress >= 0.5: returns 1
-- |
-- | Use for instant transitions on beat.
stepBlend :: Number -> Number
stepBlend progress = if progress >= 0.5 then 1.0 else 0.0

-- | Linear blend: direct crossfade.
-- |
-- | Returns progress clamped to [0, 1].
linearBlend :: Number -> Number
linearBlend progress = Math.max 0.0 (Math.min 1.0 progress)

-- | Smooth blend: smoothstep crossfade.
-- |
-- | Uses 3t² - 2t³ curve for natural-feeling transitions.
smoothBlend :: Number -> Number
smoothBlend progress =
  let t = Math.max 0.0 (Math.min 1.0 progress)
  in t * t * (3.0 - 2.0 * t)

-- | Apply blend mode to get blend factor.
applyBlendMode :: Number -> BlendMode -> Number
applyBlendMode progress mode = case mode of
  Step -> stepBlend progress
  Linear -> linearBlend progress
  Smooth -> smoothBlend progress

--------------------------------------------------------------------------------
-- Weight Calculation
--------------------------------------------------------------------------------

-- | Calculate weights for two-image transition.
-- |
-- | blend: Blend factor [0, 1]
-- | minWeight: Minimum weight floor (for IPAdapter stability)
-- |
-- | Returns: { current, next } weights
twoImageWeights :: Number -> Number -> { current :: Number, next :: Number }
twoImageWeights blend minWeight =
  let current = Math.max minWeight (1.0 - blend)
      next = Math.max minWeight blend
  in { current, next }

-- | Calculate blend factor for N-image cycling.
-- |
-- | imageCount: Total number of images in cycle
-- | progress: Overall progress through all images [0, N]
-- |
-- | Returns: { currentIndex, nextIndex, blendFactor }
cycleBlendIndices :: Int -> Number -> { currentIndex :: Int, nextIndex :: Int, blendFactor :: Number }
cycleBlendIndices imageCount progress
  | imageCount == 0 = { currentIndex: 0, nextIndex: 0, blendFactor: 0.0 }
  | otherwise =
      let current = floor progress `mod` imageCount
          next = (current + 1) `mod` imageCount
          blend = progress - toNumber (floor progress)
      in { currentIndex: current, nextIndex: next, blendFactor: blend }

--------------------------------------------------------------------------------
-- Transition Progress
--------------------------------------------------------------------------------

-- | Calculate transition progress.
-- |
-- | currentFrame: Current frame number
-- | transitionStartFrame: Frame when transition started
-- | transitionLength: Total transition length in frames
-- |
-- | Returns: Progress [0, 1] clamped
transitionProgress :: Int -> Int -> Int -> Number
transitionProgress currentFrame transitionStartFrame transitionLength
  | transitionLength == 0 = 1.0
  | otherwise =
      let elapsed = currentFrame - transitionStartFrame
          progress = toNumber elapsed / toNumber transitionLength
      in Math.max 0.0 (Math.min 1.0 progress)

-- | Check if transition is complete.
isTransitionComplete :: Number -> Boolean
isTransitionComplete progress = progress >= 1.0

--------------------------------------------------------------------------------
-- Full Transition Calculation
--------------------------------------------------------------------------------

-- | Calculate IPAdapter-style weights for frame.
-- |
-- | Returns: { getWeight, newCurrentIndex, isComplete }
-- |
-- | The getWeight function takes an image index and returns its weight.
calculateIPAdapterWeights :: Int -> Int -> Int -> Int -> Int -> BlendMode -> Number
                         -> { getWeight :: Int -> Number, newCurrentIndex :: Int, isComplete :: Boolean }
calculateIPAdapterWeights currentFrame transitionStartFrame transitionLength
                          currentIndex imageCount blendMode minWeight
  | imageCount == 0 = { getWeight: const 0.0, newCurrentIndex: 0, isComplete: true }
  | otherwise =
      let progress = transitionProgress currentFrame transitionStartFrame transitionLength
          complete = isTransitionComplete progress
          blend = applyBlendMode progress blendMode
          nextIndex = (currentIndex + 1) `mod` imageCount
          weights = twoImageWeights blend minWeight

          getWeight i
            | i == currentIndex = weights.current
            | i == nextIndex = weights.next
            | otherwise = minWeight

          newIndex = if complete then nextIndex else currentIndex
      in { getWeight, newCurrentIndex: newIndex, isComplete: complete }
