-- |
-- Module      : Lattice.Composables.CurveEditorKeyboard
-- Description : Curve editor keyboard logic (keyframe navigation)
--
-- Ported from ui/src/composables/useCurveEditorKeyboard.ts
-- Pure: collect keyframe frames, find prev/next. No DOM or setFrame side effect.
--

module Lattice.Composables.CurveEditorKeyboard
  ( goToPreviousKeyframe
  , goToNextKeyframe
  ) where

import Data.List (nub, sort)
import Lattice.Types.Animation (AnimatableProperty(..), Keyframe(..), PropertyValue)

-- | Collect all unique keyframe frame numbers from visible properties, sorted
allKeyframeFrames :: [AnimatableProperty PropertyValue] -> [Double]
allKeyframeFrames props =
  sort . nub $ concatMap (map keyframeFrame . animatablePropertyKeyframes) props

-- | Navigate to previous keyframe (largest frame < currentFrame). Returns Nothing if none.
goToPreviousKeyframe
  :: Double
  -> [AnimatableProperty PropertyValue]
  -> Maybe Double
goToPreviousKeyframe currentFrame visibleProperties =
  let frames = allKeyframeFrames visibleProperties
      prevFrames = filter (< currentFrame) frames
  in case prevFrames of
       [] -> Nothing
       xs -> Just (maximum xs)

-- | Navigate to next keyframe (smallest frame > currentFrame). Returns Nothing if none.
goToNextKeyframe
  :: Double
  -> [AnimatableProperty PropertyValue]
  -> Maybe Double
goToNextKeyframe currentFrame visibleProperties =
  let frames = allKeyframeFrames visibleProperties
      nextFrames = filter (> currentFrame) frames
  in case nextFrames of
       [] -> Nothing
       xs -> Just (minimum xs)
