-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // animation // time
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Time primitives for animation: Duration and Progress.
-- |
-- | Duration is measured in milliseconds.
-- | Progress is normalized to [0, 1].

module Hydrogen.Animation.Time
  ( Duration(Duration)
  , Milliseconds
  , Progress(Progress)
  , normalizeProgress
  ) where

import Prelude

import Data.Newtype (class Newtype)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Duration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Duration in milliseconds, bounded to reasonable animation lengths.
-- | Maximum duration: 10 minutes (600000ms) — sufficient for any UI animation.
-- | Minimum duration: 0ms (instant).
type Milliseconds = Int

newtype Duration = Duration Milliseconds

derive instance Newtype Duration _
derive instance Eq Duration
derive instance Ord Duration

instance Semigroup Duration where
  append (Duration a) (Duration b) = Duration (a + b)

instance Monoid Duration where
  mempty = Duration 0

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress through an animation, normalized to [0, 1].
-- | This is the fundamental bounded time unit.
-- | 0.0 = animation start
-- | 1.0 = animation end
-- | Values outside [0,1] are clamped by normalizeProgress.
newtype Progress = Progress Number

derive instance Newtype Progress _
derive instance Eq Progress
derive instance Ord Progress

-- | Clamp progress to valid range [0, 1].
-- | This ensures all animation calculations operate on bounded values.
normalizeProgress :: Number -> Progress
normalizeProgress n
  | n < 0.0 = Progress 0.0
  | n > 1.0 = Progress 1.0
  | otherwise = Progress n
