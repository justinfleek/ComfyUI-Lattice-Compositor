-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress Atom — Normalized animation progress value [0.0, 1.0].
-- |
-- | Progress represents the current state of an animation or process:
-- | - 0.0: Start
-- | - 1.0: End
-- |
-- | Values are clamped to [0.0, 1.0] to ensure valid interpolation.

module Hydrogen.Schema.Temporal.Progress
  ( Progress
  , progress
  , unsafeProgress
  , unwrapProgress
  , progressToNumber
  , start
  , end
  , progressBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized progress value [0.0, 1.0]
newtype Progress = Progress Number

derive instance eqProgress :: Eq Progress
derive instance ordProgress :: Ord Progress

instance showProgress :: Show Progress where
  show (Progress p) = "(Progress " <> show p <> ")"

-- | Create Progress, clamping to [0.0, 1.0]
progress :: Number -> Progress
progress p
  | p < 0.0 = Progress 0.0
  | p > 1.0 = Progress 1.0
  | otherwise = Progress p

-- | Create Progress without bounds checking
unsafeProgress :: Number -> Progress
unsafeProgress = Progress

-- | Extract raw Number from Progress
unwrapProgress :: Progress -> Number
unwrapProgress (Progress p) = p

-- | Alias for unwrapProgress
progressToNumber :: Progress -> Number
progressToNumber = unwrapProgress

-- | Start of progress (0.0)
start :: Progress
start = Progress 0.0

-- | End of progress (1.0)
end :: Progress
end = Progress 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Progress
progressBounds :: Bounded.NumberBounds
progressBounds = Bounded.numberBounds 0.0 1.0 "progress"
  "Normalized progress value (0.0 to 1.0)"
