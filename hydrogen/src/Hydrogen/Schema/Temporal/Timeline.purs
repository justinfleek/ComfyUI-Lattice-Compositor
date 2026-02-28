-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // timeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timeline Compound — Orchestration of multiple animations in time.
-- |
-- | Allows composing animations:
-- | - **Sequentially**: Run B after A finishes.
-- | - **Parallel**: Run A and B at the same time.
-- | - **Staggered**: Run multiple items with a delay offset.
-- | - **Absolute**: Place animations at specific time offsets.

module Hydrogen.Schema.Temporal.Timeline
  ( Timeline(..)
  , sequence
  , parallel
  , stagger
  , absolute
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Generic.Rep (class Generic)
import Hydrogen.Schema.Temporal.Animation (Animation)
import Hydrogen.Schema.Temporal.Duration (Duration)
import Hydrogen.Schema.Temporal.Delay (Delay)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // timeline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Recursive structure for composing animations
data Timeline a
  = Single (Animation a)
  | Sequence (Array (Timeline a))
  | Parallel (Array (Timeline a))
  | Stagger Delay (Array (Timeline a))
  | Absolute (Array { offset :: Duration, animation :: Timeline a })

derive instance eqTimeline :: (Eq a) => Eq (Timeline a)
derive instance ordTimeline :: (Ord a) => Ord (Timeline a)
derive instance genericTimeline :: Generic (Timeline a) _

instance showTimeline :: (Show a) => Show (Timeline a) where
  show (Single a) = "(Single " <> show a <> ")"
  show (Sequence as) = "(Sequence " <> show as <> ")"
  show (Parallel as) = "(Parallel " <> show as <> ")"
  show (Stagger d as) = "(Stagger " <> show d <> " " <> show as <> ")"
  show (Absolute as) = "(Absolute " <> show as <> ")"

-- | Run animations one after another
sequence :: forall a. Array (Timeline a) -> Timeline a
sequence = Sequence

-- | Run animations simultaneously
parallel :: forall a. Array (Timeline a) -> Timeline a
parallel = Parallel

-- | Run animations with a delay between start times
stagger :: forall a. Delay -> Array (Timeline a) -> Timeline a
stagger = Stagger

-- | Place animations at absolute time offsets
absolute :: forall a. Array { offset :: Duration, animation :: Timeline a } -> Timeline a
absolute = Absolute
