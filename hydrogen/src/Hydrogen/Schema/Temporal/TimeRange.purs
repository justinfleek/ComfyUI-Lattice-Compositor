-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // temporal // time-range
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimeRange Molecule — A start and end duration defining an interval.
-- |
-- | Used for trimming media, defining active windows, or scheduling.
-- |
-- | Constraints:
-- | - Start must be <= End (enforced by smart constructor)

module Hydrogen.Schema.Temporal.TimeRange
  ( TimeRange
  , timeRange
  , start
  , end
  , duration
  , contains
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
  , (<=)
  , (>=)
  , (&&)
  )

import Hydrogen.Schema.Temporal.Duration (Duration)
import Hydrogen.Schema.Temporal.Duration as Duration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // time range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interval between two time points
data TimeRange = TimeRange Duration Duration

derive instance eqTimeRange :: Eq TimeRange
derive instance ordTimeRange :: Ord TimeRange

instance showTimeRange :: Show TimeRange where
  show (TimeRange s e) = "(TimeRange " <> show s <> " -> " <> show e <> ")"

-- | Create TimeRange, ensuring start <= end
-- | If start > end, they are swapped.
timeRange :: Duration -> Duration -> TimeRange
timeRange a b
  | a <= b    = TimeRange a b
  | otherwise = TimeRange b a

-- | Get start time
start :: TimeRange -> Duration
start (TimeRange s _) = s

-- | Get end time
end :: TimeRange -> Duration
end (TimeRange _ e) = e

-- | Get duration of range (End - Start)
duration :: TimeRange -> Duration
duration (TimeRange s e) = Duration.subtract e s

-- | Check if a time point is within the range (inclusive)
contains :: Duration -> TimeRange -> Boolean
contains t (TimeRange s e) = t >= s && t <= e
