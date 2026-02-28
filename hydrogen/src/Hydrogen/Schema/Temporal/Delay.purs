-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // temporal // delay
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Delay Molecule — A duration specifically representing a wait time.
-- |
-- | While structurally identical to Duration, Delay carries specific semantic
-- | meaning: "time before start". Separation of types prevents confusing
-- | active duration with delay time.

module Hydrogen.Schema.Temporal.Delay
  ( Delay
  , delay
  , toDuration
  , none
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

import Hydrogen.Schema.Temporal.Duration (Duration)
import Hydrogen.Schema.Temporal.Duration as Duration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // delay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time to wait before starting an action
newtype Delay = Delay Duration

derive instance eqDelay :: Eq Delay
derive instance ordDelay :: Ord Delay

instance showDelay :: Show Delay where
  show (Delay d) = "(Delay " <> show d <> ")"

-- | Create Delay from Duration
delay :: Duration -> Delay
delay = Delay

-- | Convert back to Duration
toDuration :: Delay -> Duration
toDuration (Delay d) = d

-- | No delay (0ms)
none :: Delay
none = Delay Duration.zero
