-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // schema // temporal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pillar 7: Temporal
-- |
-- | Time, motion, and animation primitives.
-- |
-- | ## Submodules
-- |
-- | ### Units
-- | - `Hydrogen.Schema.Temporal.Duration`
-- | - `Hydrogen.Schema.Temporal.FPS`
-- | - `Hydrogen.Schema.Temporal.Frames`
-- | - `Hydrogen.Schema.Temporal.Timecode`
-- |
-- | ### Animation
-- | - `Hydrogen.Schema.Temporal.Animation`
-- | - `Hydrogen.Schema.Temporal.Timeline`
-- | - `Hydrogen.Schema.Temporal.Keyframe`
-- | - `Hydrogen.Schema.Temporal.Easing`
-- | - `Hydrogen.Schema.Temporal.CubicBezierEasing`
-- | - `Hydrogen.Schema.Temporal.Spring`
-- |
-- | ### State
-- | - `Hydrogen.Schema.Temporal.PlayState`
-- | - `Hydrogen.Schema.Temporal.Direction`
-- | - `Hydrogen.Schema.Temporal.Persistence`
-- | - `Hydrogen.Schema.Temporal.Iteration`
-- | - `Hydrogen.Schema.Temporal.Progress`
-- |
-- | ### Calendar
-- | - `Hydrogen.Schema.Temporal.TimeOfDay`
-- | - `Hydrogen.Schema.Temporal.DayOfWeek`
-- | - `Hydrogen.Schema.Temporal.Timezone`
-- |
-- | This module exists as documentation. Import submodules directly.

module Hydrogen.Schema.Temporal
  ( module Hydrogen.Schema.Temporal
  ) where

-- | Temporal pillar version for compatibility checks.
temporalVersion :: String
temporalVersion = "0.1.0"
