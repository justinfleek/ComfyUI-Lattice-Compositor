-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // a11y // motion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Reduced motion support
-- |
-- | Utilities for respecting user's motion preferences.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.A11y.Motion as Motion
-- |
-- | -- Only animate when user allows motion
-- | Motion.motionSafe "animate-spin"
-- | -- "motion-safe:animate-spin"
-- |
-- | -- Disable animations when reduced motion preferred
-- | Motion.motionReduce "animate-none"
-- | -- "motion-reduce:animate-none"
-- |
-- | -- Combined approach
-- | Motion.withReducedMotion "animate-bounce" "animate-none"
-- | -- "motion-safe:animate-bounce motion-reduce:animate-none"
-- | ```
module Hydrogen.A11y.Motion
  ( -- * Motion Prefixes
    motionSafe
  , motionReduce
    -- * Combined
  , withReducedMotion
    -- * Presets
  , safeTransition
  , safeAnimation
  , reducedAnimation
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // motion prefixes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply class only when reduced motion is NOT preferred
-- |
-- | Use for animations that should be disabled when user prefers reduced motion.
motionSafe :: String -> String
motionSafe cls = "motion-safe:" <> cls

-- | Apply class only when reduced motion IS preferred
-- |
-- | Use for fallback styles when animations are disabled.
motionReduce :: String -> String
motionReduce cls = "motion-reduce:" <> cls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // combined
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply animated class normally, fallback when reduced motion preferred
-- |
-- | ```purescript
-- | withReducedMotion "animate-spin" "animate-none"
-- | -- Uses spin animation normally, no animation when reduced motion preferred
-- | ```
withReducedMotion :: String -> String -> String
withReducedMotion normalClass reducedClass =
  motionSafe normalClass <> " " <> motionReduce reducedClass

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safe transition that respects reduced motion
-- |
-- | Uses instant transition when reduced motion is preferred.
safeTransition :: String
safeTransition = 
  "motion-safe:transition-all motion-safe:duration-200 motion-reduce:transition-none"

-- | Safe animation that respects reduced motion
-- |
-- | Disables animation when reduced motion is preferred.
safeAnimation :: String -> String
safeAnimation animationClass =
  motionSafe animationClass <> " " <> motionReduce "animate-none"

-- | Reduced animation preset
-- |
-- | Common pattern for reduced motion fallback.
reducedAnimation :: String
reducedAnimation = "motion-reduce:animate-none motion-reduce:transition-none"
