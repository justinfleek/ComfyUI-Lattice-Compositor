-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // tour // motion // responsive
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Responsive Motion — Accessibility and performance scaling.
-- |
-- | ## Overview
-- |
-- | Motion should adapt to user preferences and device capabilities:
-- | - Respect `prefers-reduced-motion`
-- | - Scale down on low-power devices
-- | - Adapt to frame rate capabilities
-- |
-- | ## Design Philosophy
-- |
-- | Accessibility is not optional. These adaptations ensure tours work
-- | beautifully for everyone, regardless of device or user needs.

module Hydrogen.Element.Compound.Tour.Motion.Responsive
  ( -- * Scale Types
    MotionScale(..)
  , PerformanceTier(..)
  
    -- * Configuration
  , ReducedMotionFallback
  
    -- * Computation
  , computeMotionScale
  , reducedMotionFallbacks
  , performanceAdaptations
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , (*)
  , (<)
  )

import Hydrogen.Element.Compound.Tour.Motion.Spring (criticallyDamped)
import Hydrogen.Element.Compound.Tour.Motion.Spotlight
  ( MorphConfig
  , MorphInterpolation(InterpolateDirect)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Motion scale for accessibility and performance.
data MotionScale
  = MotionFull           -- ^ Full animations
  | MotionReduced        -- ^ Reduced motion (prefers-reduced-motion)
  | MotionMinimal        -- ^ Minimal motion (very low performance)
  | MotionNone           -- ^ No motion at all

derive instance eqMotionScale :: Eq MotionScale
derive instance ordMotionScale :: Ord MotionScale

instance showMotionScale :: Show MotionScale where
  show MotionFull = "full"
  show MotionReduced = "reduced"
  show MotionMinimal = "minimal"
  show MotionNone = "none"

instance boundedMotionScale :: Bounded MotionScale where
  bottom = MotionFull
  top = MotionNone

-- | Performance tier for adaptive animations.
data PerformanceTier
  = TierHigh            -- ^ Full effects, blur, shadows
  | TierMedium          -- ^ Most effects, no blur
  | TierLow             -- ^ Basic animations only
  | TierMinimal         -- ^ Opacity changes only

derive instance eqPerformanceTier :: Eq PerformanceTier
derive instance ordPerformanceTier :: Ord PerformanceTier

instance showPerformanceTier :: Show PerformanceTier where
  show TierHigh = "high"
  show TierMedium = "medium"
  show TierLow = "low"
  show TierMinimal = "minimal"

-- | Reduced motion fallback configuration.
type ReducedMotionFallback =
  { morphToFade :: Boolean
    -- ^ Replace morph with crossfade
  , disableSpring :: Boolean
    -- ^ Use linear timing instead of springs
  , disablePulse :: Boolean
    -- ^ Disable all pulse animations
  , instantProgress :: Boolean
    -- ^ Progress jumps instantly
  , keepOpacity :: Boolean
    -- ^ Keep opacity animations (usually safe)
  , maxDuration :: Number
    -- ^ Maximum animation duration (ms)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute motion scale from user preference and device.
computeMotionScale
  :: { prefersReducedMotion :: Boolean, isLowPower :: Boolean, fps :: Number }
  -> MotionScale
computeMotionScale prefs
  | prefs.prefersReducedMotion = MotionReduced
  | prefs.isLowPower = MotionMinimal
  | prefs.fps < 30.0 = MotionMinimal
  | prefs.fps < 50.0 = MotionReduced
  | true = MotionFull

-- | Get reduced motion fallbacks.
reducedMotionFallbacks :: ReducedMotionFallback
reducedMotionFallbacks =
  { morphToFade: true
  , disableSpring: true
  , disablePulse: true
  , instantProgress: true
  , keepOpacity: true
  , maxDuration: 200.0
  }

-- | Adapt animations based on performance tier.
performanceAdaptations :: PerformanceTier -> MorphConfig -> MorphConfig
performanceAdaptations tier config = case tier of
  TierHigh -> config
  TierMedium -> config
    { scaleAtMidpoint = 1.0
    , rotateAtMidpoint = 0.0
    }
  TierLow -> config
    { duration = config.duration * 0.7
    , spring = criticallyDamped
    , pathCurve = 0.0
    , scaleAtMidpoint = 1.0
    , rotateAtMidpoint = 0.0
    , opacityDip = 0.0
    }
  TierMinimal -> config
    { duration = 0.0
    , interpolation = InterpolateDirect
    }
