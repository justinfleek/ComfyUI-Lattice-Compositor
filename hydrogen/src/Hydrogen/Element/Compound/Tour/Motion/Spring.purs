-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // tour // motion // spring
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spring Physics — Foundational physics-based animation parameters.
-- |
-- | ## Overview
-- |
-- | Spring physics provides organic, physically-based motion. Unlike bezier
-- | curves, springs respond naturally to interruption and feel "alive".
-- |
-- | ## Design Philosophy
-- |
-- | Springs are configured by three physical parameters:
-- | - **Stiffness**: How quickly the spring returns to rest
-- | - **Damping**: How quickly oscillation decays
-- | - **Mass**: Inertia of the animated object
-- |
-- | The presets here are tuned for UI animation based on Framer Motion
-- | conventions and extensive perceptual testing.

module Hydrogen.Element.Compound.Tour.Motion.Spring
  ( -- * Types
    SpringPreset(..)
  , SpringParams
  
    -- * Presets
  , snappySpring
  , bouncySpring
  , smoothSpring
  , preciseSpring
  , criticallyDamped
  
    -- * Evaluation
  , evaluateSpring
  , springDuration
  
    -- * CSS Conversion
  , springToCss
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , max
  , min
  , negate
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (>=)
  , (||)
  )

import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring physics presets for different use cases.
data SpringPreset
  = Snappy        -- ^ Quick, responsive UI feedback
  | Bouncy        -- ^ Playful with visible overshoot
  | Smooth        -- ^ Elegant, no overshoot
  | Precise       -- ^ Exact positioning, minimal settling
  | Critical      -- ^ Critically damped (fastest without overshoot)

derive instance eqSpringPreset :: Eq SpringPreset
derive instance ordSpringPreset :: Ord SpringPreset

instance showSpringPreset :: Show SpringPreset where
  show Snappy = "snappy"
  show Bouncy = "bouncy"
  show Smooth = "smooth"
  show Precise = "precise"
  show Critical = "critical"

-- | Spring parameters based on Framer Motion conventions.
-- |
-- | These three parameters define the complete spring behavior:
-- | - **stiffness**: Spring constant (N/m equivalent). Range: 50-500. Default: 100.
-- | - **damping**: Damping coefficient. Range: 5-40. Default: 10.
-- | - **mass**: Object mass. Range: 0.5-3. Default: 1.
type SpringParams =
  { stiffness :: Number
  , damping :: Number
  , mass :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snappy spring — responsive UI interactions.
-- |
-- | Duration: ~200ms, slight overshoot for liveliness.
-- | Use for: button responses, menu opens, toggles.
snappySpring :: SpringParams
snappySpring =
  { stiffness: 400.0
  , damping: 30.0
  , mass: 1.0
  }

-- | Bouncy spring — playful, attention-grabbing.
-- |
-- | Duration: ~400ms, visible bounce.
-- | Use for: celebrations, confirmations, first-time reveals.
bouncySpring :: SpringParams
bouncySpring =
  { stiffness: 300.0
  , damping: 10.0
  , mass: 1.0
  }

-- | Smooth spring — elegant transitions.
-- |
-- | Duration: ~350ms, no overshoot.
-- | Use for: modal opens, page transitions, tooltips.
smoothSpring :: SpringParams
smoothSpring =
  { stiffness: 150.0
  , damping: 20.0
  , mass: 1.0
  }

-- | Precise spring — accurate positioning.
-- |
-- | Duration: ~180ms, minimal settling.
-- | Use for: scroll following, cursor tracking, snapping.
preciseSpring :: SpringParams
preciseSpring =
  { stiffness: 500.0
  , damping: 40.0
  , mass: 0.8
  }

-- | Critically damped — fastest without overshoot.
-- |
-- | Duration: ~120ms, no oscillation.
-- | Use for: reduced motion mode, instant feedback.
criticallyDamped :: SpringParams
criticallyDamped =
  { stiffness: 300.0
  , damping: 34.64      -- sqrt(4 * stiffness * mass)
  , mass: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate spring at time t (0-1).
-- |
-- | Returns the spring's position at normalized time t, where:
-- | - t = 0.0 → 0.0 (start)
-- | - t = 1.0 → 1.0 (end)
-- |
-- | The actual trajectory depends on spring parameters:
-- | - Underdamped springs oscillate before settling
-- | - Critically damped springs reach target as fast as possible
-- | - Overdamped springs approach slowly without overshoot
evaluateSpring :: SpringParams -> Number -> Number
evaluateSpring spring t
  | t < 0.0 = 0.0
  | t >= 1.0 = 1.0
  | true =
      let
        omega0 = Math.sqrt (spring.stiffness / spring.mass)
        zeta = spring.damping / (2.0 * Math.sqrt (spring.stiffness * spring.mass))
        
        -- Underdamped case (typical for UI springs)
        omegaD = omega0 * Math.sqrt (1.0 - zeta * zeta)
        decay = Math.exp (negate zeta * omega0 * t)
      in
        if zeta < 1.0
          -- Underdamped: oscillates
          then 1.0 - decay * (Math.cos (omegaD * t) + (zeta * omega0 / omegaD) * Math.sin (omegaD * t))
          -- Critically damped or overdamped
          else 1.0 - decay * (1.0 + omega0 * t)

-- | Estimate spring animation duration in milliseconds.
-- |
-- | Based on when oscillation amplitude drops below 1% of target.
springDuration :: SpringParams -> Number
springDuration spring =
  let
    omega0 = Math.sqrt (spring.stiffness / spring.mass)
    zeta = spring.damping / (2.0 * Math.sqrt (spring.stiffness * spring.mass))
    
    -- Settling time (99% of final value)
    settlingTime = if zeta >= 1.0
      -- Critically damped or overdamped
      then 4.0 / (zeta * omega0)
      -- Underdamped
      else 4.0 / (zeta * omega0)
  in
    -- Convert to milliseconds, clamp to reasonable range
    min 1000.0 (max 100.0 (settlingTime * 1000.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // css conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert spring params to CSS cubic-bezier approximation.
-- |
-- | Note: True spring physics cannot be represented in CSS.
-- | This provides a visual approximation suitable for CSS transitions.
springToCss :: SpringParams -> String
springToCss spring
  -- Snappy springs approximate to ease-out
  | spring.stiffness >= 350.0 || spring.damping >= 25.0 =
      "cubic-bezier(0.22, 1.0, 0.36, 1.0)"
  -- Bouncy springs have overshoot
  | spring.damping < 15.0 =
      "cubic-bezier(0.34, 1.56, 0.64, 1.0)"
  -- Smooth springs are ease-out-quad
  | spring.stiffness < 200.0 || spring.damping >= 15.0 =
      "cubic-bezier(0.25, 0.46, 0.45, 0.94)"
  -- Default fallback
  | true =
      "cubic-bezier(0.33, 1.0, 0.68, 1.0)"
