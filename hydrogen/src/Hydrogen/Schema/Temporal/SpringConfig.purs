-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // temporal // spring-config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SpringConfig — Molecule composing spring physics parameters.
-- |
-- | A complete configuration for spring-based animation, combining:
-- | - Mass (inertia)
-- | - Stiffness (spring constant)
-- | - Damping (friction)
-- | - Initial velocity
-- | - Rest thresholds
-- |
-- | ## Presets
-- |
-- | Common spring configurations for different animation feels:
-- | - **gentle**: Slow, smooth, no bounce
-- | - **wobbly**: Fast, bouncy, playful
-- | - **stiff**: Snappy, responsive
-- | - **slow**: Dramatic, lazy motion
-- | - **molasses**: Very slow, syrupy

module Hydrogen.Schema.Temporal.SpringConfig
  ( SpringConfig(..)
  , springConfig
  , springConfigWithVelocity
  
  -- * Accessors
  , configMass
  , configStiffness
  , configDamping
  , configVelocity
  , configRestDelta
  , configRestSpeed
  
  -- * Derived Properties
  , isUnderdamped
  , isOverdamped
  , isCriticallyDamped
  , dampingRatio
  , naturalFrequency
  
  -- * Presets
  , gentle
  , wobbly
  , stiff
  , slow
  , molasses
  , noWobble
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (/)
  , (*)
  , (<>)
  , (<)
  , (>)
  , (&&)
  )

import Data.Number (sqrt) as Number
import Hydrogen.Schema.Temporal.Spring 
  ( Mass
  , Stiffness
  , Damping
  , Velocity
  , RestDelta
  , RestSpeed
  , mass
  , stiffness
  , damping
  , zeroVelocity
  , restDelta
  , restSpeed
  , unwrapMass
  , unwrapStiffness
  , unwrapDamping
  , criticalDamping
  , unwrapDamping
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spring config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete spring physics configuration
-- |
-- | All parameters needed to simulate a damped harmonic oscillator.
newtype SpringConfig = SpringConfig
  { mass :: Mass
  , stiffness :: Stiffness
  , damping :: Damping
  , velocity :: Velocity
  , restDelta :: RestDelta
  , restSpeed :: RestSpeed
  }

derive instance eqSpringConfig :: Eq SpringConfig
derive instance ordSpringConfig :: Ord SpringConfig

instance showSpringConfig :: Show SpringConfig where
  show (SpringConfig c) = 
    "(SpringConfig mass:" <> show c.mass 
    <> " stiffness:" <> show c.stiffness 
    <> " damping:" <> show c.damping 
    <> " velocity:" <> show c.velocity
    <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create SpringConfig with default velocity (0) and rest thresholds
-- |
-- | ```purescript
-- | springConfig (mass 1.0) (stiffness 170.0) (damping 26.0)
-- | ```
springConfig :: Mass -> Stiffness -> Damping -> SpringConfig
springConfig m s d = SpringConfig
  { mass: m
  , stiffness: s
  , damping: d
  , velocity: zeroVelocity
  , restDelta: restDelta 0.01
  , restSpeed: restSpeed 0.01
  }

-- | Create SpringConfig with custom initial velocity
-- |
-- | ```purescript
-- | springConfigWithVelocity (mass 1.0) (stiffness 170.0) (damping 26.0) (velocity 5.0)
-- | ```
springConfigWithVelocity :: Mass -> Stiffness -> Damping -> Velocity -> SpringConfig
springConfigWithVelocity m s d v = SpringConfig
  { mass: m
  , stiffness: s
  , damping: d
  , velocity: v
  , restDelta: restDelta 0.01
  , restSpeed: restSpeed 0.01
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get mass from config
configMass :: SpringConfig -> Mass
configMass (SpringConfig c) = c.mass

-- | Get stiffness from config
configStiffness :: SpringConfig -> Stiffness
configStiffness (SpringConfig c) = c.stiffness

-- | Get damping from config
configDamping :: SpringConfig -> Damping
configDamping (SpringConfig c) = c.damping

-- | Get initial velocity from config
configVelocity :: SpringConfig -> Velocity
configVelocity (SpringConfig c) = c.velocity

-- | Get rest delta threshold from config
configRestDelta :: SpringConfig -> RestDelta
configRestDelta (SpringConfig c) = c.restDelta

-- | Get rest speed threshold from config
configRestSpeed :: SpringConfig -> RestSpeed
configRestSpeed (SpringConfig c) = c.restSpeed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // derived properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if spring is underdamped (will oscillate/bounce)
-- |
-- | Damping ratio < 1
isUnderdamped :: SpringConfig -> Boolean
isUnderdamped cfg = dampingRatio cfg < 1.0

-- | Check if spring is overdamped (no oscillation, slow settle)
-- |
-- | Damping ratio > 1
isOverdamped :: SpringConfig -> Boolean
isOverdamped cfg = dampingRatio cfg > 1.0

-- | Check if spring is critically damped (fastest settle without oscillation)
-- |
-- | Damping ratio == 1 (within tolerance)
isCriticallyDamped :: SpringConfig -> Boolean
isCriticallyDamped cfg = 
  let ratio = dampingRatio cfg
  in ratio > 0.99 && ratio < 1.01

-- | Calculate damping ratio (zeta)
-- |
-- | zeta = c / (2 * sqrt(m * k))
-- |
-- | - zeta < 1: underdamped (oscillates)
-- | - zeta = 1: critically damped (fastest non-oscillating)
-- | - zeta > 1: overdamped (slow settle)
dampingRatio :: SpringConfig -> Number
dampingRatio (SpringConfig c) =
  let m = unwrapMass c.mass
      k = unwrapStiffness c.stiffness
      d = unwrapDamping c.damping
      critical = 2.0 * Number.sqrt (m * k)
  in d / critical

-- | Calculate natural frequency (omega_n)
-- |
-- | omega_n = sqrt(k / m)
-- |
-- | Higher natural frequency = faster oscillation
naturalFrequency :: SpringConfig -> Number
naturalFrequency (SpringConfig c) =
  let m = unwrapMass c.mass
      k = unwrapStiffness c.stiffness
  in Number.sqrt (k / m)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gentle spring: slow, smooth, minimal bounce
-- |
-- | Good for: background elements, subtle transitions
gentle :: SpringConfig
gentle = springConfig (mass 1.0) (stiffness 120.0) (damping 14.0)

-- | Wobbly spring: fast, bouncy, playful
-- |
-- | Good for: playful UI, notifications, attention-grabbing
wobbly :: SpringConfig
wobbly = springConfig (mass 1.0) (stiffness 180.0) (damping 12.0)

-- | Stiff spring: snappy, responsive, minimal overshoot
-- |
-- | Good for: buttons, toggles, responsive UI
stiff :: SpringConfig
stiff = springConfig (mass 1.0) (stiffness 400.0) (damping 30.0)

-- | Slow spring: dramatic, lazy motion
-- |
-- | Good for: page transitions, hero animations
slow :: SpringConfig
slow = springConfig (mass 1.0) (stiffness 100.0) (damping 20.0)

-- | Molasses spring: very slow, syrupy feel
-- |
-- | Good for: dramatic reveals, emphasis
molasses :: SpringConfig
molasses = springConfig (mass 1.0) (stiffness 80.0) (damping 25.0)

-- | No wobble: critically damped (no overshoot)
-- |
-- | Good for: precise positioning, no playfulness desired
noWobble :: SpringConfig
noWobble = 
  let m = mass 1.0
      s = stiffness 170.0
  in springConfig m s (criticalDamping m s)
