-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // motion // spring
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spring physics animations
-- |
-- | Physics-based spring animation calculations.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.Spring as Spring
-- |
-- | -- Create a spring config
-- | let spring = Spring.springConfig 170.0 26.0  -- stiffness, damping
-- |
-- | -- Preset springs
-- | Spring.springDefault
-- | Spring.springGentle
-- | Spring.springWobbly
-- | Spring.springStiff
-- |
-- | -- Calculate spring value at time t
-- | Spring.springValue spring 0.0 1.0 0.5  -- from, to, progress
-- | ```
module Hydrogen.Motion.Spring
  ( -- * Spring Configuration
    SpringConfig
  , springConfig
  , springConfigFull
    -- * Presets
  , springDefault
  , springGentle
  , springWobbly
  , springStiff
  , springSlow
  , springMolasses
    -- * Spring Calculation
  , springValue
  , springVelocity
  , isAtRest
    -- * Fixed Timestep Simulation
    -- | For stable physics at variable frame rates
  , SpringInstance
  , springInstance
  , tickSpring
  , tickSpringFixed
  , springPosition
  , springInstanceVelocity
  , springAtRest
  , setTarget
  , setPosition
  , resetSpring
    -- * Critical Damping
  , criticalDamping
  , dampingRatio
  , isCriticallyDamped
  , isOverdamped
  , isUnderdamped
    -- * CSS Spring
  , springToCubicBezier
  ) where

import Prelude

import Data.Number (sqrt, exp, cos, sin, abs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // spring configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring configuration
-- |
-- | - stiffness: Spring constant (higher = faster)
-- | - damping: Resistance (higher = less bouncy)
-- | - mass: Inertia (higher = slower)
-- | - velocity: Initial velocity
type SpringConfig =
  { stiffness :: Number
  , damping :: Number
  , mass :: Number
  , velocity :: Number
  , precision :: Number  -- Threshold for considering spring at rest
  }

-- | Create a spring configuration
springConfig :: Number -> Number -> SpringConfig
springConfig stiffness damping =
  { stiffness
  , damping
  , mass: 1.0
  , velocity: 0.0
  , precision: 0.01
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default spring (balanced)
springDefault :: SpringConfig
springDefault = springConfig 170.0 26.0

-- | Gentle spring (smooth, no bounce)
springGentle :: SpringConfig
springGentle = springConfig 120.0 14.0

-- | Wobbly spring (bouncy)
springWobbly :: SpringConfig
springWobbly = springConfig 180.0 12.0

-- | Stiff spring (fast, minimal bounce)
springStiff :: SpringConfig
springStiff = springConfig 210.0 20.0

-- | Slow spring (gradual)
springSlow :: SpringConfig
springSlow = springConfig 280.0 60.0

-- | Molasses (very slow, heavy)
springMolasses :: SpringConfig
springMolasses = springConfig 280.0 120.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // spring calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate spring value at time t (0 to 1)
-- |
-- | Uses damped harmonic oscillator equation.
springValue :: SpringConfig -> Number -> Number -> Number -> Number
springValue config from to t =
  let
    delta = to - from
    zeta = dampingRatio config
    angularFreq = sqrt (config.stiffness / config.mass)
    
    -- Underdamped (bouncy) case
    dampedFreq = angularFreq * sqrt (1.0 - zeta * zeta)
    
    -- Exponential decay
    expDecay = exp (negate zeta * angularFreq * t)
    
    -- Oscillation
    oscillation = cos (dampedFreq * t) + 
                  (zeta * angularFreq / dampedFreq) * sin (dampedFreq * t)
  in
    if zeta >= 1.0
      -- Critically damped or overdamped
      then to - delta * expDecay * (1.0 + angularFreq * t)
      -- Underdamped (bouncy)
      else to - delta * expDecay * oscillation

-- | Calculate spring velocity at time t
springVelocity :: SpringConfig -> Number -> Number -> Number -> Number
springVelocity config from to t =
  let
    delta = to - from
    zeta = dampingRatio config
    angularFreq = sqrt (config.stiffness / config.mass)
    dampedFreq = angularFreq * sqrt (1.0 - zeta * zeta)
    expDecay = exp (negate zeta * angularFreq * t)
  in
    if zeta >= 1.0
      then delta * angularFreq * angularFreq * t * expDecay
      else delta * expDecay * dampedFreq * sin (dampedFreq * t)

-- | Check if spring is at rest (within precision threshold)
isAtRest :: SpringConfig -> Number -> Number -> Number -> Boolean
isAtRest config from to t =
  let
    currentValue = springValue config from to t
    currentVelocity = springVelocity config from to t
  in
    abs (currentValue - to) < config.precision && 
    abs currentVelocity < config.precision

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css spring
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximate spring as cubic-bezier for CSS transitions
-- |
-- | Note: This is an approximation - true spring physics requires JS.
springToCubicBezier :: SpringConfig -> String
springToCubicBezier config =
  let
    dr = dampingRatio config
    -- Approximate cubic bezier values based on damping
    x1 = 0.25
    y1 = if dr < 0.5 then 0.1 else 0.25
    x2 = 0.25
    y2 = if dr < 0.5 then 1.5 else 1.0
  in
    "cubic-bezier(" <> show x1 <> ", " <> show y1 <> ", " <> show x2 <> ", " <> show y2 <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // critical damping ratio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate critical damping coefficient
-- |
-- | Critical damping is the minimum damping that prevents oscillation.
-- | At critical damping (ζ = 1.0), the spring returns to rest as fast as
-- | possible without overshooting.
-- |
-- | ```
-- | c_critical = 2 * √(k * m)
-- | ```
criticalDamping :: SpringConfig -> Number
criticalDamping config = 2.0 * sqrt (config.stiffness * config.mass)

-- | Calculate damping ratio (ζ)
-- |
-- | - ζ < 1.0: Underdamped (oscillates)
-- | - ζ = 1.0: Critically damped (fastest return without overshoot)
-- | - ζ > 1.0: Overdamped (slow return, no oscillation)
dampingRatio :: SpringConfig -> Number
dampingRatio config = config.damping / criticalDamping config

-- | Check if spring is critically damped (ζ ≈ 1.0)
isCriticallyDamped :: SpringConfig -> Boolean
isCriticallyDamped config = 
  let dr = dampingRatio config
  in dr >= 0.99 && dr <= 1.01

-- | Check if spring is overdamped (ζ > 1.0)
isOverdamped :: SpringConfig -> Boolean
isOverdamped config = dampingRatio config > 1.0

-- | Check if spring is underdamped (ζ < 1.0)
isUnderdamped :: SpringConfig -> Boolean
isUnderdamped config = dampingRatio config < 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // fixed timestep simulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | A running spring instance with state
-- |
-- | Unlike SpringConfig which defines spring properties, SpringInstance
-- | tracks the current state of a spring simulation.
-- |
-- | ## Why Fixed Timestep?
-- |
-- | Semi-implicit Euler integration is stable for constant timesteps but
-- | can become unstable with variable frame times. At high stiffness
-- | (k > 1000) and variable dt (16.67ms → 33.33ms during a hitch),
-- | springs can overshoot or explode.
-- |
-- | The accumulator pattern ensures physics runs at a fixed rate:
-- |
-- | ```
-- | while (accumulator >= fixedDt) {
-- |   stepPhysics(fixedDt)
-- |   accumulator -= fixedDt
-- | }
-- | ```
-- |
-- | Remaining time is stored for the next frame.
type SpringInstance =
  { config :: SpringConfig
  , position :: Number        -- Current position
  , velocity :: Number        -- Current velocity
  , target :: Number          -- Target position
  , accumulator :: Number     -- Time accumulator for fixed timestep
  , fixedDt :: Number         -- Fixed timestep (e.g., 1/120 second)
  }

-- | Create a spring instance
springInstance :: SpringConfig -> Number -> Number -> SpringInstance
springInstance config start target =
  { config
  , position: start
  , velocity: config.velocity
  , target
  , accumulator: 0.0
  , fixedDt: 1.0 / 120.0  -- 120 Hz default (8.33ms)
  }

-- | Create spring config with all parameters
springConfigFull 
  :: Number 
  -> Number 
  -> Number 
  -> Number 
  -> Number 
  -> SpringConfig
springConfigFull stiffness damping mass velocity precision =
  { stiffness, damping, mass, velocity, precision }

-- | Tick spring simulation with variable delta time
-- |
-- | Uses accumulator pattern for stable physics regardless of frame rate.
-- | This is the recommended way to update springs each frame.
tickSpring :: Number -> SpringInstance -> SpringInstance
tickSpring dt spring =
  let
    -- Add frame time to accumulator
    newAccumulator = spring.accumulator + dt
  in
    tickSpringFixed spring { accumulator = newAccumulator }

-- | Internal: Process accumulated time in fixed timesteps
-- |
-- | Uses semi-implicit Euler (symplectic Euler) for energy conservation.
-- | Velocity is updated first, then position uses new velocity.
tickSpringFixed :: SpringInstance -> SpringInstance
tickSpringFixed spring =
  if spring.accumulator >= spring.fixedDt
    then
      let
        stepped = stepSpring spring.fixedDt spring
        reduced = stepped { accumulator = stepped.accumulator - stepped.fixedDt }
      in
        tickSpringFixed reduced
    else
      spring

-- | Single physics step using semi-implicit Euler
-- |
-- | Semi-implicit Euler is first-order accurate but symplectic,
-- | meaning it conserves energy over time (won't explode or damp
-- | incorrectly for constant timesteps).
-- |
-- | ```
-- | v' = v + a * dt       (velocity first)
-- | x' = x + v' * dt      (position uses new velocity)
-- | ```
stepSpring :: Number -> SpringInstance -> SpringInstance
stepSpring dt spring =
  let
    k = spring.config.stiffness
    c = spring.config.damping
    m = spring.config.mass
    
    -- Displacement from target
    x = spring.position - spring.target
    v = spring.velocity
    
    -- Spring force: F = -kx - cv
    -- Acceleration: a = F/m = (-kx - cv) / m
    acceleration = (negate k * x - c * v) / m
    
    -- Semi-implicit Euler: update velocity first
    newVelocity = v + acceleration * dt
    
    -- Then update position with new velocity
    newPosition = spring.position + newVelocity * dt
  in
    spring
      { position = newPosition
      , velocity = newVelocity
      }

-- | Get current spring position
springPosition :: SpringInstance -> Number
springPosition spring = spring.position

-- | Get current spring velocity
springInstanceVelocity :: SpringInstance -> Number
springInstanceVelocity spring = spring.velocity

-- | Check if spring is at rest
springAtRest :: SpringInstance -> Boolean
springAtRest spring =
  abs (spring.position - spring.target) < spring.config.precision &&
  abs spring.velocity < spring.config.precision

-- | Set new target position
setTarget :: Number -> SpringInstance -> SpringInstance
setTarget newTarget spring = spring { target = newTarget }

-- | Set current position (e.g., for drag interactions)
setPosition :: Number -> SpringInstance -> SpringInstance
setPosition newPosition spring = spring { position = newPosition, velocity = 0.0 }

-- | Reset spring to start position
resetSpring :: Number -> SpringInstance -> SpringInstance
resetSpring newPosition spring = 
  spring 
    { position = newPosition
    , velocity = 0.0
    , accumulator = 0.0
    }
