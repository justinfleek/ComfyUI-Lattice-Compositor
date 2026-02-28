-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // temporal // spring
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spring Physics Atoms — Parameters for spring-based animation.
-- |
-- | Spring animations create natural, physics-based motion that feels organic
-- | and responsive. Unlike bezier easing, spring animations have no fixed
-- | duration — they settle when the spring reaches equilibrium.
-- |
-- | ## The Spring Model
-- |
-- | Based on the damped harmonic oscillator:
-- |   F = -kx - cv + ma
-- |
-- | Where:
-- | - **k** = spring stiffness (how "tight" the spring is)
-- | - **c** = damping coefficient (how quickly oscillation fades)
-- | - **m** = mass (affects acceleration response)
-- | - **v** = velocity (current speed of motion)
-- | - **x** = displacement (distance from target)
-- |
-- | ## Common Presets
-- |
-- | - **Gentle**: Low stiffness, high damping (slow, smooth settle)
-- | - **Wobbly**: High stiffness, low damping (bouncy, playful)
-- | - **Stiff**: High stiffness, high damping (snappy, responsive)
-- | - **Slow**: Low stiffness, low damping (lazy, dramatic)

module Hydrogen.Schema.Temporal.Spring
  ( -- * Mass
    Mass
  , mass
  , unsafeMass
  , unwrapMass
  , massToNumber
  
  -- * Stiffness
  , Stiffness
  , stiffness
  , unsafeStiffness
  , unwrapStiffness
  , stiffnessToNumber
  
  -- * Damping
  , Damping
  , damping
  , unsafeDamping
  , unwrapDamping
  , dampingToNumber
  , criticalDamping
  
  -- * Velocity
  , Velocity
  , velocity
  , unsafeVelocity
  , unwrapVelocity
  , velocityToNumber
  , zeroVelocity
  
  -- * Rest Thresholds
  , RestDelta
  , restDelta
  , unsafeRestDelta
  , unwrapRestDelta
  
  , RestSpeed
  , restSpeed
  , unsafeRestSpeed
  , unwrapRestSpeed
  
  -- * Bounds
  , massBounds
  , stiffnessBounds
  , dampingBounds
  , velocityBounds
  , restDeltaBounds
  , restSpeedBounds
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
  , negate
  , (*)
  , (<>)
  , (<)
  )

import Data.Number (sqrt) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // mass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mass of the animated object (> 0)
-- |
-- | Higher mass means slower acceleration and deceleration.
-- | Most animations use mass = 1.0 as a baseline.
newtype Mass = Mass Number

derive instance eqMass :: Eq Mass
derive instance ordMass :: Ord Mass

instance showMass :: Show Mass where
  show (Mass m) = "(Mass " <> show m <> ")"

-- | Create Mass, clamping to minimum of 0.01
mass :: Number -> Mass
mass m
  | m < 0.01 = Mass 0.01
  | otherwise = Mass m

-- | Create Mass without bounds checking
unsafeMass :: Number -> Mass
unsafeMass = Mass

-- | Extract raw Number from Mass
unwrapMass :: Mass -> Number
unwrapMass (Mass m) = m

-- | Alias for unwrapMass
massToNumber :: Mass -> Number
massToNumber = unwrapMass

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // stiffness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring constant k (> 0)
-- |
-- | Higher stiffness = faster animation, more "snappy" feel.
-- | Lower stiffness = slower animation, more "lazy" feel.
-- |
-- | Common values:
-- | - 100-200: Gentle, slow
-- | - 200-400: Normal, balanced
-- | - 400-800: Snappy, responsive
-- | - 800+: Very stiff, almost instant
newtype Stiffness = Stiffness Number

derive instance eqStiffness :: Eq Stiffness
derive instance ordStiffness :: Ord Stiffness

instance showStiffness :: Show Stiffness where
  show (Stiffness k) = "(Stiffness " <> show k <> ")"

-- | Create Stiffness, clamping to minimum of 0.01
stiffness :: Number -> Stiffness
stiffness k
  | k < 0.01 = Stiffness 0.01
  | otherwise = Stiffness k

-- | Create Stiffness without bounds checking
unsafeStiffness :: Number -> Stiffness
unsafeStiffness = Stiffness

-- | Extract raw Number from Stiffness
unwrapStiffness :: Stiffness -> Number
unwrapStiffness (Stiffness k) = k

-- | Alias for unwrapStiffness
stiffnessToNumber :: Stiffness -> Number
stiffnessToNumber = unwrapStiffness

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // damping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Damping coefficient c (>= 0)
-- |
-- | Controls how quickly oscillation fades:
-- | - 0: No damping, oscillates forever
-- | - < critical: Underdamped, some overshoot/bounce
-- | - = critical: Critically damped, fastest settle without overshoot
-- | - > critical: Overdamped, slow settle without overshoot
-- |
-- | Common values:
-- | - 10-20: Very bouncy
-- | - 20-30: Slightly bouncy
-- | - 30-50: Balanced
-- | - 50+: Little to no bounce
newtype Damping = Damping Number

derive instance eqDamping :: Eq Damping
derive instance ordDamping :: Ord Damping

instance showDamping :: Show Damping where
  show (Damping c) = "(Damping " <> show c <> ")"

-- | Create Damping, clamping to minimum of 0
damping :: Number -> Damping
damping c
  | c < 0.0 = Damping 0.0
  | otherwise = Damping c

-- | Create Damping without bounds checking
unsafeDamping :: Number -> Damping
unsafeDamping = Damping

-- | Extract raw Number from Damping
unwrapDamping :: Damping -> Number
unwrapDamping (Damping c) = c

-- | Alias for unwrapDamping
dampingToNumber :: Damping -> Number
dampingToNumber = unwrapDamping

-- | Calculate critical damping for given mass and stiffness
-- |
-- | Critical damping = 2 * sqrt(mass * stiffness)
-- | This is the minimum damping needed to prevent oscillation.
-- |
-- | ```purescript
-- | criticalDamping (mass 1.0) (stiffness 100.0)  -- Damping 20.0
-- | ```
criticalDamping :: Mass -> Stiffness -> Damping
criticalDamping (Mass m) (Stiffness k) = Damping (2.0 * Number.sqrt (m * k))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // velocity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Initial velocity (can be positive or negative)
-- |
-- | Used to "throw" an animation with initial momentum.
-- | Positive = moving toward target, Negative = moving away.
-- |
-- | Most animations start with velocity = 0.
newtype Velocity = Velocity Number

derive instance eqVelocity :: Eq Velocity
derive instance ordVelocity :: Ord Velocity

instance showVelocity :: Show Velocity where
  show (Velocity v) = "(Velocity " <> show v <> ")"

-- | Create Velocity (unbounded, any value allowed)
velocity :: Number -> Velocity
velocity = Velocity

-- | Alias for velocity constructor
unsafeVelocity :: Number -> Velocity
unsafeVelocity = Velocity

-- | Extract raw Number from Velocity
unwrapVelocity :: Velocity -> Number
unwrapVelocity (Velocity v) = v

-- | Alias for unwrapVelocity
velocityToNumber :: Velocity -> Number
velocityToNumber = unwrapVelocity

-- | Zero velocity (most common starting point)
zeroVelocity :: Velocity
zeroVelocity = Velocity 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // rest delta
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rest threshold for displacement (> 0)
-- |
-- | Animation is considered "at rest" when displacement from target
-- | is less than this value. Smaller = more precision, longer animation.
-- |
-- | Common values:
-- | - 0.01: High precision (for important UI)
-- | - 0.1: Normal precision (most animations)
-- | - 1.0: Low precision (background effects)
newtype RestDelta = RestDelta Number

derive instance eqRestDelta :: Eq RestDelta
derive instance ordRestDelta :: Ord RestDelta

instance showRestDelta :: Show RestDelta where
  show (RestDelta d) = "(RestDelta " <> show d <> ")"

-- | Create RestDelta, clamping to minimum of 0.0001
restDelta :: Number -> RestDelta
restDelta d
  | d < 0.0001 = RestDelta 0.0001
  | otherwise = RestDelta d

-- | Create RestDelta without bounds checking
unsafeRestDelta :: Number -> RestDelta
unsafeRestDelta = RestDelta

-- | Extract raw Number from RestDelta
unwrapRestDelta :: RestDelta -> Number
unwrapRestDelta (RestDelta d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // rest speed
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rest threshold for velocity (> 0)
-- |
-- | Animation is considered "at rest" when velocity is less than this value.
-- | Used together with RestDelta — both must be satisfied for rest.
-- |
-- | Common values:
-- | - 0.01: High precision
-- | - 0.1: Normal precision
-- | - 1.0: Low precision
newtype RestSpeed = RestSpeed Number

derive instance eqRestSpeed :: Eq RestSpeed
derive instance ordRestSpeed :: Ord RestSpeed

instance showRestSpeed :: Show RestSpeed where
  show (RestSpeed s) = "(RestSpeed " <> show s <> ")"

-- | Create RestSpeed, clamping to minimum of 0.0001
restSpeed :: Number -> RestSpeed
restSpeed s
  | s < 0.0001 = RestSpeed 0.0001
  | otherwise = RestSpeed s

-- | Create RestSpeed without bounds checking
unsafeRestSpeed :: Number -> RestSpeed
unsafeRestSpeed = RestSpeed

-- | Extract raw Number from RestSpeed
unwrapRestSpeed :: RestSpeed -> Number
unwrapRestSpeed (RestSpeed s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Mass
massBounds :: Bounded.NumberBounds
massBounds = Bounded.numberBounds 0.01 1000.0 "mass" 
  "Spring mass (0.01 minimum, typical range 0.1-10)"

-- | Bounds for Stiffness
stiffnessBounds :: Bounded.NumberBounds
stiffnessBounds = Bounded.numberBounds 0.01 10000.0 "stiffness"
  "Spring stiffness constant k (0.01 minimum, typical range 100-500)"

-- | Bounds for Damping
dampingBounds :: Bounded.NumberBounds
dampingBounds = Bounded.numberBounds 0.0 1000.0 "damping"
  "Spring damping coefficient c (0 = no damping, typical range 10-50)"

-- | Bounds for Velocity
velocityBounds :: Bounded.NumberBounds
velocityBounds = Bounded.numberBounds (-10000.0) 10000.0 "velocity"
  "Initial velocity (unbounded in principle, practical range -1000 to 1000)"

-- | Bounds for RestDelta
restDeltaBounds :: Bounded.NumberBounds
restDeltaBounds = Bounded.numberBounds 0.0001 100.0 "restDelta"
  "Rest displacement threshold (smaller = more precision)"

-- | Bounds for RestSpeed
restSpeedBounds :: Bounded.NumberBounds
restSpeedBounds = Bounded.numberBounds 0.0001 100.0 "restSpeed"
  "Rest velocity threshold (smaller = more precision)"
