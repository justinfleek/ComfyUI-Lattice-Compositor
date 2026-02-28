-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // sensation // force
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Force Atoms — Physics sensation primitives.
-- |
-- | Force sensation captures the physical forces acting on the agent:
-- |   - What direction is gravity pulling me?
-- |   - What external forces are being applied?
-- |   - How much resistance am I experiencing?
-- |   - Was I just impacted?
-- |
-- | ## SCHEMA.md Reference (Pillar 15: Sensation — Force)
-- |
-- | | Name           | Type   | Min  | Max  | Behavior | Notes                      |
-- | |----------------|--------|------|------|----------|----------------------------|
-- | | GravityMag     | Number | 0    | none | finite   | Gravity strength (m/s²)    |
-- | | Drag           | Number | 0    | 1    | clamps   | Resistance from medium     |
-- | | Buoyancy       | Number | -1   | 1    | clamps   | Upward/downward force      |
-- | | ImpactIntensity| Number | 0    | 1    | clamps   | Recent collision severity  |
-- | | Acceleration   | Number | none | none | finite   | Current acceleration (m/s²)|
-- | | Velocity       | Number | 0    | none | finite   | Current speed (m/s)        |
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Number (sqrt)
-- |
-- | ## Dependents
-- | - Sensation/Molecules.purs (MovementState, EnvironmentState)
-- | - Sensation/Compounds.purs (Distress, Disorientation)

module Hydrogen.Schema.Sensation.Force
  ( -- * GravityVector (3D direction + magnitude)
    GravityVector
  , mkGravityVector
  , gravityX
  , gravityY
  , gravityZ
  , gravityMagnitude
  , gravityDirection
  , gravityEarth
  , gravityMoon
  , gravityZero
  , gravityDown
    -- * ExternalForce (3D vector)
  , ExternalForce
  , mkExternalForce
  , forceX
  , forceY
  , forceZ
  , forceMagnitude
  , forceNone
  , forceLight
  , forceStrong
  , addForces
  , scaleForce
    -- * Drag (0-1, clamps)
  , Drag
  , mkDrag
  , unwrapDrag
  , dragNone
  , dragAir
  , dragWater
  , dragViscous
  , dragMaximum
  , isLowDrag
  , isHighDrag
    -- * Buoyancy (-1 to 1, clamps)
  , Buoyancy
  , mkBuoyancy
  , unwrapBuoyancy
  , buoyancySinking
  , buoyancyNeutral
  , buoyancyFloating
  , buoyancyRising
  , isSinking
  , isFloating
    -- * ImpactIntensity (0-1, clamps)
  , ImpactIntensity
  , mkImpactIntensity
  , unwrapImpactIntensity
  , impactNone
  , impactLight
  , impactModerate
  , impactHeavy
  , impactSevere
  , wasImpacted
  , wasSeverelyImpacted
    -- * Acceleration (signed, finite)
  , Acceleration
  , mkAcceleration
  , unwrapAcceleration
  , accelerationNone
  , accelerationLight
  , accelerationStrong
  , decelerating
  , accelerating
    -- * Velocity (0+, finite)
  , Velocity
  , mkVelocity
  , unwrapVelocity
  , velocityStationary
  , velocitySlow
  , velocityModerate
  , velocityFast
  , velocityExtreme
  , isStationary
  , isMoving
  , isMovingFast
    -- * Momentum (3D vector)
  , Momentum
  , mkMomentum
  , momentumX
  , momentumY
  , momentumZ
  , momentumMagnitude
  , momentumNone
  ) where

import Prelude

import Data.Number (sqrt) as Num

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // gravity // vector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gravity vector (3D direction + magnitude).
-- |
-- | The direction and strength of gravitational force acting on the agent.
-- | Represented as a 3D vector where magnitude = acceleration in m/s².
type GravityVector =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Create a gravity vector (stores raw values)
mkGravityVector :: Number -> Number -> Number -> GravityVector
mkGravityVector x y z = { x, y, z }

-- | Get X component
gravityX :: GravityVector -> Number
gravityX g = g.x

-- | Get Y component
gravityY :: GravityVector -> Number
gravityY g = g.y

-- | Get Z component
gravityZ :: GravityVector -> Number
gravityZ g = g.z

-- | Get gravity magnitude (m/s²)
gravityMagnitude :: GravityVector -> Number
gravityMagnitude g = Num.sqrt (g.x * g.x + g.y * g.y + g.z * g.z)

-- | Get normalized gravity direction
gravityDirection :: GravityVector -> GravityVector
gravityDirection g =
  let mag = gravityMagnitude g
      safeMag = if mag < 0.0001 then 1.0 else mag
  in { x: g.x / safeMag, y: g.y / safeMag, z: g.z / safeMag }

-- | Earth gravity (9.81 m/s² downward)
gravityEarth :: GravityVector
gravityEarth = { x: 0.0, y: -9.81, z: 0.0 }

-- | Moon gravity (1.62 m/s² downward)
gravityMoon :: GravityVector
gravityMoon = { x: 0.0, y: -1.62, z: 0.0 }

-- | Zero gravity (weightlessness)
gravityZero :: GravityVector
gravityZero = { x: 0.0, y: 0.0, z: 0.0 }

-- | Generic downward gravity (normalized)
gravityDown :: GravityVector
gravityDown = { x: 0.0, y: -1.0, z: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // external // force
-- ═════════════════════════════════════════════════════════════════════════════

-- | External force vector (3D).
-- |
-- | Forces being applied to the agent from external sources.
-- | Magnitude in Newtons (or normalized force units).
type ExternalForce =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Create an external force
mkExternalForce :: Number -> Number -> Number -> ExternalForce
mkExternalForce x y z = { x, y, z }

-- | Get X component
forceX :: ExternalForce -> Number
forceX f = f.x

-- | Get Y component
forceY :: ExternalForce -> Number
forceY f = f.y

-- | Get Z component
forceZ :: ExternalForce -> Number
forceZ f = f.z

-- | Get force magnitude
forceMagnitude :: ExternalForce -> Number
forceMagnitude f = Num.sqrt (f.x * f.x + f.y * f.y + f.z * f.z)

-- | No external force
forceNone :: ExternalForce
forceNone = { x: 0.0, y: 0.0, z: 0.0 }

-- | Light force (1.0 units forward)
forceLight :: ExternalForce
forceLight = { x: 0.0, y: 0.0, z: 1.0 }

-- | Strong force (10.0 units forward)
forceStrong :: ExternalForce
forceStrong = { x: 0.0, y: 0.0, z: 10.0 }

-- | Add two forces
addForces :: ExternalForce -> ExternalForce -> ExternalForce
addForces a b = { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }

-- | Scale a force by a factor
scaleForce :: Number -> ExternalForce -> ExternalForce
scaleForce s f = { x: f.x * s, y: f.y * s, z: f.z * s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // drag
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drag coefficient (0 to 1, clamps).
-- |
-- | Resistance from the medium the agent is moving through.
-- |   0.0 = vacuum (no resistance)
-- |   0.2 = air
-- |   0.5 = water
-- |   1.0 = maximum viscous resistance
newtype Drag = Drag Number

derive instance eqDrag :: Eq Drag
derive instance ordDrag :: Ord Drag

instance showDrag :: Show Drag where
  show (Drag n) = "Drag(" <> show n <> ")"

-- | Create a bounded drag (clamps to 0..1)
mkDrag :: Number -> Drag
mkDrag n = Drag (clampNumber 0.0 1.0 n)

-- | Unwrap the drag value
unwrapDrag :: Drag -> Number
unwrapDrag (Drag n) = n

-- | No drag (vacuum)
dragNone :: Drag
dragNone = Drag 0.0

-- | Air drag (0.1)
dragAir :: Drag
dragAir = Drag 0.1

-- | Water drag (0.5)
dragWater :: Drag
dragWater = Drag 0.5

-- | Viscous medium (0.8)
dragViscous :: Drag
dragViscous = Drag 0.8

-- | Maximum drag (1.0)
dragMaximum :: Drag
dragMaximum = Drag 1.0

-- | Is drag low? (drag < 0.2)
isLowDrag :: Drag -> Boolean
isLowDrag (Drag d) = d < 0.2

-- | Is drag high? (drag > 0.5)
isHighDrag :: Drag -> Boolean
isHighDrag (Drag d) = d > 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // buoyancy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buoyancy force (-1 to 1, clamps).
-- |
-- | Net upward or downward force from medium displacement.
-- |   -1.0 = sinking rapidly (denser than medium)
-- |    0.0 = neutrally buoyant
-- |   +1.0 = rising rapidly (lighter than medium)
newtype Buoyancy = Buoyancy Number

derive instance eqBuoyancy :: Eq Buoyancy
derive instance ordBuoyancy :: Ord Buoyancy

instance showBuoyancy :: Show Buoyancy where
  show (Buoyancy n) = "Buoyancy(" <> show n <> ")"

-- | Create a bounded buoyancy (clamps to -1..1)
mkBuoyancy :: Number -> Buoyancy
mkBuoyancy n = Buoyancy (clamp (-1.0) 1.0 n)

-- | Unwrap the buoyancy value
unwrapBuoyancy :: Buoyancy -> Number
unwrapBuoyancy (Buoyancy n) = n

-- | Sinking (-1.0)
buoyancySinking :: Buoyancy
buoyancySinking = Buoyancy (-1.0)

-- | Neutrally buoyant (0.0)
buoyancyNeutral :: Buoyancy
buoyancyNeutral = Buoyancy 0.0

-- | Floating (0.5)
buoyancyFloating :: Buoyancy
buoyancyFloating = Buoyancy 0.5

-- | Rising rapidly (1.0)
buoyancyRising :: Buoyancy
buoyancyRising = Buoyancy 1.0

-- | Is agent sinking? (buoyancy < -0.2)
isSinking :: Buoyancy -> Boolean
isSinking (Buoyancy b) = b < -0.2

-- | Is agent floating? (buoyancy > 0.2)
isFloating :: Buoyancy -> Boolean
isFloating (Buoyancy b) = b > 0.2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // impact // intensity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Recent impact intensity (0 to 1, clamps).
-- |
-- | Severity of the most recent collision or impact.
-- |   0.0 = no recent impact
-- |   0.5 = moderate impact
-- |   1.0 = severe impact (potentially damaging)
-- |
-- | Decays over time; represents recency-weighted collision history.
newtype ImpactIntensity = ImpactIntensity Number

derive instance eqImpactIntensity :: Eq ImpactIntensity
derive instance ordImpactIntensity :: Ord ImpactIntensity

instance showImpactIntensity :: Show ImpactIntensity where
  show (ImpactIntensity n) = "ImpactIntensity(" <> show n <> ")"

-- | Create a bounded impact intensity (clamps to 0..1)
mkImpactIntensity :: Number -> ImpactIntensity
mkImpactIntensity n = ImpactIntensity (clampNumber 0.0 1.0 n)

-- | Unwrap the impact intensity value
unwrapImpactIntensity :: ImpactIntensity -> Number
unwrapImpactIntensity (ImpactIntensity n) = n

-- | No impact (0.0)
impactNone :: ImpactIntensity
impactNone = ImpactIntensity 0.0

-- | Light impact (0.25)
impactLight :: ImpactIntensity
impactLight = ImpactIntensity 0.25

-- | Moderate impact (0.5)
impactModerate :: ImpactIntensity
impactModerate = ImpactIntensity 0.5

-- | Heavy impact (0.75)
impactHeavy :: ImpactIntensity
impactHeavy = ImpactIntensity 0.75

-- | Severe impact (1.0)
impactSevere :: ImpactIntensity
impactSevere = ImpactIntensity 1.0

-- | Was agent recently impacted? (intensity > 0.1)
wasImpacted :: ImpactIntensity -> Boolean
wasImpacted (ImpactIntensity i) = i > 0.1

-- | Was agent severely impacted? (intensity > 0.7)
wasSeverelyImpacted :: ImpactIntensity -> Boolean
wasSeverelyImpacted (ImpactIntensity i) = i > 0.7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // acceleration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Acceleration (signed, finite) in m/s².
-- |
-- | Current rate of velocity change. Positive = speeding up,
-- | negative = slowing down (along primary axis of motion).
newtype Acceleration = Acceleration Number

derive instance eqAcceleration :: Eq Acceleration
derive instance ordAcceleration :: Ord Acceleration

instance showAcceleration :: Show Acceleration where
  show (Acceleration n) = "Acceleration(" <> show n <> "m/s²)"

-- | Create an acceleration (no clamping, finite)
mkAcceleration :: Number -> Acceleration
mkAcceleration = Acceleration

-- | Unwrap the acceleration value
unwrapAcceleration :: Acceleration -> Number
unwrapAcceleration (Acceleration n) = n

-- | No acceleration
accelerationNone :: Acceleration
accelerationNone = Acceleration 0.0

-- | Light acceleration (2.0 m/s²)
accelerationLight :: Acceleration
accelerationLight = Acceleration 2.0

-- | Strong acceleration (10.0 m/s²)
accelerationStrong :: Acceleration
accelerationStrong = Acceleration 10.0

-- | Is agent decelerating? (acceleration < -0.5)
decelerating :: Acceleration -> Boolean
decelerating (Acceleration a) = a < -0.5

-- | Is agent accelerating? (acceleration > 0.5)
accelerating :: Acceleration -> Boolean
accelerating (Acceleration a) = a > 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // velocity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity magnitude (0+, finite) in m/s.
-- |
-- | Current speed of the agent. Direction is separate.
newtype Velocity = Velocity Number

derive instance eqVelocity :: Eq Velocity
derive instance ordVelocity :: Ord Velocity

instance showVelocity :: Show Velocity where
  show (Velocity n) = "Velocity(" <> show n <> "m/s)"

-- | Create a bounded velocity (clamps to 0+)
mkVelocity :: Number -> Velocity
mkVelocity n = Velocity (max 0.0 n)

-- | Unwrap the velocity value
unwrapVelocity :: Velocity -> Number
unwrapVelocity (Velocity n) = n

-- | Stationary (0.0 m/s)
velocityStationary :: Velocity
velocityStationary = Velocity 0.0

-- | Slow (1.0 m/s - walking pace)
velocitySlow :: Velocity
velocitySlow = Velocity 1.0

-- | Moderate (5.0 m/s - running)
velocityModerate :: Velocity
velocityModerate = Velocity 5.0

-- | Fast (20.0 m/s - vehicle)
velocityFast :: Velocity
velocityFast = Velocity 20.0

-- | Extreme (100.0 m/s)
velocityExtreme :: Velocity
velocityExtreme = Velocity 100.0

-- | Is agent stationary? (velocity < 0.1)
isStationary :: Velocity -> Boolean
isStationary (Velocity v) = v < 0.1

-- | Is agent moving? (velocity > 0.1)
isMoving :: Velocity -> Boolean
isMoving (Velocity v) = v > 0.1

-- | Is agent moving fast? (velocity > 10)
isMovingFast :: Velocity -> Boolean
isMovingFast (Velocity v) = v > 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // momentum
-- ═════════════════════════════════════════════════════════════════════════════

-- | Momentum vector (3D).
-- |
-- | The agent's current momentum (mass × velocity).
-- | Represents inertia and resistance to direction change.
type Momentum =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Create a momentum vector
mkMomentum :: Number -> Number -> Number -> Momentum
mkMomentum x y z = { x, y, z }

-- | Get X component
momentumX :: Momentum -> Number
momentumX m = m.x

-- | Get Y component
momentumY :: Momentum -> Number
momentumY m = m.y

-- | Get Z component
momentumZ :: Momentum -> Number
momentumZ m = m.z

-- | Get momentum magnitude
momentumMagnitude :: Momentum -> Number
momentumMagnitude m = Num.sqrt (m.x * m.x + m.y * m.y + m.z * m.z)

-- | No momentum (stationary)
momentumNone :: Momentum
momentumNone = { x: 0.0, y: 0.0, z: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to a range.
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
