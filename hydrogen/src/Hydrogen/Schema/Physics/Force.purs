-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // physics // force
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Force — Physical force primitives for physics-based UI and animation.
-- |
-- | ## Design Philosophy
-- |
-- | Forces are the drivers of motion. In UI physics, forces create natural-feeling
-- | animations: springs pull elements to targets, drag slows motion, gravity
-- | creates weight. This module provides bounded, composable force primitives.
-- |
-- | ## Force Categories
-- |
-- | **Conservative Forces**: Path-independent, have potential energy
-- | - Gravitational: Constant downward pull
-- | - Spring/Elastic: Proportional to displacement (Hooke's law)
-- | - Electrostatic: Attraction/repulsion (UI element interactions)
-- |
-- | **Non-Conservative Forces**: Path-dependent, dissipate energy
-- | - Drag: Proportional to velocity (air resistance)
-- | - Friction: Opposes motion at contact
-- | - Damping: Viscous resistance (spring damping)
-- |
-- | ## Bounded Design
-- |
-- | Force magnitudes are bounded to prevent:
-- | - Infinite forces (division by zero in inverse-square laws)
-- | - Numerical instability in simulations
-- | - Unrealistic behavior at billion-agent scale
-- |
-- | ## Units
-- |
-- | Forces are dimensionless in UI space. The "mass" of a UI element is
-- | typically 1.0, so force equals acceleration. Physical units (Newtons)
-- | are not used; instead, forces are calibrated to produce pleasing motion.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Number (sqrt, abs)
-- |
-- | ## Dependents
-- |
-- | - Motion.Spring (spring physics)
-- | - Component.Draggable (drag physics)
-- | - Animation.Physics (physics-based animation)

module Hydrogen.Schema.Physics.Force
  ( -- * Force Vector
    Force2D(..)
  , force2D
  , forceZero
  , forceUp
  , forceDown
  , forceLeft
  , forceRight
  , forceX
  , forceY
  , forceMagnitude
  , forceDirection
  , forceNormalize
  , forceScale
  , forceNegate
  , forceAdd
  , forceSubtract
  , forceDot
  , forceClamp
  
  -- * Force Types
  , ForceType(..)
  , isConservative
  , isNonConservative
  
  -- * Gravitational Force
  , Gravity(..)
  , gravity
  , gravityEarth
  , gravityMoon
  , gravityLight
  , gravityHeavy
  , gravityZero
  , gravityForce
  , gravityMagnitude
  , gravityDirection
  
  -- * Spring Force (Hooke's Law)
  , SpringForce(..)
  , springForce
  , springForceDefault
  , springForceSoft
  , springForceStiff
  , springForceValue
  , springPotentialEnergy
  , springStiffness
  , springRestLength
  
  -- * Drag Force
  , DragForce(..)
  , dragForce
  , dragForceLight
  , dragForceMedium
  , dragForceHeavy
  , dragForceValue
  , dragCoefficient
  
  -- * Friction Force
  , FrictionForce(..)
  , frictionForce
  , frictionStatic
  , frictionKinetic
  , frictionIce
  , frictionRubber
  , frictionForceValue
  , staticCoefficient
  , kineticCoefficient
  
  -- * Damping Force
  , DampingForce(..)
  , dampingForce
  , dampingLight
  , dampingCritical
  , dampingHeavy
  , dampingForceValue
  , dampingCoefficient
  
  -- * Attractive/Repulsive Force
  , PointForce(..)
  , pointForce
  , attractiveForce
  , repulsiveForce
  , pointForceValue
  , pointForceStrength
  , pointForceFalloff
  
  -- * Combined Forces
  , ForceField(..)
  , emptyField
  , uniformField
  , addForceToField
  , fieldForceAt
  , fieldContains
  
  -- * Force Application
  , applyForce
  , netForce
  , accelerationFromForce
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , not
  , otherwise
  , (&&)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<<<)
  , (<=)
  , (<>)
  , (>)
  )

import Data.Array as Array
import Data.Array (foldl, snoc)
import Data.Number (sqrt, atan2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // force vector
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D force vector.
-- |
-- | Forces are vectors with magnitude and direction. Components are bounded
-- | to prevent numerical instability.
newtype Force2D = Force2D { x :: Number, y :: Number }

derive instance eqForce2D :: Eq Force2D
derive instance ordForce2D :: Ord Force2D

instance showForce2D :: Show Force2D where
  show (Force2D f) = "Force2D(" <> show f.x <> ", " <> show f.y <> ")"

-- | Create a 2D force vector with bounded components
force2D :: Number -> Number -> Force2D
force2D x y = Force2D 
  { x: clampForceComponent x
  , y: clampForceComponent y
  }

-- | Zero force (no acceleration)
forceZero :: Force2D
forceZero = Force2D { x: 0.0, y: 0.0 }

-- | Unit force pointing up (negative Y in screen coordinates)
forceUp :: Force2D
forceUp = Force2D { x: 0.0, y: -1.0 }

-- | Unit force pointing down (positive Y in screen coordinates)
forceDown :: Force2D
forceDown = Force2D { x: 0.0, y: 1.0 }

-- | Unit force pointing left
forceLeft :: Force2D
forceLeft = Force2D { x: -1.0, y: 0.0 }

-- | Unit force pointing right
forceRight :: Force2D
forceRight = Force2D { x: 1.0, y: 0.0 }

-- | Get X component
forceX :: Force2D -> Number
forceX (Force2D f) = f.x

-- | Get Y component
forceY :: Force2D -> Number
forceY (Force2D f) = f.y

-- | Calculate force magnitude
forceMagnitude :: Force2D -> Number
forceMagnitude (Force2D f) = sqrt (f.x * f.x + f.y * f.y)

-- | Calculate force direction as angle in radians from positive X axis
forceDirection :: Force2D -> Number
forceDirection (Force2D f) = atan2 f.y f.x

-- | Normalize force to unit length (magnitude 1)
forceNormalize :: Force2D -> Force2D
forceNormalize f =
  let mag = forceMagnitude f
  in if mag < 0.0001 
     then forceZero
     else forceScale (1.0 / mag) f

-- | Scale force by a factor
forceScale :: Number -> Force2D -> Force2D
forceScale s (Force2D f) = force2D (f.x * s) (f.y * s)

-- | Negate force (reverse direction)
forceNegate :: Force2D -> Force2D
forceNegate (Force2D f) = Force2D { x: negate f.x, y: negate f.y }

-- | Add two forces (vector addition)
forceAdd :: Force2D -> Force2D -> Force2D
forceAdd (Force2D a) (Force2D b) = force2D (a.x + b.x) (a.y + b.y)

-- | Subtract forces (a - b)
forceSubtract :: Force2D -> Force2D -> Force2D
forceSubtract (Force2D a) (Force2D b) = force2D (a.x - b.x) (a.y - b.y)

-- | Dot product of two forces
forceDot :: Force2D -> Force2D -> Number
forceDot (Force2D a) (Force2D b) = a.x * b.x + a.y * b.y

-- | Clamp force magnitude to maximum
forceClamp :: Number -> Force2D -> Force2D
forceClamp maxMag f =
  let mag = forceMagnitude f
  in if mag > maxMag && mag > 0.0001
     then forceScale (maxMag / mag) f
     else f

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // force types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classification of force types.
data ForceType
  = Conservative    -- ^ Path-independent, has potential energy
  | NonConservative -- ^ Path-dependent, dissipates energy

derive instance eqForceType :: Eq ForceType
derive instance ordForceType :: Ord ForceType

instance showForceType :: Show ForceType where
  show Conservative = "Conservative"
  show NonConservative = "NonConservative"

-- | Check if force is conservative
isConservative :: ForceType -> Boolean
isConservative Conservative = true
isConservative NonConservative = false

-- | Check if force is non-conservative
isNonConservative :: ForceType -> Boolean
isNonConservative = not <<< isConservative

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gravitational force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gravitational force configuration.
-- |
-- | Gravity is a constant force in a fixed direction.
-- | In UI space, "down" is typically positive Y.
newtype Gravity = Gravity 
  { magnitude :: Number  -- ^ Acceleration due to gravity (bounded 0-1000)
  , direction :: Force2D -- ^ Unit vector direction
  }

derive instance eqGravity :: Eq Gravity
derive instance ordGravity :: Ord Gravity

instance showGravity :: Show Gravity where
  show (Gravity g) = "Gravity(" <> show g.magnitude <> ")"

-- | Create gravity with magnitude and direction
gravity :: Number -> Force2D -> Gravity
gravity mag dir = Gravity 
  { magnitude: clampPositive 1000.0 mag
  , direction: forceNormalize dir
  }

-- | Earth-like gravity (strong, for heavy UI feel)
gravityEarth :: Gravity
gravityEarth = Gravity { magnitude: 9.8, direction: forceDown }

-- | Moon-like gravity (light, floaty feel)
gravityMoon :: Gravity
gravityMoon = Gravity { magnitude: 1.62, direction: forceDown }

-- | Light gravity for subtle effects
gravityLight :: Gravity
gravityLight = Gravity { magnitude: 2.0, direction: forceDown }

-- | Heavy gravity for weighty feel
gravityHeavy :: Gravity
gravityHeavy = Gravity { magnitude: 20.0, direction: forceDown }

-- | Zero gravity
gravityZero :: Gravity
gravityZero = Gravity { magnitude: 0.0, direction: forceDown }

-- | Calculate gravitational force on a mass
gravityForce :: Gravity -> Number -> Force2D
gravityForce (Gravity g) mass = 
  forceScale (g.magnitude * clampPositive 1000.0 mass) g.direction

-- | Get gravity magnitude
gravityMagnitude :: Gravity -> Number
gravityMagnitude (Gravity g) = g.magnitude

-- | Get gravity direction
gravityDirection :: Gravity -> Force2D
gravityDirection (Gravity g) = g.direction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // spring force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring force following Hooke's Law: F = -k * x
-- |
-- | Springs pull toward their rest position with force proportional to
-- | displacement. This creates oscillatory motion when combined with mass.
newtype SpringForce = SpringForce
  { stiffness :: Number   -- ^ Spring constant k (bounded 0-10000)
  , restLength :: Number  -- ^ Natural length of spring (bounded 0-10000)
  }

derive instance eqSpringForce :: Eq SpringForce
derive instance ordSpringForce :: Ord SpringForce

instance showSpringForce :: Show SpringForce where
  show (SpringForce s) = "SpringForce(k=" <> show s.stiffness <> ")"

-- | Create a spring force
springForce :: Number -> Number -> SpringForce
springForce k rest = SpringForce
  { stiffness: clampPositive 10000.0 k
  , restLength: clampPositive 10000.0 rest
  }

-- | Default spring (moderate stiffness)
springForceDefault :: SpringForce
springForceDefault = SpringForce { stiffness: 100.0, restLength: 0.0 }

-- | Soft spring (low stiffness, slow oscillation)
springForceSoft :: SpringForce
springForceSoft = SpringForce { stiffness: 30.0, restLength: 0.0 }

-- | Stiff spring (high stiffness, fast oscillation)
springForceStiff :: SpringForce
springForceStiff = SpringForce { stiffness: 300.0, restLength: 0.0 }

-- | Calculate spring force given current displacement from rest
-- |
-- | Displacement is a vector from rest position to current position.
-- | Force points back toward rest position.
springForceValue :: SpringForce -> Force2D -> Force2D
springForceValue (SpringForce s) displacement =
  let 
    dist = forceMagnitude displacement
    stretch = dist - s.restLength
  in if absNumber dist < 0.0001
     then forceZero
     else forceScale (negate s.stiffness * stretch / dist) displacement

-- | Calculate potential energy stored in spring
springPotentialEnergy :: SpringForce -> Number -> Number
springPotentialEnergy (SpringForce s) displacement =
  let stretch = displacement - s.restLength
  in 0.5 * s.stiffness * stretch * stretch

-- | Get spring stiffness
springStiffness :: SpringForce -> Number
springStiffness (SpringForce s) = s.stiffness

-- | Get spring rest length
springRestLength :: SpringForce -> Number
springRestLength (SpringForce s) = s.restLength

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // drag force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drag force proportional to velocity: F = -c * v
-- |
-- | Drag opposes motion, slowing objects down. Linear drag is proportional
-- | to velocity (viscous drag). Quadratic drag (proportional to v²) is
-- | used for high-speed aerodynamic drag but linear is simpler for UI.
newtype DragForce = DragForce
  { coefficient :: Number  -- ^ Drag coefficient (bounded 0-100)
  }

derive instance eqDragForce :: Eq DragForce
derive instance ordDragForce :: Ord DragForce

instance showDragForce :: Show DragForce where
  show (DragForce d) = "DragForce(c=" <> show d.coefficient <> ")"

-- | Create drag force with coefficient
dragForce :: Number -> DragForce
dragForce c = DragForce { coefficient: clampPositive 100.0 c }

-- | Light drag (minimal resistance)
dragForceLight :: DragForce
dragForceLight = DragForce { coefficient: 0.5 }

-- | Medium drag (balanced)
dragForceMedium :: DragForce
dragForceMedium = DragForce { coefficient: 2.0 }

-- | Heavy drag (strong resistance)
dragForceHeavy :: DragForce
dragForceHeavy = DragForce { coefficient: 8.0 }

-- | Calculate drag force given velocity
dragForceValue :: DragForce -> Force2D -> Force2D
dragForceValue (DragForce d) velocity =
  forceScale (negate d.coefficient) velocity

-- | Get drag coefficient
dragCoefficient :: DragForce -> Number
dragCoefficient (DragForce d) = d.coefficient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // friction force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Friction force opposing motion at contact.
-- |
-- | Friction has two regimes:
-- | - Static: Prevents motion until threshold exceeded
-- | - Kinetic: Constant force opposing motion
newtype FrictionForce = FrictionForce
  { staticCoeff :: Number   -- ^ Static friction coefficient (bounded 0-2)
  , kineticCoeff :: Number  -- ^ Kinetic friction coefficient (bounded 0-2)
  }

derive instance eqFrictionForce :: Eq FrictionForce
derive instance ordFrictionForce :: Ord FrictionForce

instance showFrictionForce :: Show FrictionForce where
  show (FrictionForce f) = 
    "FrictionForce(μs=" <> show f.staticCoeff <> ", μk=" <> show f.kineticCoeff <> ")"

-- | Create friction force
frictionForce :: Number -> Number -> FrictionForce
frictionForce static kinetic = FrictionForce
  { staticCoeff: clampUnit 2.0 static
  , kineticCoeff: clampUnit 2.0 kinetic
  }

-- | Static friction only (no sliding)
frictionStatic :: Number -> FrictionForce
frictionStatic coeff = FrictionForce
  { staticCoeff: clampUnit 2.0 coeff
  , kineticCoeff: clampUnit 2.0 (coeff * 0.8)
  }

-- | Kinetic friction (already sliding)
frictionKinetic :: Number -> FrictionForce
frictionKinetic coeff = FrictionForce
  { staticCoeff: clampUnit 2.0 (coeff * 1.2)
  , kineticCoeff: clampUnit 2.0 coeff
  }

-- | Ice-like friction (very slippery)
frictionIce :: FrictionForce
frictionIce = FrictionForce { staticCoeff: 0.1, kineticCoeff: 0.03 }

-- | Rubber-like friction (high grip)
frictionRubber :: FrictionForce
frictionRubber = FrictionForce { staticCoeff: 1.0, kineticCoeff: 0.8 }

-- | Calculate friction force given normal force and velocity
-- |
-- | Returns kinetic friction if moving, static friction threshold if stationary
frictionForceValue :: FrictionForce -> Number -> Force2D -> Force2D
frictionForceValue (FrictionForce f) normalMag velocity =
  let 
    speed = forceMagnitude velocity
    frictionMag = f.kineticCoeff * absNumber normalMag
  in if speed < 0.0001
     then forceZero  -- stationary, static friction handles externally
     else forceScale (negate frictionMag / speed) velocity

-- | Get static friction coefficient
staticCoefficient :: FrictionForce -> Number
staticCoefficient (FrictionForce f) = f.staticCoeff

-- | Get kinetic friction coefficient
kineticCoefficient :: FrictionForce -> Number
kineticCoefficient (FrictionForce f) = f.kineticCoeff

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // damping force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Damping force for oscillation control.
-- |
-- | Damping reduces oscillation amplitude over time. Critical damping
-- | returns to equilibrium fastest without overshooting.
newtype DampingForce = DampingForce
  { coefficient :: Number  -- ^ Damping coefficient (bounded 0-1000)
  }

derive instance eqDampingForce :: Eq DampingForce
derive instance ordDampingForce :: Ord DampingForce

instance showDampingForce :: Show DampingForce where
  show (DampingForce d) = "DampingForce(c=" <> show d.coefficient <> ")"

-- | Create damping force
dampingForce :: Number -> DampingForce
dampingForce c = DampingForce { coefficient: clampPositive 1000.0 c }

-- | Light damping (underdamped, bouncy)
dampingLight :: DampingForce
dampingLight = DampingForce { coefficient: 5.0 }

-- | Critical damping (no overshoot)
dampingCritical :: DampingForce
dampingCritical = DampingForce { coefficient: 20.0 }

-- | Heavy damping (overdamped, sluggish)
dampingHeavy :: DampingForce
dampingHeavy = DampingForce { coefficient: 50.0 }

-- | Calculate damping force given velocity
dampingForceValue :: DampingForce -> Force2D -> Force2D
dampingForceValue (DampingForce d) velocity =
  forceScale (negate d.coefficient) velocity

-- | Get damping coefficient
dampingCoefficient :: DampingForce -> Number
dampingCoefficient (DampingForce d) = d.coefficient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // attractive/repulsive
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point force: attraction or repulsion from a point.
-- |
-- | Used for:
-- | - Magnetic UI elements
-- | - Particle effects
-- | - Snap-to-point behavior
newtype PointForce = PointForce
  { strength :: Number   -- ^ Force strength (positive = attractive, negative = repulsive)
  , falloff :: Number    -- ^ Distance falloff exponent (1 = linear, 2 = inverse square)
  , minDistance :: Number -- ^ Minimum distance to prevent infinite force
  }

derive instance eqPointForce :: Eq PointForce
derive instance ordPointForce :: Ord PointForce

instance showPointForce :: Show PointForce where
  show (PointForce p) = "PointForce(str=" <> show p.strength <> ")"

-- | Create a point force
pointForce :: Number -> Number -> PointForce
pointForce strength falloff = PointForce
  { strength: clampForceComponent strength
  , falloff: clampPositive 4.0 falloff
  , minDistance: 1.0
  }

-- | Attractive force (pulls toward point)
attractiveForce :: Number -> PointForce
attractiveForce strength = PointForce
  { strength: absNumber (clampForceComponent strength)
  , falloff: 2.0
  , minDistance: 1.0
  }

-- | Repulsive force (pushes away from point)
repulsiveForce :: Number -> PointForce
repulsiveForce strength = PointForce
  { strength: negate (absNumber (clampForceComponent strength))
  , falloff: 2.0
  , minDistance: 1.0
  }

-- | Calculate point force given displacement from force center
pointForceValue :: PointForce -> Force2D -> Force2D
pointForceValue (PointForce p) displacement =
  let 
    dist = forceMagnitude displacement
    effectiveDist = if dist < p.minDistance then p.minDistance else dist
    falloffFactor = power effectiveDist p.falloff
    mag = p.strength / falloffFactor
  in if dist < 0.0001
     then forceZero
     else forceScale (mag / dist) displacement

-- | Get point force strength
pointForceStrength :: PointForce -> Number
pointForceStrength (PointForce p) = p.strength

-- | Get point force falloff
pointForceFalloff :: PointForce -> Number
pointForceFalloff (PointForce p) = p.falloff

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // force field
-- ═════════════════════════════════════════════════════════════════════════════

-- | A collection of forces that can be evaluated at any point.
data ForceField
  = EmptyField
  | UniformField Force2D
  | CompositeField (Array ForceField)

derive instance eqForceField :: Eq ForceField

instance showForceField :: Show ForceField where
  show EmptyField = "EmptyField"
  show (UniformField f) = "UniformField(" <> show f <> ")"
  show (CompositeField fields) = "CompositeField[" <> show (arrayLength fields) <> "]"

-- | Empty force field (no forces)
emptyField :: ForceField
emptyField = EmptyField

-- | Uniform force field (same force everywhere)
uniformField :: Force2D -> ForceField
uniformField = UniformField

-- | Add a force to a field
addForceToField :: ForceField -> ForceField -> ForceField
addForceToField EmptyField f = f
addForceToField f EmptyField = f
addForceToField (CompositeField fs) f = CompositeField (snoc fs f)
addForceToField f1 f2 = CompositeField [f1, f2]

-- | Evaluate force field at a position (for uniform fields, position is ignored)
fieldForceAt :: ForceField -> Force2D -> Force2D
fieldForceAt EmptyField _ = forceZero
fieldForceAt (UniformField f) _ = f
fieldForceAt (CompositeField fields) pos = 
  foldl (\acc field -> forceAdd acc (fieldForceAt field pos)) forceZero fields

-- | Check if field contains any forces
fieldContains :: ForceField -> Boolean
fieldContains EmptyField = false
fieldContains (UniformField _) = true
fieldContains (CompositeField fields) = arrayLength fields > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // force application
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a force to calculate acceleration (F = ma, so a = F/m)
applyForce :: Force2D -> Number -> Force2D
applyForce f mass =
  let m = if mass < 0.001 then 0.001 else mass
  in forceScale (1.0 / m) f

-- | Calculate net force from multiple forces
netForce :: Array Force2D -> Force2D
netForce forces = foldl forceAdd forceZero forces

-- | Calculate acceleration from force and mass
accelerationFromForce :: Force2D -> Number -> Force2D
accelerationFromForce = applyForce

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp force component to reasonable bounds
clampForceComponent :: Number -> Number
clampForceComponent n
  | n > 10000.0 = 10000.0
  | n < -10000.0 = -10000.0
  | otherwise = n

-- | Clamp positive value
clampPositive :: Number -> Number -> Number
clampPositive maxVal n
  | n < 0.0 = 0.0
  | n > maxVal = maxVal
  | otherwise = n

-- | Clamp to unit-ish range
clampUnit :: Number -> Number -> Number
clampUnit maxVal n
  | n < 0.0 = 0.0
  | n > maxVal = maxVal
  | otherwise = n

-- | Absolute value
absNumber :: Number -> Number
absNumber n = if n < 0.0 then negate n else n

-- | Power function (simple iterative for integer-ish exponents)
power :: Number -> Number -> Number
power base exp
  | exp <= 0.0 = 1.0
  | exp <= 1.0 = base
  | exp <= 2.0 = base * base
  | exp <= 3.0 = base * base * base
  | otherwise = base * base * base * base

-- | Array length (pure implementation)
arrayLength :: forall a. Array a -> Int
arrayLength = Array.length
