/-
  Lattice.Particles.Physics - Particle physics configurations

  Part of Particles module. Max 500 lines.

  Source: ui/src/types/particles.ts (collision, flocking, spring, SPH)
-/

import Lattice.Primitives
import Lattice.Particles.Enums

namespace Lattice.Particles.Physics

open Lattice.Primitives
open Lattice.Particles.Enums

/-! ## Vec3 for Particles -/

/-- 3D vector for particle physics -/
structure ParticleVec3 where
  x : Float
  y : Float
  z : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  z_finite : z.isFinite
  deriving Repr

/-! ## Collision Plane -/

/-- Individual collision plane (walls, floors at any angle) -/
structure CollisionPlaneConfig where
  id : NonEmptyString
  name : Option NonEmptyString
  enabled : Bool
  point : ParticleVec3               -- A point on the plane
  normal : ParticleVec3              -- Plane normal (outward direction)
  bounciness : Float                 -- 0-1
  friction : Float                   -- 0-1
  bounciness_ge_0 : bounciness ≥ 0
  bounciness_le_1 : bounciness ≤ 1
  bounciness_finite : bounciness.isFinite
  friction_ge_0 : friction ≥ 0
  friction_le_1 : friction ≤ 1
  friction_finite : friction.isFinite
  deriving Repr

/-! ## Collision Config -/

/-- Collision detection configuration -/
structure CollisionConfig where
  enabled : Bool
  -- Particle-particle collision
  particleCollision : Bool
  particleRadius : Float             -- Collision radius per particle
  bounciness : Float                 -- 0-1
  friction : Float                   -- 0-1
  -- Boundary collision
  boundaryEnabled : Bool
  boundaryBehavior : BoundaryBehavior
  boundaryPadding : Float            -- Pixels from edge
  -- Floor collision (CC Particle World style)
  floorEnabled : Bool
  floorY : Float                     -- Normalized Y position (0=top, 1=bottom)
  floorBehavior : FloorBehavior
  floorFriction : Float              -- 0-1
  -- Optional ceiling
  ceilingEnabled : Bool
  ceilingY : Float                   -- Normalized Y position
  -- Custom collision planes
  planes : Array CollisionPlaneConfig
  particleRadius_ge_0 : particleRadius ≥ 0
  particleRadius_finite : particleRadius.isFinite
  bounciness_ge_0 : bounciness ≥ 0
  bounciness_le_1 : bounciness ≤ 1
  bounciness_finite : bounciness.isFinite
  friction_ge_0 : friction ≥ 0
  friction_le_1 : friction ≤ 1
  friction_finite : friction.isFinite
  boundaryPadding_ge_0 : boundaryPadding ≥ 0
  boundaryPadding_finite : boundaryPadding.isFinite
  floorY_ge_0 : floorY ≥ 0
  floorY_le_1 : floorY ≤ 1
  floorY_finite : floorY.isFinite
  floorFriction_ge_0 : floorFriction ≥ 0
  floorFriction_le_1 : floorFriction ≤ 1
  floorFriction_finite : floorFriction.isFinite
  ceilingY_ge_0 : ceilingY ≥ 0
  ceilingY_le_1 : ceilingY ≤ 1
  ceilingY_finite : ceilingY.isFinite
  deriving Repr

/-! ## Flocking Config -/

/-- Flocking (boids) behavior configuration -/
structure FlockingConfig where
  enabled : Bool
  -- Separation - avoid crowding neighbors
  separationWeight : Float           -- 0-100
  separationRadius : Float           -- Pixels
  -- Alignment - steer towards average heading
  alignmentWeight : Float            -- 0-100
  alignmentRadius : Float            -- Pixels
  -- Cohesion - steer towards average position
  cohesionWeight : Float             -- 0-100
  cohesionRadius : Float             -- Pixels
  -- Limits
  maxSpeed : Float                   -- Maximum particle speed
  maxForce : Float                   -- Maximum steering force
  perceptionAngle : Float            -- Field of view in degrees
  separationWeight_ge_0 : separationWeight ≥ 0
  separationWeight_le_100 : separationWeight ≤ 100
  separationWeight_finite : separationWeight.isFinite
  separationRadius_ge_0 : separationRadius ≥ 0
  separationRadius_finite : separationRadius.isFinite
  alignmentWeight_ge_0 : alignmentWeight ≥ 0
  alignmentWeight_le_100 : alignmentWeight ≤ 100
  alignmentWeight_finite : alignmentWeight.isFinite
  alignmentRadius_ge_0 : alignmentRadius ≥ 0
  alignmentRadius_finite : alignmentRadius.isFinite
  cohesionWeight_ge_0 : cohesionWeight ≥ 0
  cohesionWeight_le_100 : cohesionWeight ≤ 100
  cohesionWeight_finite : cohesionWeight.isFinite
  cohesionRadius_ge_0 : cohesionRadius ≥ 0
  cohesionRadius_finite : cohesionRadius.isFinite
  maxSpeed_ge_0 : maxSpeed ≥ 0
  maxSpeed_finite : maxSpeed.isFinite
  maxForce_ge_0 : maxForce ≥ 0
  maxForce_finite : maxForce.isFinite
  perceptionAngle_ge_0 : perceptionAngle ≥ 0
  perceptionAngle_le_360 : perceptionAngle ≤ 360
  perceptionAngle_finite : perceptionAngle.isFinite
  deriving Repr

/-! ## Spring Structure -/

/-- Spring structure for cloth/rope/softbody -/
structure SpringStructure where
  id : NonEmptyString
  structureType : SpringStructureType
  -- Cloth-specific
  width : Option Nat                 -- Particles in X
  height : Option Nat                -- Particles in Y
  -- Rope-specific
  length : Option Nat                -- Number of particles
  -- Common
  startParticle : Nat
  pinnedParticles : Array Nat        -- Indices of fixed particles
  stiffness : Float
  damping : Float
  breakThreshold : Float             -- 0 = unbreakable
  stiffness_ge_0 : stiffness ≥ 0
  stiffness_finite : stiffness.isFinite
  damping_ge_0 : damping ≥ 0
  damping_finite : damping.isFinite
  breakThreshold_ge_0 : breakThreshold ≥ 0
  breakThreshold_finite : breakThreshold.isFinite
  deriving Repr

/-! ## Spring System Config -/

/-- Spring system configuration (cloth, soft body, ropes) -/
structure SpringSystemConfig where
  enabled : Bool
  useVerlet : Bool                   -- Verlet integration (more stable)
  solverIterations : Nat             -- 1-16
  globalStiffness : Float            -- 0.001-10000
  globalDamping : Float              -- 0-1000
  enableBreaking : Bool              -- Allow springs to break under tension
  gravity : ParticleVec3
  structures : Array SpringStructure
  solverIterations_positive : solverIterations > 0
  solverIterations_le_16 : solverIterations ≤ 16
  globalStiffness_ge_0 : globalStiffness ≥ 0
  globalStiffness_finite : globalStiffness.isFinite
  globalDamping_ge_0 : globalDamping ≥ 0
  globalDamping_finite : globalDamping.isFinite
  deriving Repr

/-! ## SPH Fluid Config -/

/-- SPH fluid simulation configuration -/
structure SPHFluidConfig where
  enabled : Bool
  preset : SPHPreset
  smoothingRadius : Float            -- h, affects neighbor search
  restDensity : Float                -- ρ₀, fluid rest density
  gasConstant : Float                -- k, pressure stiffness
  viscosity : Float                  -- μ, how "thick" the fluid is
  surfaceTension : Float             -- σ, surface cohesion
  gravity : ParticleVec3
  boundaryDamping : Float            -- Energy loss at boundaries
  smoothingRadius_positive : smoothingRadius > 0
  smoothingRadius_finite : smoothingRadius.isFinite
  restDensity_positive : restDensity > 0
  restDensity_finite : restDensity.isFinite
  gasConstant_positive : gasConstant > 0
  gasConstant_finite : gasConstant.isFinite
  viscosity_ge_0 : viscosity ≥ 0
  viscosity_finite : viscosity.isFinite
  surfaceTension_ge_0 : surfaceTension ≥ 0
  surfaceTension_finite : surfaceTension.isFinite
  boundaryDamping_ge_0 : boundaryDamping ≥ 0
  boundaryDamping_le_1 : boundaryDamping ≤ 1
  boundaryDamping_finite : boundaryDamping.isFinite
  deriving Repr

/-! ## Turbulence Field -/

/-- Turbulence field configuration -/
structure TurbulenceFieldConfig where
  id : NonEmptyString
  enabled : Bool
  scale : Float                      -- Noise frequency, 0.001-0.01
  strength : Float                   -- Force magnitude, 0-500
  evolutionSpeed : Float             -- How fast noise changes, 0-1
  octaves : Nat                      -- Number of noise octaves
  persistence : Float                -- Amplitude multiplier per octave
  animationSpeed : Float             -- Speed of noise evolution
  scale_positive : scale > 0
  scale_finite : scale.isFinite
  strength_ge_0 : strength ≥ 0
  strength_finite : strength.isFinite
  evolutionSpeed_ge_0 : evolutionSpeed ≥ 0
  evolutionSpeed_le_1 : evolutionSpeed ≤ 1
  evolutionSpeed_finite : evolutionSpeed.isFinite
  octaves_positive : octaves > 0
  persistence_ge_0 : persistence ≥ 0
  persistence_le_1 : persistence ≤ 1
  persistence_finite : persistence.isFinite
  animationSpeed_ge_0 : animationSpeed ≥ 0
  animationSpeed_finite : animationSpeed.isFinite
  deriving Repr

/-! ## Gravity Well -/

/-- Gravity well configuration -/
structure GravityWellConfig where
  id : NonEmptyString
  name : NonEmptyString
  x : Float
  y : Float
  strength : Float
  radius : Float
  falloff : ParticleFalloff
  enabled : Bool
  x_finite : x.isFinite
  y_finite : y.isFinite
  strength_finite : strength.isFinite
  radius_positive : radius > 0
  radius_finite : radius.isFinite
  deriving Repr

/-! ## Vortex -/

/-- Vortex configuration -/
structure VortexConfig where
  id : NonEmptyString
  name : NonEmptyString
  x : Float
  y : Float
  strength : Float
  radius : Float
  rotationSpeed : Float
  inwardPull : Float
  enabled : Bool
  x_finite : x.isFinite
  y_finite : y.isFinite
  strength_finite : strength.isFinite
  radius_positive : radius > 0
  radius_finite : radius.isFinite
  rotationSpeed_finite : rotationSpeed.isFinite
  inwardPull_finite : inwardPull.isFinite
  deriving Repr

/-! ## LOD Config -/

/-- Level of Detail configuration -/
structure ParticleLODConfig where
  enabled : Bool
  distances : Array Float            -- [near, mid, far]
  sizeMultipliers : Array Float      -- [near, mid, far]
  deriving Repr

/-! ## DOF Config -/

/-- Depth of Field configuration for particles -/
structure ParticleDOFConfig where
  enabled : Bool
  focusDistance : Float
  focusRange : Float
  blurAmount : Float
  focusDistance_ge_0 : focusDistance ≥ 0
  focusDistance_finite : focusDistance.isFinite
  focusRange_ge_0 : focusRange ≥ 0
  focusRange_finite : focusRange.isFinite
  blurAmount_ge_0 : blurAmount ≥ 0
  blurAmount_le_1 : blurAmount ≤ 1
  blurAmount_finite : blurAmount.isFinite
  deriving Repr

/-! ## Group Config -/

/-- Particle group configuration -/
structure ParticleGroupConfig where
  id : NonEmptyString
  name : NonEmptyString
  enabled : Bool
  color : RGBA                       -- RGBA tint
  collisionMask : Nat                -- Bitmask for which groups this collides with
  connectionMask : Nat               -- Bitmask for which groups this connects to
  deriving Repr

end Lattice.Particles.Physics
