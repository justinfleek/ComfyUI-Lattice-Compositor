/-
  Lattice.Physics.Forces - Force field types

  Part of Physics module. Max 500 lines.

  Source: ui/src/types/physics.ts (lines 352-477)
-/

import Lattice.Primitives
import Lattice.Physics.Enums
import Lattice.Physics.Core

namespace Lattice.Physics.Forces

open Lattice.Primitives
open Lattice.Physics.Enums
open Lattice.Physics.Core

/-! ## Force Field Base -/

/-- Base force field configuration -/
structure ForceFieldBase where
  id : NonEmptyString
  forceType : ForceType
  enabled : Bool
  affectedBodies : Option (Array NonEmptyString)  -- Empty = all
  startFrame : FrameNumber
  endFrame : FrameNumber  -- Negative = forever
  deriving Repr

/-! ## Gravity Force -/

/-- Gravity force - constant directional -/
structure GravityForce extends ForceFieldBase where
  gravityPropertyId : NonEmptyString  -- AnimatableProperty ID for gravity vector
  deriving Repr

/-! ## Wind Force -/

/-- Wind force - directional with turbulence -/
structure WindForce extends ForceFieldBase where
  directionPropertyId : NonEmptyString    -- AnimatableProperty ID for direction
  turbulencePropertyId : NonEmptyString   -- AnimatableProperty ID for turbulence strength
  frequency : Float                       -- Turbulence frequency
  seed : Nat                              -- Noise seed for determinism
  frequency_positive : frequency > 0
  frequency_finite : frequency.isFinite
  deriving Repr

/-! ## Attraction Force -/

/-- Attraction force - point attractor/repeller -/
structure AttractionForce extends ForceFieldBase where
  positionPropertyId : NonEmptyString     -- AnimatableProperty ID for position
  strengthPropertyId : NonEmptyString     -- AnimatableProperty ID for strength (negative = repel)
  radius : Float                          -- Falloff radius (0 = infinite range)
  falloff : ForceFalloff
  radius_ge_0 : radius ≥ 0
  radius_finite : radius.isFinite
  deriving Repr

/-! ## Explosion Force -/

/-- Explosion force - radial impulse -/
structure ExplosionForce extends ForceFieldBase where
  position : PhysicsVec2   -- Explosion center
  strength : Float         -- Impulse strength
  radius : Float           -- Effect radius
  triggerFrame : FrameNumber
  duration : FrameNumber   -- Duration in frames (1 = instant)
  strength_finite : strength.isFinite
  radius_positive : radius > 0
  radius_finite : radius.isFinite
  deriving Repr

/-! ## Buoyancy Force -/

/-- Buoyancy force - fluid simulation -/
structure BuoyancyForce extends ForceFieldBase where
  surfaceLevelPropertyId : NonEmptyString  -- AnimatableProperty ID for surface Y
  density : Float           -- Fluid density
  linearDrag : Float        -- Linear drag in fluid
  angularDrag : Float       -- Angular drag in fluid
  density_positive : density > 0
  density_finite : density.isFinite
  linearDrag_ge_0 : linearDrag ≥ 0
  linearDrag_finite : linearDrag.isFinite
  angularDrag_ge_0 : angularDrag ≥ 0
  angularDrag_finite : angularDrag.isFinite
  deriving Repr

/-! ## Vortex Force -/

/-- Vortex force - rotational -/
structure VortexForce extends ForceFieldBase where
  positionPropertyId : NonEmptyString   -- AnimatableProperty ID for center position
  strengthPropertyId : NonEmptyString   -- AnimatableProperty ID for tangential strength
  inwardForce : Float                   -- Inward pull strength
  radius : Float                        -- Effect radius
  inwardForce_finite : inwardForce.isFinite
  radius_positive : radius > 0
  radius_finite : radius.isFinite
  deriving Repr

/-! ## Drag Force -/

/-- Drag force - air/fluid resistance -/
structure DragForce extends ForceFieldBase where
  linear : Float      -- Linear drag coefficient
  quadratic : Float   -- Quadratic drag coefficient
  linear_ge_0 : linear ≥ 0
  linear_finite : linear.isFinite
  quadratic_ge_0 : quadratic ≥ 0
  quadratic_finite : quadratic.isFinite
  deriving Repr

/-! ## Force Field Sum Type -/

/-- All force field types -/
inductive ForceField where
  | gravity : GravityForce → ForceField
  | wind : WindForce → ForceField
  | attraction : AttractionForce → ForceField
  | explosion : ExplosionForce → ForceField
  | buoyancy : BuoyancyForce → ForceField
  | vortex : VortexForce → ForceField
  | drag : DragForce → ForceField
  deriving Repr

/-! ## Force Field Helpers -/

/-- Get force field ID -/
def ForceField.id : ForceField → NonEmptyString
  | gravity f => f.id
  | wind f => f.id
  | attraction f => f.id
  | explosion f => f.id
  | buoyancy f => f.id
  | vortex f => f.id
  | drag f => f.id

/-- Get force field type -/
def ForceField.forceType : ForceField → ForceType
  | gravity _ => ForceType.gravity
  | wind _ => ForceType.wind
  | attraction _ => ForceType.attraction
  | explosion _ => ForceType.explosion
  | buoyancy _ => ForceType.buoyancy
  | vortex _ => ForceType.vortex
  | drag _ => ForceType.drag

/-- Check if force field is enabled -/
def ForceField.isEnabled : ForceField → Bool
  | gravity f => f.enabled
  | wind f => f.enabled
  | attraction f => f.enabled
  | explosion f => f.enabled
  | buoyancy f => f.enabled
  | vortex f => f.enabled
  | drag f => f.enabled

end Lattice.Physics.Forces
