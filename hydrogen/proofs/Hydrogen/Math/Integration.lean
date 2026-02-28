/-
  Hydrogen.Math.Integration
  
  Numerical integration methods for particle physics simulation.
  
  PROVEN INVARIANTS:
    1. verlet_time_reversible: Verlet integration reverses trajectory when
       time-reversed (forward then backward returns to previous state)
    2. euler_semiImplicit_same_velocity: Both Euler methods produce identical
       velocity updates (differ only in position by a*dt²)
    3. verlet_position_formula: Equivalent to classic Störmer-Verlet:
       x(t+dt) = 2x(t) - x(t-dt) + a*dt²
    4. verlet_damping_one: Damping factor 1 = undamped Verlet
    5. Zero timestep is identity for Euler methods
  
  NOT YET PROVEN (future work):
    - Energy conservation bounds for conservative systems
    - Symplecticity of semi-implicit Euler (det Jacobian = 1)
    - Stability bounds for different dt values
  
  METHODS IMPLEMENTED:
    - Euler (explicit): x += v*dt, v += a*dt
    - Semi-implicit Euler: v += a*dt, x += v*dt (velocity first)
    - Verlet: x' = 2x - x_prev + a*dt² (position-based)
    - Velocity Verlet: x += v*dt + 0.5*a*dt², v += a*dt
  
  Status: FOUNDATIONAL - All theorems fully proven, no sorry, no custom axioms.
-/

import Hydrogen.Math.Vec2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math.Integration

open Vec2 in

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARTICLE STATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- State of a 2D particle for physics simulation -/
structure ParticleState where
  position : Vec2
  velocity : Vec2

/-- Extended state for Verlet integration (stores previous position) -/
structure VerletState where
  position : Vec2
  previousPosition : Vec2

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION THEOREMS
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ParticleState.ext {a b : ParticleState} 
    (hp : a.position = b.position) (hv : a.velocity = b.velocity) : a = b := by
  cases a; cases b; simp_all

@[ext]
theorem VerletState.ext {a b : VerletState} 
    (hp : a.position = b.position) (hpp : a.previousPosition = b.previousPosition) : a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXPLICIT EULER INTEGRATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Explicit Euler integration step
    
    x(t+dt) = x(t) + v(t) * dt
    v(t+dt) = v(t) + a(t) * dt
    
    Simple but can be unstable for oscillatory systems.
-/
def eulerStep (state : ParticleState) (acceleration : Vec2) (dt : ℝ) : ParticleState :=
  { position := Vec2.add state.position (Vec2.scale dt state.velocity)
    velocity := Vec2.add state.velocity (Vec2.scale dt acceleration) }

-- ═══════════════════════════════════════════════════════════════════════════════
-- SEMI-IMPLICIT EULER (SYMPLECTIC EULER)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Semi-implicit Euler integration step
    
    v(t+dt) = v(t) + a(t) * dt
    x(t+dt) = x(t) + v(t+dt) * dt
    
    Note: velocity is updated FIRST, then used for position update.
    This makes it symplectic (preserves phase space volume).
    Used by LATTICE for rigid body simulation.
-/
def semiImplicitEulerStep (state : ParticleState) (acceleration : Vec2) (dt : ℝ) : ParticleState :=
  let newVelocity := Vec2.add state.velocity (Vec2.scale dt acceleration)
  { position := Vec2.add state.position (Vec2.scale dt newVelocity)
    velocity := newVelocity }

-- ═══════════════════════════════════════════════════════════════════════════════
-- VERLET INTEGRATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Verlet integration step
    
    velocity = position - previousPosition  (implicit)
    newPosition = position + velocity + acceleration * dt²
    
    Equivalent to: x(t+dt) = 2*x(t) - x(t-dt) + a(t)*dt²
    
    Properties:
    - Time-reversible
    - Second-order accurate
    - Better energy conservation than Euler
    
    Used by LATTICE for soft body simulation (cloth, ropes, etc.)
-/
def verletStep (state : VerletState) (acceleration : Vec2) (dt : ℝ) : VerletState :=
  let velocity := Vec2.sub state.position state.previousPosition
  let dtSq := dt * dt
  { position := Vec2.add (Vec2.add state.position velocity) (Vec2.scale dtSq acceleration)
    previousPosition := state.position }

/-- Verlet step with damping factor
    
    velocity = (position - previousPosition) * damping
    newPosition = position + dampedVelocity + acceleration * dt²
    
    Damping in range [0, 1] where:
    - 1.0 = no damping (perfectly elastic)
    - 0.0 = full damping (no motion)
    - 0.98 = typical value for soft body simulation
-/
def verletStepDamped (state : VerletState) (acceleration : Vec2) (dt : ℝ) (damping : ℝ) : VerletState :=
  let velocity := Vec2.sub state.position state.previousPosition
  let dampedVelocity := Vec2.scale damping velocity
  let dtSq := dt * dt
  { position := Vec2.add (Vec2.add state.position dampedVelocity) (Vec2.scale dtSq acceleration)
    previousPosition := state.position }

-- ═══════════════════════════════════════════════════════════════════════════════
-- VELOCITY VERLET
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Velocity Verlet integration step
    
    x(t+dt) = x(t) + v(t)*dt + 0.5*a(t)*dt²
    v(t+dt) = v(t) + 0.5*(a(t) + a(t+dt))*dt
    
    This requires knowing acceleration at both t and t+dt.
    For simplicity, this version assumes constant acceleration.
-/
noncomputable def velocityVerletStep (state : ParticleState) (acceleration : Vec2) (dt : ℝ) : ParticleState :=
  let halfDtSq := (dt * dt) / 2
  { position := Vec2.add (Vec2.add state.position (Vec2.scale dt state.velocity)) (Vec2.scale halfDtSq acceleration)
    velocity := Vec2.add state.velocity (Vec2.scale dt acceleration) }

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONVERSION UTILITIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert ParticleState to VerletState
    
    previousPosition is computed by rewinding one timestep.
-/
def toVerletState (state : ParticleState) (dt : ℝ) : VerletState :=
  { position := state.position
    previousPosition := Vec2.sub state.position (Vec2.scale dt state.velocity) }

/-- Extract implicit velocity from Verlet state -/
def verletVelocity (state : VerletState) : Vec2 :=
  Vec2.sub state.position state.previousPosition

/-- Convert VerletState to ParticleState -/
def fromVerletState (state : VerletState) : ParticleState :=
  { position := state.position
    velocity := verletVelocity state }

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: BASIC PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Zero acceleration leaves velocity unchanged (Euler) -/
theorem euler_zero_accel (state : ParticleState) (dt : ℝ) :
    (eulerStep state Vec2.zero dt).velocity = state.velocity := by
  simp only [eulerStep, Vec2.zero, Vec2.scale, Vec2.add]
  ext <;> ring

/-- Zero acceleration leaves velocity unchanged (semi-implicit Euler) -/
theorem semiImplicit_zero_accel (state : ParticleState) (dt : ℝ) :
    (semiImplicitEulerStep state Vec2.zero dt).velocity = state.velocity := by
  simp only [semiImplicitEulerStep, Vec2.zero, Vec2.scale, Vec2.add]
  ext <;> ring

/-- Zero timestep leaves state unchanged (Euler) -/
theorem euler_zero_dt (state : ParticleState) (acceleration : Vec2) :
    eulerStep state acceleration 0 = state := by
  simp only [eulerStep, Vec2.scale, Vec2.add]
  ext <;> ring

/-- Zero timestep leaves state unchanged (semi-implicit Euler) -/
theorem semiImplicit_zero_dt (state : ParticleState) (acceleration : Vec2) :
    semiImplicitEulerStep state acceleration 0 = state := by
  simp only [semiImplicitEulerStep, Vec2.scale, Vec2.add]
  ext <;> ring

/-- Zero timestep behavior for Verlet (position still advances by implicit velocity) -/
theorem verlet_zero_dt (state : VerletState) (acceleration : Vec2) :
    verletStep state acceleration 0 = 
    { position := Vec2.add state.position (verletVelocity state)
      previousPosition := state.position } := by
  simp only [verletStep, verletVelocity, Vec2.add, Vec2.sub, Vec2.scale]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: VERLET TIME-REVERSIBILITY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- THE KEY THEOREM: Verlet integration is time-reversible
    
    If we step forward with dt, then step backward with -dt (and swap positions),
    the trajectory reverses: we move from the new position back to the old position.
    
    Specifically:
    - backward.position = state.previousPosition (we end up at the old previous)
    - backward.previousPosition = state.position (our new previous is the old position)
    
    This "rewinding" property is fundamental for energy conservation in physics simulations.
    Unlike Euler methods, Verlet doesn't accumulate energy drift over time.
-/
theorem verlet_time_reversible (state : VerletState) (acceleration : Vec2) (dt : ℝ) :
    let forward := verletStep state acceleration dt
    let reversed := { position := forward.previousPosition
                      previousPosition := forward.position : VerletState }
    let backward := verletStep reversed acceleration (-dt)
    backward.position = state.previousPosition ∧ backward.previousPosition = state.position := by
  simp only [verletStep, Vec2.add, Vec2.sub, Vec2.scale]
  constructor
  · ext <;> ring
  · trivial

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: EULER VS SEMI-IMPLICIT COMPARISON
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Explicit and semi-implicit Euler produce the same velocity -/
theorem euler_semiImplicit_same_velocity (state : ParticleState) (acceleration : Vec2) (dt : ℝ) :
    (eulerStep state acceleration dt).velocity = (semiImplicitEulerStep state acceleration dt).velocity := by
  simp only [eulerStep, semiImplicitEulerStep]

/-- Explicit and semi-implicit Euler differ in position by a*dt² 
    
    semi-implicit position = explicit position + a*dt²
    
    This is why semi-implicit is better for oscillatory systems:
    it slightly "looks ahead" in the velocity.
-/
theorem euler_semiImplicit_position_diff (state : ParticleState) (acceleration : Vec2) (dt : ℝ) :
    (semiImplicitEulerStep state acceleration dt).position = 
    Vec2.add (eulerStep state acceleration dt).position (Vec2.scale dt (Vec2.scale dt acceleration)) := by
  simp only [eulerStep, semiImplicitEulerStep, Vec2.add, Vec2.scale]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: VERLET EQUIVALENCE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Verlet position formula: x(t+dt) = 2*x(t) - x(t-dt) + a*dt²
    
    This is the classic Störmer-Verlet formulation.
-/
theorem verlet_position_formula (state : VerletState) (acceleration : Vec2) (dt : ℝ) :
    (verletStep state acceleration dt).position = 
    Vec2.add (Vec2.sub (Vec2.scale 2 state.position) state.previousPosition) (Vec2.scale (dt * dt) acceleration) := by
  simp only [verletStep, Vec2.add, Vec2.sub, Vec2.scale]
  ext <;> ring

/-- Verlet velocity is correctly preserved through conversion -/
theorem verlet_conversion_velocity (state : ParticleState) (dt : ℝ) :
    verletVelocity (toVerletState state dt) = Vec2.scale dt state.velocity := by
  simp only [verletVelocity, toVerletState, Vec2.sub, Vec2.scale]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: DAMPING PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Damping factor of 1 is equivalent to undamped Verlet -/
theorem verlet_damping_one (state : VerletState) (acceleration : Vec2) (dt : ℝ) :
    verletStepDamped state acceleration dt 1 = verletStep state acceleration dt := by
  simp only [verletStepDamped, verletStep, Vec2.add, Vec2.sub, Vec2.scale]
  ext <;> ring

/-- Damping factor of 0 eliminates velocity -/
theorem verlet_damping_zero (state : VerletState) (acceleration : Vec2) (dt : ℝ) :
    (verletStepDamped state acceleration dt 0).position = 
    Vec2.add state.position (Vec2.scale (dt * dt) acceleration) := by
  simp only [verletStepDamped, Vec2.add, Vec2.sub, Vec2.scale]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: VELOCITY VERLET PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Velocity Verlet produces same velocity as explicit Euler (for constant acceleration) -/
theorem velocityVerlet_same_velocity (state : ParticleState) (acceleration : Vec2) (dt : ℝ) :
    (velocityVerletStep state acceleration dt).velocity = (eulerStep state acceleration dt).velocity := by
  simp only [velocityVerletStep, eulerStep]

/-- Velocity Verlet position includes second-order correction -/
theorem velocityVerlet_position (state : ParticleState) (acceleration : Vec2) (dt : ℝ) :
    (velocityVerletStep state acceleration dt).position = 
    Vec2.add (Vec2.add state.position (Vec2.scale dt state.velocity)) (Vec2.scale (dt * dt / 2) acceleration) := by
  simp only [velocityVerletStep]

end Hydrogen.Math.Integration
