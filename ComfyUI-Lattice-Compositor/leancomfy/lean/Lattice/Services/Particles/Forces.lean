/-
  Lattice.Services.Particles.Forces - Particle Force Field Calculations

  Pure mathematical functions for particle force fields:
  - Gravity wells with falloff (linear, quadratic, constant)
  - Vortex fields with tangential force and inward pull
  - Lorenz strange attractor (2D approximation)
  - Wind force from direction/strength
  - Friction damping

  All functions operate on normalized coordinates (0-1) and return
  velocity deltas to be applied to particles.

  Source: ui/src/services/particleSystem.ts
-/

namespace Lattice.Services.Particles.Forces

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Falloff function type for force fields -/
inductive FalloffType
  | constant   -- No falloff
  | linear     -- Linear falloff with distance
  | quadratic  -- Quadratic falloff (inverse square-ish)
  deriving Repr, Inhabited, BEq

/-- 2D velocity vector -/
structure Vec2 where
  x : Float
  y : Float
  deriving Repr, Inhabited

/-- Gravity well configuration -/
structure GravityWell where
  x : Float           -- Center X (normalized 0-1)
  y : Float           -- Center Y (normalized 0-1)
  strength : Float    -- Force strength
  radius : Float      -- Effect radius
  falloff : FalloffType
  deriving Repr, Inhabited

/-- Vortex configuration -/
structure Vortex where
  x : Float           -- Center X
  y : Float           -- Center Y
  strength : Float    -- Tangential force strength
  inwardPull : Float  -- Radial inward force
  radius : Float      -- Effect radius
  deriving Repr, Inhabited

/-- Lorenz attractor configuration -/
structure LorenzAttractor where
  x : Float           -- Center X
  y : Float           -- Center Y
  sigma : Float       -- Lorenz σ parameter (default 10)
  rho : Float         -- Lorenz ρ parameter (default 28)
  beta : Float        -- Lorenz β parameter (default 8/3)
  strength : Float    -- Overall force multiplier
  radius : Float      -- Effect radius
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Vector Operations
--------------------------------------------------------------------------------

/-- Calculate distance between two points -/
def distance (x1 y1 x2 y2 : Float) : Float :=
  let dx := x2 - x1
  let dy := y2 - y1
  Float.sqrt (dx * dx + dy * dy)

/-- Normalize a vector, returns zero vector if magnitude is too small -/
def normalize (dx dy : Float) : Vec2 :=
  let mag := Float.sqrt (dx * dx + dy * dy)
  if mag > 0.0001 then { x := dx / mag, y := dy / mag }
  else { x := 0.0, y := 0.0 }

/-- Add two vectors -/
def vecAdd (a b : Vec2) : Vec2 :=
  { x := a.x + b.x, y := a.y + b.y }

/-- Scale a vector -/
def vecScale (v : Vec2) (s : Float) : Vec2 :=
  { x := v.x * s, y := v.y * s }

--------------------------------------------------------------------------------
-- Falloff Functions
--------------------------------------------------------------------------------

/-- Apply falloff based on distance ratio (0 at center, 1 at edge) -/
def applyFalloff (distRatio : Float) (falloff : FalloffType) : Float :=
  match falloff with
  | .constant => 1.0
  | .linear => 1.0 - distRatio
  | .quadratic => (1.0 - distRatio) * (1.0 - distRatio)

--------------------------------------------------------------------------------
-- Gravity Well Force
--------------------------------------------------------------------------------

/-- Calculate force from a gravity well on a particle.

    Returns velocity delta (vx, vy) to add to particle.
    Force points toward well center, scaled by strength and falloff.

    @param px Particle X position
    @param py Particle Y position
    @param well Gravity well configuration
    @param deltaTime Time step
    @return Velocity delta to apply -/
def gravityWellForce (px py : Float) (well : GravityWell) (deltaTime : Float) : Vec2 :=
  let dx := well.x - px
  let dy := well.y - py
  let dist := Float.sqrt (dx * dx + dy * dy)

  -- Only apply force within radius and with safe distance
  if dist >= well.radius || dist <= 0.001 then
    { x := 0.0, y := 0.0 }
  else
    let distRatio := dist / well.radius
    let falloffFactor := applyFalloff distRatio well.falloff
    let force := well.strength * 0.0001 * falloffFactor

    -- Normalize direction and apply force
    let nx := dx / dist
    let ny := dy / dist
    { x := nx * force * deltaTime, y := ny * force * deltaTime }

--------------------------------------------------------------------------------
-- Vortex Force
--------------------------------------------------------------------------------

/-- Calculate force from a vortex field on a particle.

    Returns velocity delta with:
    - Tangential component (perpendicular to radius, creates spin)
    - Radial component (inward pull, creates spiral)

    @param px Particle X position
    @param py Particle Y position
    @param vortex Vortex configuration
    @param deltaTime Time step
    @return Velocity delta to apply -/
def vortexForce (px py : Float) (vortex : Vortex) (deltaTime : Float) : Vec2 :=
  let dx := vortex.x - px
  let dy := vortex.y - py
  let dist := Float.sqrt (dx * dx + dy * dy)

  if dist >= vortex.radius || dist <= 0.001 then
    { x := 0.0, y := 0.0 }
  else
    let influence := 1.0 - dist / vortex.radius
    let tangentialStrength := vortex.strength * 0.0001 * influence

    -- Normalize direction
    let nx := dx / dist
    let ny := dy / dist

    -- Perpendicular direction (tangent)
    let perpX := -ny
    let perpY := nx

    -- Tangential force
    let tangentForce := { x := perpX * tangentialStrength * deltaTime
                        , y := perpY * tangentialStrength * deltaTime }

    -- Inward pull force
    let inwardStrength := vortex.inwardPull * 0.0001 * influence
    let inwardForce := { x := nx * inwardStrength * deltaTime
                       , y := ny * inwardStrength * deltaTime }

    vecAdd tangentForce inwardForce

--------------------------------------------------------------------------------
-- Lorenz Attractor Force
--------------------------------------------------------------------------------

/-- Calculate force from a Lorenz strange attractor.

    Creates chaotic, butterfly-like motion. Uses 2D approximation where
    the Z coordinate is simulated from distance to center.

    Lorenz equations:
    dx/dt = σ(y - x)
    dy/dt = x(ρ - z) - y

    @param px Particle X position
    @param py Particle Y position
    @param attractor Lorenz attractor configuration
    @param deltaTime Time step
    @return Velocity delta to apply -/
def lorenzForce (px py : Float) (attractor : LorenzAttractor) (deltaTime : Float) : Vec2 :=
  let dx := px - attractor.x
  let dy := py - attractor.y
  let dist := Float.sqrt (dx * dx + dy * dy)

  if dist >= attractor.radius || dist <= 0.001 then
    { x := 0.0, y := 0.0 }
  else
    let influence := 1.0 - dist / attractor.radius

    -- Simulate Z coordinate from distance (creates 3D-like behavior)
    let pseudoZ := dist * 0.1

    -- Lorenz equations (adapted for 2D)
    let ldx := attractor.sigma * (dy - dx)
    let ldy := dx * (attractor.rho - pseudoZ) - dy

    -- Apply force scaled by strength and influence
    let strength := attractor.strength * 0.001 * influence
    { x := ldx * strength * deltaTime, y := ldy * strength * deltaTime }

--------------------------------------------------------------------------------
-- Wind Force
--------------------------------------------------------------------------------

/-- Calculate wind force from direction and strength.

    @param direction Wind direction in degrees (0 = right, 90 = down)
    @param strength Wind strength
    @param deltaTime Time step
    @return Velocity delta to apply -/
def windForce (direction strength deltaTime : Float) : Vec2 :=
  let radians := direction * Float.pi / 180.0
  let windX := Float.cos radians * strength * 0.001
  let windY := Float.sin radians * strength * 0.001
  { x := windX * deltaTime, y := windY * deltaTime }

--------------------------------------------------------------------------------
-- Gravity Force
--------------------------------------------------------------------------------

/-- Calculate global gravity force.

    @param gravity Gravity strength (positive = down)
    @param deltaTime Time step
    @return Velocity delta to apply -/
def gravityForce (gravity deltaTime : Float) : Vec2 :=
  { x := 0.0, y := gravity * 0.001 * deltaTime }

--------------------------------------------------------------------------------
-- Friction
--------------------------------------------------------------------------------

/-- Apply friction to velocity.

    Returns scaled velocity after friction.
    friction = 0 means no friction (full speed preserved)
    friction = 1 means complete stop

    @param vx Current X velocity
    @param vy Current Y velocity
    @param friction Friction coefficient (0-1)
    @return New velocity after friction -/
def applyFriction (vx vy friction : Float) : Vec2 :=
  let factor := 1.0 - Float.max 0.0 (Float.min 1.0 friction)
  { x := vx * factor, y := vy * factor }

--------------------------------------------------------------------------------
-- Combined Force Application
--------------------------------------------------------------------------------

/-- Apply multiple gravity wells to a particle.

    @param px Particle X position
    @param py Particle Y position
    @param wells Array of gravity wells
    @param deltaTime Time step
    @return Total velocity delta from all wells -/
def applyGravityWells (px py : Float) (wells : Array GravityWell) (deltaTime : Float) : Vec2 :=
  wells.foldl (init := { x := 0.0, y := 0.0 }) fun acc well =>
    vecAdd acc (gravityWellForce px py well deltaTime)

/-- Apply multiple vortices to a particle.

    @param px Particle X position
    @param py Particle Y position
    @param vortices Array of vortices
    @param deltaTime Time step
    @return Total velocity delta from all vortices -/
def applyVortices (px py : Float) (vortices : Array Vortex) (deltaTime : Float) : Vec2 :=
  vortices.foldl (init := { x := 0.0, y := 0.0 }) fun acc vortex =>
    vecAdd acc (vortexForce px py vortex deltaTime)

/-- Apply multiple Lorenz attractors to a particle.

    @param px Particle X position
    @param py Particle Y position
    @param attractors Array of Lorenz attractors
    @param deltaTime Time step
    @return Total velocity delta from all attractors -/
def applyLorenzAttractors (px py : Float) (attractors : Array LorenzAttractor) (deltaTime : Float) : Vec2 :=
  attractors.foldl (init := { x := 0.0, y := 0.0 }) fun acc attractor =>
    vecAdd acc (lorenzForce px py attractor deltaTime)

end Lattice.Services.Particles.Forces
