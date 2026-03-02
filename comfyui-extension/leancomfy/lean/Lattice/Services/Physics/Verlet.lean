/-
  Lattice.Services.Physics.Verlet - Verlet Integration for Soft Bodies

  Pure mathematical functions for position-based dynamics using Verlet
  integration. Used for soft body and cloth simulation.

  Features:
  - Verlet integration (position-based)
  - Distance constraint solving
  - Constraint breaking (tearing)
  - Damping

  Verlet integration formula:
    x_new = x_curr + (x_curr - x_prev) * damping + a * dt²

  Source: ui/src/services/physics/PhysicsEngine.ts
-/

namespace Lattice.Services.Physics.Verlet

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Verlet particle state -/
structure ParticleState where
  posX : Float
  posY : Float
  prevX : Float
  prevY : Float
  accelX : Float
  accelY : Float
  invMass : Float  -- 0 for pinned particles
  deriving Repr, Inhabited

/-- Distance constraint between two particles -/
structure Constraint where
  restLength : Float
  stiffness : Float  -- 0-1, how rigidly constraint is enforced
  breakThreshold : Option Float  -- If set, constraint breaks when stretched beyond this ratio
  deriving Repr, Inhabited

/-- Result of constraint solving -/
structure ConstraintResult where
  particle1PosX : Float
  particle1PosY : Float
  particle2PosX : Float
  particle2PosY : Float
  broken : Bool
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Verlet Integration
--------------------------------------------------------------------------------

/-- Perform Verlet integration step for a single particle.

    Verlet formula: x_new = x + (x - x_prev) * damping + a * dt²

    @param state Current particle state
    @param damping Velocity damping factor (0-1, typically 0.98)
    @param dt Time step
    @return Updated particle state -/
def integrateParticle (state : ParticleState) (damping dt : Float) : ParticleState :=
  if state.invMass == 0.0 then
    -- Pinned particle - don't move
    state
  else
    let dtSq := dt * dt
    -- Current velocity (implicit in position difference)
    let velX := state.posX - state.prevX
    let velY := state.posY - state.prevY
    -- Apply damping to velocity
    let dampedVelX := velX * damping
    let dampedVelY := velY * damping
    -- New position
    let newPosX := state.posX + dampedVelX + state.accelX * dtSq
    let newPosY := state.posY + dampedVelY + state.accelY * dtSq

    { posX := newPosX
    , posY := newPosY
    , prevX := state.posX
    , prevY := state.posY
    , accelX := 0.0  -- Clear acceleration for next frame
    , accelY := 0.0
    , invMass := state.invMass }

/-- Extract velocity from particle state.

    Verlet velocity is implicit: v = (x_curr - x_prev) / dt

    @param state Particle state
    @return (velX, velY) -/
def getVelocity (state : ParticleState) : Float × Float :=
  (state.posX - state.prevX, state.posY - state.prevY)

/-- Set velocity by adjusting previous position.

    @param state Particle state
    @param velX X velocity
    @param velY Y velocity
    @return Updated state with new velocity -/
def setVelocity (state : ParticleState) (velX velY : Float) : ParticleState :=
  { state with
    prevX := state.posX - velX
    prevY := state.posY - velY }

--------------------------------------------------------------------------------
-- Distance Constraint Solving
--------------------------------------------------------------------------------

/-- Solve a distance constraint between two particles.

    Moves both particles to satisfy the rest length constraint.
    Mass-weighted: lighter particles move more.

    @param p1 First particle state
    @param p2 Second particle state
    @param constraint Constraint configuration
    @return (new p1 pos, new p2 pos, broken flag) -/
def solveConstraint (p1 p2 : ParticleState) (constraint : Constraint) : ConstraintResult :=
  let dx := p2.posX - p1.posX
  let dy := p2.posY - p1.posY
  let distance := Float.sqrt (dx * dx + dy * dy)

  -- Check for breaking
  match constraint.breakThreshold with
  | some threshold =>
      if distance > constraint.restLength * threshold then
        { particle1PosX := p1.posX
        , particle1PosY := p1.posY
        , particle2PosX := p2.posX
        , particle2PosY := p2.posY
        , broken := true }
      else
        solveConstraintInner p1 p2 constraint.restLength constraint.stiffness dx dy distance
  | none =>
      solveConstraintInner p1 p2 constraint.restLength constraint.stiffness dx dy distance

where
  solveConstraintInner (p1 p2 : ParticleState) (restLength stiffness dx dy distance : Float) : ConstraintResult :=
    if distance < 0.0001 then
      -- Particles at same position, can't solve
      { particle1PosX := p1.posX
      , particle1PosY := p1.posY
      , particle2PosX := p2.posX
      , particle2PosY := p2.posY
      , broken := false }
    else
      let totalInvMass := p1.invMass + p2.invMass
      if totalInvMass < 0.0001 then
        -- Both particles pinned
        { particle1PosX := p1.posX
        , particle1PosY := p1.posY
        , particle2PosX := p2.posX
        , particle2PosY := p2.posY
        , broken := false }
      else
        -- Calculate error and correction
        let error := (distance - restLength) / distance
        let correctionX := dx * error * stiffness * 0.5
        let correctionY := dy * error * stiffness * 0.5

        -- Mass-weighted distribution
        let ratio1 := p1.invMass / totalInvMass
        let ratio2 := p2.invMass / totalInvMass

        { particle1PosX := p1.posX + correctionX * ratio1
        , particle1PosY := p1.posY + correctionY * ratio1
        , particle2PosX := p2.posX - correctionX * ratio2
        , particle2PosY := p2.posY - correctionY * ratio2
        , broken := false }

--------------------------------------------------------------------------------
-- Cloth Grid Helpers
--------------------------------------------------------------------------------

/-- Calculate rest length for structural constraints (horizontal/vertical).

    @param spacing Grid spacing
    @return Rest length (equals spacing) -/
def structuralRestLength (spacing : Float) : Float := spacing

/-- Calculate rest length for shear constraints (diagonal).

    @param spacing Grid spacing
    @return Rest length (spacing * sqrt(2)) -/
def shearRestLength (spacing : Float) : Float :=
  spacing * Float.sqrt 2.0

/-- Calculate rest length for bend constraints (skip one).

    @param spacing Grid spacing
    @return Rest length (spacing * 2) -/
def bendRestLength (spacing : Float) : Float := spacing * 2.0

/-- Calculate grid index from row and column.

    @param row Row index (0-based)
    @param col Column index (0-based)
    @param width Grid width
    @return Linear index -/
def gridIndex (row col width : Nat) : Nat :=
  row * width + col

/-- Calculate row and column from grid index.

    @param index Linear index
    @param width Grid width
    @return (row, col) -/
def gridRowCol (index width : Nat) : Nat × Nat :=
  (index / width, index % width)

--------------------------------------------------------------------------------
-- Collision with Ground
--------------------------------------------------------------------------------

/-- Handle collision with a ground plane.

    @param posX Particle X position
    @param posY Particle Y position
    @param prevX Previous X position
    @param prevY Previous Y position
    @param groundY Y coordinate of ground
    @param restitution Bounciness (0-1)
    @param friction Ground friction (0-1)
    @return (new posX, new posY, new prevX, new prevY) -/
def collideWithGround (posX posY prevX prevY groundY restitution friction : Float) :
    Float × Float × Float × Float :=
  if posY >= groundY then
    -- No collision
    (posX, posY, prevX, prevY)
  else
    -- Reflect position
    let penetration := groundY - posY
    let newPosY := groundY + penetration * restitution
    -- Adjust previous position for velocity reflection
    let velY := posY - prevY
    let newPrevY := newPosY + velY * restitution
    -- Apply friction to horizontal velocity
    let velX := posX - prevX
    let newPrevX := posX - velX * (1.0 - friction)
    (posX, newPosY, newPrevX, newPrevY)

--------------------------------------------------------------------------------
-- Bounding Box Collision
--------------------------------------------------------------------------------

/-- Keep particle within a bounding box.

    @param posX Particle X position
    @param posY Particle Y position
    @param prevX Previous X position
    @param prevY Previous Y position
    @param minX Box minimum X
    @param minY Box minimum Y
    @param maxX Box maximum X
    @param maxY Box maximum Y
    @param restitution Bounciness
    @return (new posX, new posY, new prevX, new prevY) -/
def constrainToBounds (posX posY prevX prevY minX minY maxX maxY restitution : Float) :
    Float × Float × Float × Float :=
  let (newPosX, newPrevX) :=
    if posX < minX then
      let pen := minX - posX
      (minX + pen * restitution, posX + (posX - prevX) * restitution)
    else if posX > maxX then
      let pen := posX - maxX
      (maxX - pen * restitution, posX + (posX - prevX) * restitution)
    else
      (posX, prevX)

  let (newPosY, newPrevY) :=
    if posY < minY then
      let pen := minY - posY
      (minY + pen * restitution, posY + (posY - prevY) * restitution)
    else if posY > maxY then
      let pen := posY - maxY
      (maxY - pen * restitution, posY + (posY - prevY) * restitution)
    else
      (posY, prevY)

  (newPosX, newPosY, newPrevX, newPrevY)

end Lattice.Services.Physics.Verlet
