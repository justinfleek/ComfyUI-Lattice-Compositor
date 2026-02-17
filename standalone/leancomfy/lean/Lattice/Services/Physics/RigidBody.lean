/-
  Lattice.Services.Physics.RigidBody - Rigid Body Physics Calculations

  Pure mathematical functions for rigid body dynamics:
  - Moment of inertia for various shapes
  - Impulse-based collision response
  - Friction calculation (Coulomb's law)
  - Position correction
  - Semi-implicit Euler integration

  All functions are deterministic and side-effect free.

  Source: ui/src/services/physics/PhysicsEngine.ts
-/

namespace Lattice.Services.Physics.RigidBody

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Shape type for moment of inertia calculation -/
inductive ShapeType
  | circle
  | box
  | capsule
  deriving Repr, Inhabited, BEq

/-- Rigid body state -/
structure BodyState where
  posX : Float
  posY : Float
  velX : Float
  velY : Float
  angle : Float
  angularVelocity : Float
  inverseMass : Float
  inverseInertia : Float
  deriving Repr, Inhabited

/-- Collision result -/
structure CollisionResult where
  newVel1X : Float
  newVel1Y : Float
  newAngVel1 : Float
  newVel2X : Float
  newVel2Y : Float
  newAngVel2 : Float
  impulse : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Moment of Inertia
--------------------------------------------------------------------------------

/-- Calculate moment of inertia for a circle.

    Formula: I = (m * r²) / 2

    @param mass Mass of the body
    @param radius Radius of the circle
    @return Moment of inertia -/
def momentOfInertiaCircle (mass radius : Float) : Float :=
  (mass * radius * radius) / 2.0

/-- Calculate moment of inertia for a box (rectangle).

    Formula: I = (m * (w² + h²)) / 12

    This is the moment about the center of mass.

    @param mass Mass of the body
    @param width Box width
    @param height Box height
    @return Moment of inertia -/
def momentOfInertiaBox (mass width height : Float) : Float :=
  (mass * (width * width + height * height)) / 12.0

/-- Calculate moment of inertia for a capsule (stadium shape).

    Approximates as rectangle + two semicircles.

    @param mass Mass of the body
    @param radius Capsule end radius
    @param length Capsule length (between centers)
    @return Moment of inertia -/
def momentOfInertiaCapsule (mass radius length : Float) : Float :=
  let totalLength := length + Float.pi * radius
  let rectMass := (mass * length) / totalLength
  let circleMass := mass - rectMass
  let rectI := (rectMass * (length * length + 4.0 * radius * radius)) / 12.0
  let circleI := (circleMass * radius * radius) / 2.0
  rectI + circleI

/-- Calculate moment of inertia based on shape type.

    @param shapeType Type of shape
    @param mass Mass of the body
    @param param1 First parameter (radius for circle/capsule, width for box)
    @param param2 Second parameter (length for capsule, height for box, ignored for circle)
    @return Moment of inertia -/
def momentOfInertia (shapeType : ShapeType) (mass param1 param2 : Float) : Float :=
  match shapeType with
  | ShapeType.circle => momentOfInertiaCircle mass param1
  | ShapeType.box => momentOfInertiaBox mass param1 param2
  | ShapeType.capsule => momentOfInertiaCapsule mass param1 param2

--------------------------------------------------------------------------------
-- Semi-Implicit Euler Integration
--------------------------------------------------------------------------------

/-- Integrate velocity with acceleration and damping.

    Semi-implicit Euler: v_new = v + a * dt, then apply damping

    @param vel Current velocity
    @param accel Acceleration (force / mass)
    @param damping Linear damping coefficient
    @param dt Time step
    @return New velocity -/
def integrateVelocity (vel accel damping dt : Float) : Float :=
  let newVel := vel + accel * dt
  newVel * (1.0 - damping * dt)

/-- Integrate position with velocity.

    @param pos Current position
    @param vel Velocity
    @param dt Time step
    @return New position -/
def integratePosition (pos vel dt : Float) : Float :=
  pos + vel * dt

/-- Integrate a full body state.

    @param state Current body state
    @param forceX X component of applied force
    @param forceY Y component of applied force
    @param torque Applied torque
    @param linearDamping Linear velocity damping
    @param angularDamping Angular velocity damping
    @param dt Time step
    @return New body state -/
def integrateBody (state : BodyState) (forceX forceY torque linearDamping angularDamping dt : Float) : BodyState :=
  -- Integrate velocity (with force/mass = acceleration)
  let accelX := forceX * state.inverseMass
  let accelY := forceY * state.inverseMass
  let angAccel := torque * state.inverseInertia

  let newVelX := integrateVelocity state.velX accelX linearDamping dt
  let newVelY := integrateVelocity state.velY accelY linearDamping dt
  let newAngVel := integrateVelocity state.angularVelocity angAccel angularDamping dt

  -- Integrate position
  let newPosX := integratePosition state.posX newVelX dt
  let newPosY := integratePosition state.posY newVelY dt
  let newAngle := integratePosition state.angle newAngVel dt

  { posX := newPosX
  , posY := newPosY
  , velX := newVelX
  , velY := newVelY
  , angle := newAngle
  , angularVelocity := newAngVel
  , inverseMass := state.inverseMass
  , inverseInertia := state.inverseInertia }

--------------------------------------------------------------------------------
-- Collision Response
--------------------------------------------------------------------------------

/-- Calculate impulse magnitude for collision response.

    Uses the formula:
    j = -(1 + e) * v_rel · n / (1/m1 + 1/m2 + (r1 × n)²/I1 + (r2 × n)²/I2)

    @param normalVelocity Relative velocity along collision normal (negative = approaching)
    @param restitution Coefficient of restitution (bounciness, 0-1)
    @param invMassSum Sum of inverse masses
    @param angularTerm Sum of angular contribution terms
    @return Impulse magnitude -/
def calculateImpulseMagnitude (normalVelocity restitution invMassSum angularTerm : Float) : Float :=
  let denominator := invMassSum + angularTerm
  if denominator < 0.0001 then
    0.0
  else
    -(1.0 + restitution) * normalVelocity / denominator

/-- Calculate angular contribution to impulse denominator.

    Term: (r × n)² * invInertia

    @param rx X component of contact offset (contact - center)
    @param ry Y component of contact offset
    @param nx X component of collision normal
    @param ny Y component of collision normal
    @param inverseInertia Inverse moment of inertia
    @return Angular contribution -/
def angularImpulseTerm (rx ry nx ny inverseInertia : Float) : Float :=
  let rCrossN := rx * ny - ry * nx
  rCrossN * rCrossN * inverseInertia

/-- Calculate friction impulse using Coulomb's law.

    Friction impulse is clamped to: |jt| ≤ μ * |jn|

    @param tangentVelocity Relative velocity along tangent
    @param invMassSum Sum of inverse masses
    @param normalImpulse Normal impulse magnitude
    @param friction Friction coefficient (geometric mean of materials)
    @return Friction impulse magnitude -/
def calculateFrictionImpulse (tangentVelocity invMassSum normalImpulse friction : Float) : Float :=
  if invMassSum < 0.0001 then
    0.0
  else
    let jt := -tangentVelocity / invMassSum
    let maxFriction := normalImpulse * friction
    Float.max (-maxFriction) (Float.min maxFriction jt)

/-- Calculate position correction to resolve penetration.

    Uses Baumgarte stabilization with slop and bias.

    @param depth Penetration depth
    @param slop Allowed penetration before correction
    @param bias Correction strength (typically 0.1-0.3)
    @param invMassSum Sum of inverse masses
    @return Correction magnitude -/
def positionCorrection (depth slop bias invMassSum : Float) : Float :=
  if invMassSum < 0.0001 then
    0.0
  else
    let correctionDepth := Float.max 0.0 (depth - slop)
    correctionDepth * bias / invMassSum

--------------------------------------------------------------------------------
-- Combined Collision Resolution
--------------------------------------------------------------------------------

/-- Apply impulse to a body.

    @param velX Current X velocity
    @param velY Current Y velocity
    @param angVel Current angular velocity
    @param impulseX X component of impulse
    @param impulseY Y component of impulse
    @param rx Contact offset X
    @param ry Contact offset Y
    @param inverseMass Inverse mass
    @param inverseInertia Inverse moment of inertia
    @param sign Direction multiplier (+1 for body receiving impulse, -1 for body giving)
    @return (new velX, new velY, new angVel) -/
def applyImpulse (velX velY angVel impulseX impulseY rx ry inverseMass inverseInertia sign : Float) :
    Float × Float × Float :=
  let newVelX := velX + sign * impulseX * inverseMass
  let newVelY := velY + sign * impulseY * inverseMass
  let rCrossI := rx * impulseY - ry * impulseX
  let newAngVel := angVel + sign * rCrossI * inverseInertia
  (newVelX, newVelY, newAngVel)

end Lattice.Services.Physics.RigidBody
