/-
  Lattice.Services.Flow.Patterns - Flow Field Pattern Math

  Pure mathematical functions for Anadol-style generative flow patterns.
  These compute positions based on flow field equations without
  managing trajectories or state.

  Source: ui/src/services/export/wanMoveFlowGenerators.ts
-/

import Lattice.Services.Noise.SimplexNoise

namespace Lattice.Services.Flow.Patterns

open Lattice.Services.Noise.SimplexNoise

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 2D point for flow calculations -/
structure Point2D where
  x : Float
  y : Float
  deriving Repr, Inhabited, BEq

/-- Flow field parameters common to most patterns -/
structure FlowParams where
  width : Float
  height : Float
  seed : UInt32 := 42
  noiseStrength : Float := 0.1
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Point Operations
--------------------------------------------------------------------------------

def Point2D.origin : Point2D := ⟨0.0, 0.0⟩

def Point2D.add (a b : Point2D) : Point2D :=
  ⟨a.x + b.x, a.y + b.y⟩

def Point2D.scale (p : Point2D) (s : Float) : Point2D :=
  ⟨p.x * s, p.y * s⟩

def Point2D.distance (a b : Point2D) : Float :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  Float.sqrt (dx * dx + dy * dy)

def Point2D.clamp (p : Point2D) (minX minY maxX maxY : Float) : Point2D :=
  ⟨Float.max minX (Float.min maxX p.x), Float.max minY (Float.min maxY p.y)⟩

--------------------------------------------------------------------------------
-- Spiral Flow
--------------------------------------------------------------------------------

/-- Parameters for spiral galaxy flow -/
structure SpiralParams extends FlowParams where
  turns : Float := 3.0         -- Number of spiral rotations
  expansion : Float := 1.5     -- How much spiral expands over time
  deriving Repr, Inhabited

/-- Calculate spiral position at time t.

    t: normalized time [0, 1]
    armOffset: starting angle offset (radians)
    radiusOffset: starting radius offset [0, 1]
    phaseOffset: animation phase offset
    center: spiral center point
    maxRadius: maximum spiral radius

    Returns position on spiral at time t. -/
def spiralPosition (params : SpiralParams) (t : Float)
    (armOffset radiusOffset phaseOffset : Float)
    (center : Point2D) (maxRadius : Float)
    (pointIndex frameIndex : Nat) : Point2D :=
  let effectiveT := t + phaseOffset
  let angle := armOffset + effectiveT * Float.pi * 2.0 * params.turns
  let radius := (radiusOffset + effectiveT * params.expansion) * maxRadius

  -- Add noise for organic feel
  let noise := simplexNoise2D (pointIndex.toFloat * 0.1) (frameIndex.toFloat * 0.05) params.seed
  let noisedRadius := radius * (1.0 + (noise - 0.5) * params.noiseStrength * 2.0)

  let x := center.x + Float.cos angle * noisedRadius
  let y := center.y + Float.sin angle * noisedRadius

  Point2D.clamp ⟨x, y⟩ 0.0 0.0 params.width params.height

--------------------------------------------------------------------------------
-- Wave Flow
--------------------------------------------------------------------------------

/-- Parameters for wave/ocean flow -/
structure WaveParams extends FlowParams where
  amplitude : Float := 0.0     -- Will default to height * 0.15 if 0
  frequency : Float := 3.0     -- Wave oscillations across width
  speed : Float := 0.1         -- Horizontal movement speed
  layers : Nat := 5            -- Number of wave layers
  deriving Repr, Inhabited

/-- Calculate wave position at time t.

    t: normalized time [0, 1]
    startX: initial x position
    layerY: base y position for this layer
    phaseOffset: wave phase offset
    amplitudeVar: amplitude variation factor [0.5, 1.0]

    Returns position on wave at time t. -/
def wavePosition (params : WaveParams) (t : Float)
    (startX layerY phaseOffset amplitudeVar : Float)
    (layer pointIndex frameIndex : Nat) : Point2D × Bool :=
  let amplitude := if params.amplitude == 0.0
                   then params.height * 0.15
                   else params.amplitude

  -- Move across screen with wrapping
  let rawX := startX + t * params.width * params.speed * 10.0
  let x := (rawX % (params.width * 1.2)) - params.width * 0.1

  -- Wave motion
  let waveAngle := (x / params.width) * Float.pi * 2.0 * params.frequency +
                   phaseOffset + t * Float.pi * 4.0
  let wave := Float.sin waveAngle
  let y := layerY + wave * amplitude * amplitudeVar

  -- Add turbulent noise
  let noise := simplexNoise2D (x * 0.01) (frameIndex.toFloat * 0.05 + layer.toFloat) params.seed
  let noisedY := y + (noise - 0.5) * amplitude * params.noiseStrength * 4.0

  let pos := Point2D.clamp ⟨x, noisedY⟩ 0.0 0.0 params.width params.height
  let visible := x >= 0.0 && x <= params.width
  (pos, visible)

--------------------------------------------------------------------------------
-- Explosion Flow
--------------------------------------------------------------------------------

/-- Parameters for explosion/big bang flow -/
structure ExplosionParams extends FlowParams where
  speed : Float := 1.0         -- Explosion velocity multiplier
  decay : Float := 0.95        -- Velocity decay per frame [0, 1]
  center : Point2D := Point2D.origin  -- Will use center of canvas if origin
  deriving Repr, Inhabited

/-- Explosion particle state -/
structure ExplosionState where
  x : Float
  y : Float
  vx : Float
  vy : Float
  deriving Repr, Inhabited

/-- Initialize explosion particle.

    angle: explosion direction (radians)
    speed: initial speed multiplier
    center: explosion center -/
def initExplosionParticle (params : ExplosionParams) (angle speed : Float) : ExplosionState :=
  let center := if params.center.x == 0.0 && params.center.y == 0.0
                then ⟨params.width / 2.0, params.height / 2.0⟩
                else params.center
  { x := center.x
  , y := center.y
  , vx := Float.cos angle * speed * 20.0
  , vy := Float.sin angle * speed * 20.0 }

/-- Step explosion particle forward one frame.

    Returns (newState, position, visible) -/
def stepExplosionParticle (params : ExplosionParams) (state : ExplosionState)
    (pointIndex frameIndex : Nat) : ExplosionState × Point2D × Bool :=
  -- Add noise for turbulence
  let noiseX := (simplexNoise2D (pointIndex.toFloat * 0.1) (frameIndex.toFloat * 0.1) params.seed - 0.5) *
                params.noiseStrength * 50.0
  let noiseY := (simplexNoise2D (pointIndex.toFloat * 0.1 + 100.0) (frameIndex.toFloat * 0.1) params.seed - 0.5) *
                params.noiseStrength * 50.0

  let newX := state.x + state.vx + noiseX
  let newY := state.y + state.vy + noiseY
  let newVx := state.vx * params.decay
  let newVy := state.vy * params.decay

  let newState := { x := newX, y := newY, vx := newVx, vy := newVy }
  let pos := Point2D.clamp ⟨newX, newY⟩ 0.0 0.0 params.width params.height
  let visible := newX >= 0.0 && newX <= params.width && newY >= 0.0 && newY <= params.height

  (newState, pos, visible)

--------------------------------------------------------------------------------
-- Vortex Flow
--------------------------------------------------------------------------------

/-- Parameters for vortex/whirlpool flow -/
structure VortexParams extends FlowParams where
  strength : Float := 0.5      -- Angular velocity multiplier
  maxRadius : Float := 0.0     -- Will default to min(width,height)*0.4 if 0
  center : Point2D := Point2D.origin
  deriving Repr, Inhabited

/-- Vortex particle state -/
structure VortexState where
  angle : Float
  radius : Float
  deriving Repr, Inhabited

/-- Initialize vortex particle.

    startAngle: initial angle (radians)
    startRadius: initial radius -/
def initVortexParticle (startAngle startRadius : Float) : VortexState :=
  { angle := startAngle, radius := startRadius }

/-- Step vortex particle forward one frame.

    Returns (newState, position) -/
def stepVortexParticle (params : VortexParams) (state : VortexState) : VortexState × Point2D :=
  let maxRadius := if params.maxRadius == 0.0
                   then Float.min params.width params.height * 0.4
                   else params.maxRadius
  let center := if params.center.x == 0.0 && params.center.y == 0.0
                then ⟨params.width / 2.0, params.height / 2.0⟩
                else params.center

  -- Spiral inward while rotating faster near center
  let angularSpeed := params.strength * (1.0 + (maxRadius - state.radius) / maxRadius * 2.0)
  let newAngle := state.angle + angularSpeed
  let newRadius := Float.max 10.0 (state.radius - state.radius * 0.01 * params.strength)

  -- Add noise
  let noise := simplexNoise2D state.angle (state.radius * 0.01) params.seed
  let noisedRadius := newRadius * (1.0 + (noise - 0.5) * params.noiseStrength)

  let x := center.x + Float.cos newAngle * noisedRadius
  let y := center.y + Float.sin newAngle * noisedRadius

  let newState := { angle := newAngle, radius := newRadius }
  let pos := Point2D.clamp ⟨x, y⟩ 0.0 0.0 params.width params.height

  (newState, pos)

--------------------------------------------------------------------------------
-- Data River Flow
--------------------------------------------------------------------------------

/-- Parameters for data river flow -/
structure RiverParams extends FlowParams where
  riverWidth : Float := 0.0    -- Will default to height * 0.3 if 0
  curve : Float := 0.5         -- S-curve intensity
  turbulence : Float := 0.1    -- Lane turbulence
  deriving Repr, Inhabited

/-- Calculate river centerline y-position at x.

    S-curve path from left to right. -/
def riverPath (params : RiverParams) (x : Float) : Float :=
  let t := x / params.width
  params.height / 2.0 + Float.sin (t * Float.pi * 2.0 * params.curve) * params.height * 0.25

/-- Calculate river position at time t.

    t: normalized time [0, 1]
    startX: initial x position
    laneOffset: perpendicular offset from centerline
    speed: movement speed multiplier

    Returns (position, visible) -/
def riverPosition (params : RiverParams) (t : Float)
    (startX laneOffset speed : Float)
    (pointIndex frameIndex : Nat) : Point2D × Bool :=
  let riverWidth := if params.riverWidth == 0.0
                    then params.height * 0.3
                    else params.riverWidth

  -- Flow along river
  let x := startX + t * params.width * speed * 1.3
  let baseY := riverPath params x

  -- Lane position + turbulence
  let noise := simplexNoise2D (x * 0.01) (frameIndex.toFloat * 0.05 + pointIndex.toFloat * 0.1) params.seed
  let y := baseY + laneOffset + (noise - 0.5) * riverWidth * params.turbulence * 2.0

  let pos := Point2D.clamp ⟨x, y⟩ 0.0 0.0 params.width params.height
  let visible := x >= 0.0 && x <= params.width
  (pos, visible)

--------------------------------------------------------------------------------
-- Morph Flow
--------------------------------------------------------------------------------

/-- Shape type for morph source/target -/
inductive MorphShape where
  | grid
  | circle
  | random
  deriving Repr, DecidableEq, Inhabited

/-- Easing type for morph transition -/
inductive MorphEasing where
  | easeIn
  | easeOut
  | easeInOut
  deriving Repr, DecidableEq, Inhabited

/-- Parameters for morph flow -/
structure MorphParams extends FlowParams where
  sourceShape : MorphShape := .grid
  targetShape : MorphShape := .circle
  easing : MorphEasing := .easeInOut
  deriving Repr, Inhabited

/-- Apply morph easing function -/
def applyMorphEasing (easing : MorphEasing) (t : Float) : Float :=
  match easing with
  | .easeIn => t * t
  | .easeOut => 1.0 - (1.0 - t) * (1.0 - t)
  | .easeInOut =>
    if t < 0.5 then 2.0 * t * t
    else 1.0 - ((-2.0 * t + 2.0) * (-2.0 * t + 2.0)) / 2.0

/-- Generate grid position for point index -/
def gridPosition (params : FlowParams) (index numPoints : Nat) : Point2D :=
  let cols := Float.sqrt numPoints.toFloat |>.ceil.toUInt64.toNat
  let row := index / cols
  let col := index % cols
  let x := ((col.toFloat + 0.5) / cols.toFloat) * params.width * 0.8 + params.width * 0.1
  let y := ((row.toFloat + 0.5) / cols.toFloat) * params.height * 0.8 + params.height * 0.1
  ⟨x, y⟩

/-- Generate circle position for point index -/
def circlePosition (params : FlowParams) (index numPoints : Nat) : Point2D :=
  let angle := (index.toFloat / numPoints.toFloat) * Float.pi * 2.0
  let radius := Float.min params.width params.height * 0.35
  let x := params.width / 2.0 + Float.cos angle * radius
  let y := params.height / 2.0 + Float.sin angle * radius
  ⟨x, y⟩

/-- Calculate morph position at time t.

    Interpolates between source and target shape positions with easing. -/
def morphPosition (params : MorphParams) (t : Float)
    (source target : Point2D)
    (pointIndex frameIndex : Nat) : Point2D :=
  let easedT := applyMorphEasing params.easing t

  -- Add noise for organic movement (peaks at t=0.5)
  let noise := simplexNoise2D (pointIndex.toFloat * 0.1) (frameIndex.toFloat * 0.02) params.seed
  let noiseOffset := (noise - 0.5) * 20.0 * (1.0 - Float.abs (t - 0.5) * 2.0)

  let x := source.x + (target.x - source.x) * easedT + noiseOffset
  let y := source.y + (target.y - source.y) * easedT + noiseOffset

  Point2D.clamp ⟨x, y⟩ 0.0 0.0 params.width params.height

--------------------------------------------------------------------------------
-- Swarm/Flocking Flow
--------------------------------------------------------------------------------

/-- Parameters for swarm/flocking behavior -/
structure SwarmParams extends FlowParams where
  cohesion : Float := 0.01     -- Attraction to center of mass
  separation : Float := 30.0   -- Minimum distance between particles
  alignment : Float := 0.05    -- Velocity matching strength
  maxSpeed : Float := 5.0      -- Maximum particle velocity
  deriving Repr, Inhabited

/-- Swarm particle state -/
structure SwarmParticle where
  x : Float
  y : Float
  vx : Float
  vy : Float
  deriving Repr, Inhabited

/-- Calculate cohesion force toward center of mass -/
def cohesionForce (params : SwarmParams) (particle : SwarmParticle) (cx cy : Float) : Float × Float :=
  let fx := (cx - particle.x) * params.cohesion
  let fy := (cy - particle.y) * params.cohesion
  (fx, fy)

/-- Calculate separation force from another particle -/
def separationForce (params : SwarmParams) (p1 p2 : SwarmParticle) : Float × Float :=
  let dx := p1.x - p2.x
  let dy := p1.y - p2.y
  let dist := Float.sqrt (dx * dx + dy * dy)
  if dist < params.separation && dist > 0.0 then
    let factor := (params.separation - dist) * 0.1
    (dx / dist * factor, dy / dist * factor)
  else
    (0.0, 0.0)

/-- Calculate boundary avoidance force.

    Returns (fx, fy) force pushing particle away from boundaries. -/
def boundaryForce (params : SwarmParams) (particle : SwarmParticle) : Float × Float :=
  let margin : Float := 50.0
  -- Calculate each boundary force component independently (pure functional)
  let fxLeft := if particle.x < margin
                then (margin - particle.x) * 0.1
                else 0.0
  let fxRight := if particle.x > params.width - margin
                 then -((particle.x - (params.width - margin)) * 0.1)
                 else 0.0
  let fyTop := if particle.y < margin
               then (margin - particle.y) * 0.1
               else 0.0
  let fyBottom := if particle.y > params.height - margin
                  then -((particle.y - (params.height - margin)) * 0.1)
                  else 0.0
  (fxLeft + fxRight, fyTop + fyBottom)

/-- Clamp velocity to max speed -/
def clampVelocity (vx vy maxSpeed : Float) : Float × Float :=
  let speed := Float.sqrt (vx * vx + vy * vy)
  if speed > maxSpeed then
    (vx / speed * maxSpeed, vy / speed * maxSpeed)
  else
    (vx, vy)

/-- Update swarm particle with forces -/
def updateSwarmParticle (params : SwarmParams) (particle : SwarmParticle)
    (fx fy : Float) : SwarmParticle × Point2D :=
  let newVx := particle.vx + fx
  let newVy := particle.vy + fy
  let (clampedVx, clampedVy) := clampVelocity newVx newVy params.maxSpeed
  let newX := particle.x + clampedVx
  let newY := particle.y + clampedVy

  let newParticle := { x := newX, y := newY, vx := clampedVx, vy := clampedVy }
  let pos := Point2D.clamp ⟨newX, newY⟩ 0.0 0.0 params.width params.height
  (newParticle, pos)

end Lattice.Services.Flow.Patterns
