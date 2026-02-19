/-
  Lattice.Services.Expressions.MotionExpressions - Motion physics functions

  Core physics calculations for momentum-based animations:
  - inertiaOscillation: Damped sine wave oscillation
  - bouncePhysics: Bouncing settle with elasticity
  - elasticOscillation: Spring-like elastic motion

  Source: ui/src/services/expressions/motionExpressions.ts
-/

namespace Lattice.Services.Expressions.MotionExpressions

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Default inertia amplitude -/
def defaultAmplitude : Float := 0.1

/-- Default inertia frequency -/
def defaultFrequency : Float := 2.0

/-- Default inertia decay -/
def defaultDecay : Float := 2.0

/-- Default bounce elasticity -/
def defaultElasticity : Float := 0.7

/-- Default bounce gravity -/
def defaultGravity : Float := 4000.0

/-- Default elastic period -/
def defaultPeriod : Float := 0.3

/-- Maximum bounces to simulate -/
def maxBounces : Nat := 10

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

/-- Ensure amplitude is valid -/
def safeAmplitude (amp : Float) : Float :=
  if amp.isFinite then amp else defaultAmplitude

/-- Ensure frequency is valid -/
def safeFrequency (freq : Float) : Float :=
  if freq.isFinite then freq else defaultFrequency

/-- Ensure decay is valid (minimum 0.001) -/
def safeDecay (decay : Float) : Float :=
  if decay.isFinite then Float.max 0.001 decay else defaultDecay

/-- Ensure elasticity is valid (clamped to [0, 1]) -/
def safeElasticity (e : Float) : Float :=
  if e.isFinite then Float.min 1 (Float.max 0 e) else defaultElasticity

/-- Ensure gravity is valid (positive) -/
def safeGravity (g : Float) : Float :=
  if g.isFinite && g > 0 then g else defaultGravity

/-- Ensure period is valid (positive) -/
def safePeriod (p : Float) : Float :=
  if p.isFinite && p > 0 then p else defaultPeriod

--------------------------------------------------------------------------------
-- Inertia Oscillation
--------------------------------------------------------------------------------

/-- Damped sine wave oscillation for inertia effect.

    velocity: Initial velocity component
    amplitude: Oscillation amplitude multiplier
    frequency: Oscillation frequency in Hz
    decay: Exponential decay rate
    t: Time since keyframe (must be positive)

    Returns: Oscillation offset to add to value -/
def inertiaOscillation (velocity amplitude frequency decay t : Float) : Float :=
  if t <= 0 then 0
  else
    let safeAmp := safeAmplitude amplitude
    let safeFreq := safeFrequency frequency
    let safeDec := safeDecay decay
    let phase := safeFreq * t * 2 * Float.pi
    let decayFactor := Float.exp (safeDec * t)
    if decayFactor == 0 then 0
    else velocity * safeAmp * Float.sin phase / decayFactor

/-- Apply inertia to a scalar value -/
def inertiaScalar (value velocity amplitude frequency decay t : Float) : Float :=
  value + inertiaOscillation velocity amplitude frequency decay t

/-- Apply inertia to a vector value -/
def inertiaVector (values velocities : Array Float) (amplitude frequency decay t : Float) : Array Float :=
  values.zipWith velocities fun v vel =>
    v + inertiaOscillation vel amplitude frequency decay t

--------------------------------------------------------------------------------
-- Bounce Physics
--------------------------------------------------------------------------------

/-- Calculate bounce position given time and parameters.

    t: Time since keyframe (must be positive)
    elasticity: Bounce energy retention (0-1)
    gravity: Gravity acceleration

    Returns: Bounce offset to subtract from value -/
def bouncePhysics (t elasticity gravity : Float) : Float :=
  if t <= 0 then 0
  else
    let safeE := safeElasticity elasticity
    let safeG := safeGravity gravity

    -- Calculate which bounce we're in
    let rec findBounce (i : Nat) (bounceTime height : Float) : Float × Float :=
      match i with
      | 0 => (bounceTime, height)
      | n + 1 =>
        if bounceTime <= 0 then (bounceTime, height)
        else
          let bounceDuration := Float.sqrt (2 * height / safeG)
          if bounceTime < bounceDuration * 2 then (bounceTime, height)
          else
            let newTime := bounceTime - bounceDuration * 2
            let newHeight := height * safeE * safeE
            findBounce n newTime newHeight

    let (bounceTime, bounceHeight) := findBounce maxBounces t 1.0

    -- Position within current bounce (parabola)
    let bounceDuration := Float.sqrt (2 * bounceHeight / safeG)
    let bounceT := if bounceDuration == 0 then 0 else bounceTime / (bounceDuration * 2)
    let bounceOffset := bounceHeight * 4 * bounceT * (1 - bounceT)

    bounceOffset * (1 - safeE)

/-- Apply bounce to a scalar value -/
def bounceScalar (value t elasticity gravity : Float) : Float :=
  value - bouncePhysics t elasticity gravity

/-- Apply bounce to a vector value (same offset for all components) -/
def bounceVector (values : Array Float) (t elasticity gravity : Float) : Array Float :=
  let offset := bouncePhysics t elasticity gravity
  values.map (· - offset)

--------------------------------------------------------------------------------
-- Elastic Oscillation
--------------------------------------------------------------------------------

/-- Elastic spring-like oscillation.

    t: Time since keyframe (must be positive)
    amplitude: Maximum displacement
    period: Oscillation period in seconds

    Returns: Oscillation offset to add to value -/
def elasticOscillation (t amplitude period : Float) : Float :=
  if t <= 0 then 0
  else
    let safeAmp := safeAmplitude amplitude
    let safePer := safePeriod period
    let s := safePer / 4
    -- Exponential decay: 2^(-10*t)
    let decay := Float.exp (-10 * t * Float.log 2)
    let phase := (t - s) * 2 * Float.pi / safePer
    safeAmp * decay * Float.sin phase

/-- Apply elastic motion to a scalar value -/
def elasticScalar (value t amplitude period : Float) : Float :=
  value + elasticOscillation t amplitude period

/-- Apply elastic motion to a vector value -/
def elasticVector (values : Array Float) (t amplitude period : Float) : Array Float :=
  let oscillation := elasticOscillation t amplitude period
  values.map (· + oscillation)

--------------------------------------------------------------------------------
-- Main API
--------------------------------------------------------------------------------

/-- Inertia expression for scalar values -/
def inertia (value velocity : Float) (t : Float)
    (amplitude : Float := defaultAmplitude)
    (frequency : Float := defaultFrequency)
    (decay : Float := defaultDecay) : Float :=
  inertiaScalar value velocity amplitude frequency decay t

/-- Inertia expression for vector values -/
def inertiaVec (values velocities : Array Float) (t : Float)
    (amplitude : Float := defaultAmplitude)
    (frequency : Float := defaultFrequency)
    (decay : Float := defaultDecay) : Array Float :=
  inertiaVector values velocities amplitude frequency decay t

/-- Bounce expression for scalar values -/
def bounce (value : Float) (t : Float)
    (elasticity : Float := defaultElasticity)
    (gravity : Float := defaultGravity) : Float :=
  bounceScalar value t elasticity gravity

/-- Bounce expression for vector values -/
def bounceVec (values : Array Float) (t : Float)
    (elasticity : Float := defaultElasticity)
    (gravity : Float := defaultGravity) : Array Float :=
  bounceVector values t elasticity gravity

/-- Elastic expression for scalar values -/
def elastic (value : Float) (t : Float)
    (amplitude : Float := 1.0)
    (period : Float := defaultPeriod) : Float :=
  elasticScalar value t amplitude period

/-- Elastic expression for vector values -/
def elasticVec (values : Array Float) (t : Float)
    (amplitude : Float := 1.0)
    (period : Float := defaultPeriod) : Array Float :=
  elasticVector values t amplitude period

end Lattice.Services.Expressions.MotionExpressions
