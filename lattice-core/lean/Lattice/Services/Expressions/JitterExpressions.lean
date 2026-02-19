/-
  Lattice.Services.Expressions.JitterExpressions - Noise and jitter functions

  Expression functions for adding noise/randomness:
  - jitter: Simple noise based on sine waves
  - temporalJitter: Smooth noise with Catmull-Rom interpolation

  Source: ui/src/services/expressions/jitterExpressions.ts
-/

namespace Lattice.Services.Expressions.JitterExpressions

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Maximum octaves to prevent excessive computation -/
def maxOctaves : Nat := 10

/-- Default frequency -/
def defaultFrequency : Float := 5.0

/-- Default amplitude -/
def defaultAmplitude : Float := 50.0

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

/-- Clamp octaves to valid range [1, maxOctaves] -/
def clampOctaves (octaves : Float) : Nat :=
  if !octaves.isFinite || octaves < 1 then 1
  else if octaves > maxOctaves.toFloat then maxOctaves
  else octaves.toUInt64.toNat

/-- Ensure frequency is valid -/
def safeFrequency (freq : Float) : Float :=
  if !freq.isFinite || freq <= 0 then defaultFrequency else freq

--------------------------------------------------------------------------------
-- Simple Noise (Sine-based)
--------------------------------------------------------------------------------

/-- Generate noise value from sine waves with multiple octaves.
    seed: offset for different components
    t: time value
    frequency: base frequency
    octaves: number of octave layers
    ampMultiplier: amplitude decay per octave -/
def sineNoise (seed : Float) (t : Float) (frequency : Float)
    (octaves : Nat) (ampMultiplier : Float) : Float :=
  let rec go (i : Nat) (result amp freq : Float) : Float × Float × Float :=
    match i with
    | 0 => (result, amp, freq)
    | n + 1 =>
      let phase := t * frequency * freq * Float.pi * 2 + seed * 1000
      let noise1 := amp * Float.sin phase
      let noise2 := amp * 0.5 * Float.sin (phase * 1.5 - seed * 500)
      go n (result + noise1 + noise2) (amp * ampMultiplier) (freq * 2)
  let (result, _, _) := go octaves 0 1 1
  -- Normalize by expected sum of geometric series
  let denominator := 1 + (octaves.toFloat - 1) * ampMultiplier
  if !denominator.isFinite || denominator == 0 then result
  else result / denominator

--------------------------------------------------------------------------------
-- Jitter Function
--------------------------------------------------------------------------------

/-- Jitter: Add noise to a scalar value -/
def jitterScalar (value t : Float) (frequency amplitude : Float)
    (octaves : Nat) (ampMultiplier : Float) : Float :=
  let noise := sineNoise 0 t frequency octaves ampMultiplier
  value + noise * amplitude

/-- Jitter: Add noise to a vector value.
    Each component uses a different seed for uncorrelated noise. -/
def jitterVector (values : Array Float) (t : Float) (frequency amplitude : Float)
    (octaves : Nat) (ampMultiplier : Float) : Array Float :=
  values.mapIdx fun i v =>
    let noise := sineNoise i.val.toFloat t frequency octaves ampMultiplier
    v + noise * amplitude

--------------------------------------------------------------------------------
-- Smooth Noise (Catmull-Rom Interpolated)
--------------------------------------------------------------------------------

/-- Deterministic random from integer index and seed -/
def deterministicRand (n : Float) (seed : Float) : Float :=
  let x := Float.sin (n * 12.9898 + seed * 78.233) * 43758.5453
  x - Float.floor x

/-- Catmull-Rom spline interpolation between 4 values -/
def catmullRom (v0 v1 v2 v3 t : Float) : Float :=
  let t2 := t * t
  let t3 := t2 * t
  0.5 * (2 * v1 +
         (-v0 + v2) * t +
         (2 * v0 - 5 * v1 + 4 * v2 - v3) * t2 +
         (-v0 + 3 * v1 - 3 * v2 + v3) * t3)

/-- Smooth noise with temporal correlation using Catmull-Rom interpolation -/
def smoothNoise (seed : Float) (t : Float) (frequency : Float) : Float :=
  let period := 1 / frequency
  let index := Float.floor (t / period)
  let frac := t / period - index

  -- Generate random values at integer positions
  let v0 := deterministicRand (index - 1) seed * 2 - 1
  let v1 := deterministicRand index seed * 2 - 1
  let v2 := deterministicRand (index + 1) seed * 2 - 1
  let v3 := deterministicRand (index + 2) seed * 2 - 1

  catmullRom v0 v1 v2 v3 frac

--------------------------------------------------------------------------------
-- Temporal Jitter Function
--------------------------------------------------------------------------------

/-- Temporal jitter: Smooth noise on a scalar value -/
def temporalJitterScalar (value t : Float) (frequency amplitude : Float)
    (octaves : Nat) : Float :=
  let rec go (i : Nat) (result amp freq : Float) : Float :=
    match i with
    | 0 => result
    | n + 1 =>
      let noise := smoothNoise (i.toFloat * 100) (t * freq / frequency) frequency
      go n (result + noise * amp) (amp * 0.5) (freq * 2)
  let result := go octaves 0 amplitude frequency
  value + result

/-- Temporal jitter: Smooth noise on a vector value -/
def temporalJitterVector (values : Array Float) (t : Float) (frequency amplitude : Float)
    (octaves : Nat) : Array Float :=
  values.mapIdx fun idx v =>
    let rec go (i : Nat) (result amp freq : Float) : Float :=
      match i with
      | 0 => result
      | n + 1 =>
        let seed := idx.val.toFloat * 100 + i.toFloat * 1000
        let noise := smoothNoise seed (t * freq / frequency) frequency
        go n (result + noise * amp) (amp * 0.5) (freq * 2)
    let result := go octaves 0 amplitude frequency
    v + result

--------------------------------------------------------------------------------
-- Main API
--------------------------------------------------------------------------------

/-- Jitter expression for scalar values -/
def jitter (value t : Float) (frequency : Float := defaultFrequency)
    (amplitude : Float := defaultAmplitude) (octaves : Float := 1)
    (ampMultiplier : Float := 0.5) : Float :=
  let safeOctaves := clampOctaves octaves
  let safeFreq := safeFrequency frequency
  jitterScalar value t safeFreq amplitude safeOctaves ampMultiplier

/-- Jitter expression for vector values -/
def jitterVec (values : Array Float) (t : Float) (frequency : Float := defaultFrequency)
    (amplitude : Float := defaultAmplitude) (octaves : Float := 1)
    (ampMultiplier : Float := 0.5) : Array Float :=
  let safeOctaves := clampOctaves octaves
  let safeFreq := safeFrequency frequency
  jitterVector values t safeFreq amplitude safeOctaves ampMultiplier

/-- Temporal jitter expression for scalar values -/
def temporalJitter (value t : Float) (frequency : Float := defaultFrequency)
    (amplitude : Float := defaultAmplitude) (octaves : Float := 1) : Float :=
  let safeOctaves := clampOctaves octaves
  let safeFreq := safeFrequency frequency
  temporalJitterScalar value t safeFreq amplitude safeOctaves

/-- Temporal jitter expression for vector values -/
def temporalJitterVec (values : Array Float) (t : Float) (frequency : Float := defaultFrequency)
    (amplitude : Float := defaultAmplitude) (octaves : Float := 1) : Array Float :=
  let safeOctaves := clampOctaves octaves
  let safeFreq := safeFrequency frequency
  temporalJitterVector values t safeFreq amplitude safeOctaves

end Lattice.Services.Expressions.JitterExpressions
