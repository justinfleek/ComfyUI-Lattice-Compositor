/-
  Lattice.Services.Physics.Random - Seeded Random Number Generator

  Deterministic random number generator using Mulberry32 algorithm:
  - Seeded initialization for reproducibility
  - Uniform random values in [0, 1)
  - Range-constrained values
  - Gaussian distribution via Box-Muller

  All functions are total and deterministic given the same seed.

  Source: ui/src/services/physics/PhysicsEngine.ts (PhysicsRandom class)
-/

namespace Lattice.Services.Physics.Random

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Physics random number generator state -/
structure PhysicsRandom where
  state : UInt32
  initialSeed : UInt32
  deriving Repr, Inhabited, BEq

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

/-- Create a new RNG with the given seed -/
def mkPhysicsRandom (seed : UInt32) : PhysicsRandom :=
  { state := seed
  , initialSeed := seed }

/-- Reset RNG to initial seed -/
def reset (rng : PhysicsRandom) : PhysicsRandom :=
  { rng with state := rng.initialSeed }

--------------------------------------------------------------------------------
-- Mulberry32 Core
--------------------------------------------------------------------------------

/-- Mulberry32 step - produces next 32-bit value.

    This is a high-quality PRNG suitable for physics simulation.
    Period: 2^32, passes BigCrush test suite.

    @param state Current state
    @return (next value, new state) -/
def mulberry32Step (state : UInt32) : UInt32 × UInt32 :=
  let newState := state + 0x6D2B79F5
  let t1 := newState
  let t2 := (t1 ^^^ (t1 >>> 15)) * 0x85EBCA77
  let t3 := (t2 ^^^ (t2 >>> 13)) * 0xC2B2AE3D
  let result := t3 ^^^ (t3 >>> 16)
  (result, newState)

--------------------------------------------------------------------------------
-- Generation
--------------------------------------------------------------------------------

/-- Generate next random value in [0, 1).

    @param rng Current RNG state
    @return (value in [0,1), new RNG state) -/
def next (rng : PhysicsRandom) : Float × PhysicsRandom :=
  let (raw, newState) := mulberry32Step rng.state
  let value := raw.toFloat / 4294967296.0
  (value, { rng with state := newState })

/-- Generate random value in [min, max).

    @param minVal Minimum value (inclusive)
    @param maxVal Maximum value (exclusive)
    @param rng Current RNG state
    @return (scaled value, new RNG state) -/
def nextRange (minVal maxVal : Float) (rng : PhysicsRandom) : Float × PhysicsRandom :=
  let (val, newRng) := next rng
  let scaled := minVal + val * (maxVal - minVal)
  (scaled, newRng)

/-- Generate Gaussian-distributed value using Box-Muller transform.

    Produces values from standard normal distribution (mean=0, std=1).

    @param rng Current RNG state
    @return (gaussian value, new RNG state) -/
def nextGaussian (rng : PhysicsRandom) : Float × PhysicsRandom :=
  let (u1, rng1) := next rng
  let (u2, rng2) := next rng1
  -- Avoid log(0) by ensuring u1 > epsilon
  let safeU1 := Float.max 0.000001 u1
  let gaussian := Float.sqrt (-2.0 * Float.log safeU1) * Float.cos (2.0 * Float.pi * u2)
  (gaussian, rng2)

/-- Generate N random values.

    Uses fuel parameter for termination proof.

    @param n Number of values to generate
    @param rng Current RNG state
    @return (array of values, new RNG state) -/
def nextN (n : Nat) (rng : PhysicsRandom) : Array Float × PhysicsRandom :=
  go n rng #[]
where
  go : Nat → PhysicsRandom → Array Float → Array Float × PhysicsRandom
  | 0, r, acc => (acc, r)
  | k + 1, r, acc =>
      let (v, r') := next r
      go k r' (acc.push v)

/-- Generate a random unit vector (for direction).

    @param rng Current RNG state
    @return ((x, y) unit vector, new RNG state) -/
def nextUnitVector (rng : PhysicsRandom) : (Float × Float) × PhysicsRandom :=
  let (angle, newRng) := nextRange 0.0 (2.0 * Float.pi) rng
  ((Float.cos angle, Float.sin angle), newRng)

/-- Generate a random value from [-range, +range].

    @param range Half-range (positive)
    @param rng Current RNG state
    @return (value, new RNG state) -/
def nextSymmetric (range : Float) (rng : PhysicsRandom) : Float × PhysicsRandom :=
  nextRange (-range) range rng

--------------------------------------------------------------------------------
-- Noise Functions
--------------------------------------------------------------------------------

/-- Simple 1D value noise based on position and seed.

    Returns consistent value for same (x, seed) pair.

    @param x Position
    @param seed Noise seed
    @return Noise value in [0, 1) -/
def valueNoise1D (x : Float) (seed : UInt32) : Float :=
  -- Hash x position with seed
  let xi := (x * 1000.0).toUInt32
  let combined := xi ^^^ seed
  let (result, _) := mulberry32Step combined
  result.toFloat / 4294967296.0

/-- Simple 2D value noise based on position and seed.

    Returns consistent value for same (x, y, seed) tuple.

    @param x X position
    @param y Y position
    @param seed Noise seed
    @return Noise value in [0, 1) -/
def valueNoise2D (x y : Float) (seed : UInt32) : Float :=
  let xi := (x * 1000.0).toUInt32
  let yi := (y * 1000.0).toUInt32
  let combined := xi ^^^ (yi * 31) ^^^ seed
  let (result, _) := mulberry32Step combined
  result.toFloat / 4294967296.0

/-- Generate turbulence noise for wind simulation.

    Combines multiple octaves of noise.

    @param x X position
    @param y Y position
    @param time Time value
    @param frequency Base frequency
    @param seed Noise seed
    @return (noiseX, noiseY) turbulence values in [-1, 1] -/
def turbulenceNoise (x y time frequency : Float) (seed : UInt32) : Float × Float :=
  let scale1 := frequency
  let scale2 := frequency * 2.0
  -- Octave 1
  let noise1X := valueNoise2D (x * scale1 + time) (y * scale1) seed
  let noise1Y := valueNoise2D (x * scale1) (y * scale1 + time) (seed + 1)
  -- Octave 2 (higher frequency, lower amplitude)
  let noise2X := valueNoise2D (x * scale2 + time * 1.3) (y * scale2) (seed + 2)
  let noise2Y := valueNoise2D (x * scale2) (y * scale2 + time * 1.3) (seed + 3)
  -- Combine and convert to [-1, 1]
  let combinedX := (noise1X + noise2X * 0.5) / 1.5 * 2.0 - 1.0
  let combinedY := (noise1Y + noise2Y * 0.5) / 1.5 * 2.0 - 1.0
  (combinedX, combinedY)

end Lattice.Services.Physics.Random
