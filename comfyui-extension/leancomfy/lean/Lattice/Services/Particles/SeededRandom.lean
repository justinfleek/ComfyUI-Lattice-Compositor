/-
  Lattice.Services.Particles.SeededRandom - Seeded Random Number Generator

  Uses mulberry32 algorithm for deterministic, reproducible randomness.
  This is CRITICAL for particle system determinism - same seed always
  produces the same sequence of numbers.

  Source: ui/src/services/particles/SeededRandom.ts
-/

namespace Lattice.Services.Particles.SeededRandom

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def pi : Float := 3.14159265358979323846

/-- Mulberry32 magic constant -/
def mulberry32Magic : UInt32 := 0x6D2B79F5

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Random generator state -/
structure RngState where
  state : UInt32
  initialSeed : UInt32
  deriving Repr, Inhabited

/-- 2D point -/
structure Point2D where
  x : Float
  y : Float
  deriving Repr, Inhabited

/-- 3D point -/
structure Point3D where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Core Operations
--------------------------------------------------------------------------------

/-- Create new RNG with seed -/
def create (seed : UInt32 := 12345) : RngState :=
  { state := seed, initialSeed := seed }

/-- Reset to initial seed -/
def reset (rng : RngState) : RngState :=
  { rng with state := rng.initialSeed }

/-- Set new seed -/
def setSeed (seed : UInt32) (rng : RngState) : RngState :=
  { state := seed, initialSeed := seed }

/-- Get current state for checkpointing -/
def getState (rng : RngState) : UInt32 := rng.state

/-- Restore state from checkpoint -/
def setState (state : UInt32) (rng : RngState) : RngState :=
  { rng with state := state }

/-- Get initial seed -/
def getSeed (rng : RngState) : UInt32 := rng.initialSeed

--------------------------------------------------------------------------------
-- Mulberry32 Algorithm
--------------------------------------------------------------------------------

/-- XOR operation for UInt32 -/
private def xor (a b : UInt32) : UInt32 := a ^^^ b

/-- Bitwise OR for UInt32 -/
private def bor (a b : UInt32) : UInt32 := a ||| b

/-- Unsigned right shift -/
private def shr (a : UInt32) (n : UInt32) : UInt32 := a >>> n.toNat

/-- Approximate imul (integer multiply with 32-bit wrap) -/
private def imul (a b : UInt32) : UInt32 := a * b

/--
  Get next random number in [0, 1)
  Uses mulberry32 algorithm

  Returns (value, newState)
-/
def next (rng : RngState) : Float × RngState :=
  let newState := rng.state + mulberry32Magic
  let t1 := xor newState (shr newState 15)
  let t2 := imul t1 (bor t1 1)
  let t3 := xor t2 (t2 + imul (xor t2 (shr t2 7)) (bor t2 61))
  let t4 := xor t3 (shr t3 14)
  let value := t4.toNat.toFloat / 4294967296.0
  (value, { rng with state := newState })

--------------------------------------------------------------------------------
-- Range Operations
--------------------------------------------------------------------------------

/-- Get random in range [min, max] -/
def range (min max : Float) (rng : RngState) : Float × RngState :=
  let (r, rng') := next rng
  (min + r * (max - min), rng')

/-- Get random integer in range [min, max] inclusive -/
def int (min max : Int) (rng : RngState) : Int × RngState :=
  let (r, rng') := range min.toFloat (max.toFloat + 1.0) rng
  (Float.floor r |>.toUInt64.toNat |> Int.ofNat, rng')

/-- Get random value with variance: base + random(-variance, +variance) -/
def variance (base var : Float) (rng : RngState) : Float × RngState :=
  let (r, rng') := next rng
  (base + (r - 0.5) * 2.0 * var, rng')

/-- Get random boolean with given probability of true -/
def bool (probability : Float := 0.5) (rng : RngState) : Bool × RngState :=
  let (r, rng') := next rng
  (r < probability, rng')

--------------------------------------------------------------------------------
-- Angular Operations
--------------------------------------------------------------------------------

/-- Get random angle in radians [0, 2*PI) -/
def angle (rng : RngState) : Float × RngState :=
  let (r, rng') := next rng
  (r * pi * 2.0, rng')

--------------------------------------------------------------------------------
-- Geometric Distributions
--------------------------------------------------------------------------------

/-- Get random point in unit circle -/
def inCircle (rng : RngState) : Point2D × RngState :=
  let (a, rng1) := angle rng
  let (r, rng2) := next rng1
  let radius := Float.sqrt r
  ({ x := radius * Float.cos a, y := radius * Float.sin a }, rng2)

/-- Get random point on unit sphere -/
def onSphere (rng : RngState) : Point3D × RngState :=
  let (theta, rng1) := angle rng
  let (u, rng2) := next rng1
  let phi := Float.acos (2.0 * u - 1.0)
  let sinPhi := Float.sin phi
  ({ x := sinPhi * Float.cos theta
   , y := sinPhi * Float.sin theta
   , z := Float.cos phi }, rng2)

--------------------------------------------------------------------------------
-- Statistical Distributions
--------------------------------------------------------------------------------

/--
  Get random number from Gaussian/normal distribution
  Uses Box-Muller transform for deterministic gaussian sampling
-/
def gaussian (mean stdDev : Float := 0.0) (rng : RngState) : Float × RngState :=
  let stdDev' := if stdDev == 0.0 then 1.0 else stdDev
  let (u1, rng1) := next rng
  let (u2, rng2) := next rng1
  -- Prevent log(0)
  let u1' := if u1 == 0.0 then 1e-10 else u1
  -- Box-Muller transform
  let z := Float.sqrt (-2.0 * Float.log u1') * Float.cos (2.0 * pi * u2)
  (mean + z * stdDev', rng2)

--------------------------------------------------------------------------------
-- Batch Operations (for convenience)
--------------------------------------------------------------------------------

/-- Generate n random numbers in [0, 1) -/
def nextN (n : Nat) (rng : RngState) : List Float × RngState :=
  let rec go (count : Nat) (acc : List Float) (r : RngState) : List Float × RngState :=
    match count with
    | 0 => (acc.reverse, r)
    | k + 1 =>
      let (v, r') := next r
      go k (v :: acc) r'
  go n [] rng

end Lattice.Services.Particles.SeededRandom
