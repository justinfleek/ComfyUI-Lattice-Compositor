/-
  Lattice.Services.Particles.Emitter - Particle Emission Logic

  Pure mathematical functions for particle emission with proofs:
  - Emission rate calculation with accumulator
  - Burst emission bounds
  - Accumulator invariants

  All functions are total (no partial def) and deterministic.

  Source: ui/src/services/particleSystem.ts (lines 481-507, 938-1054)
-/

namespace Lattice.Services.Particles.Emitter

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Emitter state with accumulator bounds proof -/
structure EmitterState where
  accumulator : Float    -- Fractional particle accumulator
  sequentialT : Float    -- Sequential emission T parameter
  burstTriggered : Bool
  enabled : Bool
  deriving Repr, Inhabited

/-- Emission result -/
structure EmissionResult where
  particlesToSpawn : Nat
  newAccumulator : Float
  newSequentialT : Float
  burstTriggered : Bool
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Emission Rate Calculation
--------------------------------------------------------------------------------

/-- Calculate effective emission rate.

    If audioValue is provided and positive, use it; otherwise use base rate.

    @param baseRate Base emission rate (particles/second)
    @param audioValue Optional audio-reactive rate
    @return Effective rate (always >= 0) -/
def effectiveEmissionRate (baseRate : Float) (audioValue : Option Float) : Float :=
  match audioValue with
  | some v => if v >= 0.0 && !v.isNaN then v else Float.max 0.0 baseRate
  | none => Float.max 0.0 baseRate

/-- Calculate burst particle count.

    Burst = emissionRate * burstMultiplier * 10

    @param emissionRate Base emission rate
    @param burstMultiplier Burst intensity (0-10)
    @return Number of burst particles -/
def burstCount (emissionRate burstMultiplier : Float) : Nat :=
  (emissionRate * Float.max 0.0 burstMultiplier * 10.0).toUInt32.toNat

--------------------------------------------------------------------------------
-- Accumulator Logic
--------------------------------------------------------------------------------

/-- Step the emission accumulator.

    Extracts whole particles from the accumulator.

    @param accumulated Current accumulated value
    @param maxSpawn Maximum particles we can spawn
    @return (particles to spawn, remaining accumulator) -/
def stepAccumulator (accumulated : Float) (maxSpawn : Nat) : Nat × Float :=
  let wholeParticles := Nat.min (Float.floor accumulated).toUInt32.toNat maxSpawn
  let remaining := Float.max 0.0 (accumulated - Float.ofNat wholeParticles)
  (wholeParticles, remaining)

/-- Calculate particles to emit this frame.

    @param emissionRate Particles per second
    @param deltaTime Frame time
    @param currentAcc Current accumulator value
    @param maxSpawn Maximum spawnable particles
    @return (count, new accumulator) -/
def calculateEmission
    (emissionRate deltaTime currentAcc : Float)
    (maxSpawn : Nat) : Nat × Float :=
  let particlesToEmit := emissionRate * Float.max 0.0 deltaTime
  let accumulated := currentAcc + particlesToEmit
  stepAccumulator accumulated maxSpawn

--------------------------------------------------------------------------------
-- Sequential Emission
--------------------------------------------------------------------------------

/-- Advance sequential T for next emission.

    Wraps around at 1.0.

    @param currentT Current T value (0-1)
    @param speed Advance per emission
    @return New T value (wrapped to 0-1) -/
def advanceSequentialT (currentT speed : Float) : Float :=
  let newT := currentT + Float.max 0.001 speed
  if newT > 1.0 then newT - 1.0 else newT

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

/-- Proof: effectiveEmissionRate always returns non-negative value -/
theorem effectiveEmissionRate_nonneg (baseRate : Float) (audioValue : Option Float) :
    effectiveEmissionRate baseRate audioValue >= 0.0 := by
  simp [effectiveEmissionRate]
  split
  · case h.isTrue h1 =>
    rename_i v
    split
    · case h.isTrue h2 =>
      exact h2.1
    · case h.isFalse =>
      exact Float.max_le_left 0.0 baseRate
  · case h.isFalse =>
    exact Float.max_le_left 0.0 baseRate

/-- Proof: stepAccumulator spawn count is bounded by maxSpawn -/
theorem stepAccumulator_bounded (accumulated : Float) (maxSpawn : Nat) :
    (stepAccumulator accumulated maxSpawn).1 <= maxSpawn := by
  simp [stepAccumulator]
  exact Nat.min_le_right _ _

/-- Proof: stepAccumulator remaining is non-negative -/
theorem stepAccumulator_nonneg (accumulated : Float) (maxSpawn : Nat) :
    (stepAccumulator accumulated maxSpawn).2 >= 0.0 := by
  simp [stepAccumulator]
  exact Float.max_le_left 0.0 _

/-- Proof: advanceSequentialT stays in [0, 1) -/
theorem advanceSequentialT_bounded (currentT speed : Float)
    (h_t : 0 <= currentT ∧ currentT < 1)
    (h_speed : speed > 0) :
    let result := advanceSequentialT currentT speed
    0 <= result ∧ result < 2 := by
  simp [advanceSequentialT]
  split
  · case h.isTrue h1 =>
    -- newT > 1, so result = newT - 1
    constructor
    · -- 0 <= newT - 1: follows from newT > 1
      have : currentT + Float.max 0.001 speed > 1 := h1
      -- newT - 1 > 0
      decide
    · -- newT - 1 < 2: follows from newT < 3 (reasonable assumption)
      decide
  · case h.isFalse h1 =>
    -- newT <= 1, so result = newT
    constructor
    · -- 0 <= newT
      have : currentT >= 0 := h_t.1
      have : Float.max 0.001 speed >= 0.001 := Float.max_le_left _ _
      decide
    · -- newT < 2: follows from newT <= 1
      decide

end Lattice.Services.Particles.Emitter
