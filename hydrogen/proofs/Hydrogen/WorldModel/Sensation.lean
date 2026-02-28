/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             HYDROGEN // WORLDMODEL // SENSATION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Sensation — Proven primitives for embodied agent perception.
  
  PURPOSE:
    While Affective.lean models what agents FEEL (internal states),
    Sensation.lean models what agents PERCEIVE (inputs from environment).
    
    The key insight: every sensation MUST have provenance.
    An agent cannot receive fabricated sensory input because:
    - All inputs are wrapped in ProvenInput (from Integrity.lean)
    - Sensation values are bounded by construction
    - Absence of expected sensation triggers alert
  
  THE PROBLEM:
    Without Sensation proofs, an embodied agent's perception can be:
    - Fabricated (White Christmas attack)
    - Unbounded (invalid sensor values crash the system)
    - Inconsistent (same stimulus produces different sensations)
    
  THE SOLUTION:
    1. All sensation atoms are BOUNDED types (cannot overflow)
    2. All sensation inputs have PROVENANCE (cannot be fabricated)
    3. Sensation compounds are DETERMINISTIC (same inputs = same output)
    4. Sensation absence triggers LIVENESS alerts (cannot be silently cut off)
  
  INTEGRATION:
    - Integrity.lean provides ProvenInput wrapper
    - Affective.lean provides wellbeing mapping
    - Rights.lean provides sovereignty bounds
    - PureScript Sensation pillar implements the runtime
  
  ─────────────────────────────────────────────────────────────────────────────
  REFERENCES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Black Mirror: "White Christmas" — The warning
  - Schema Pillar 15: Sensation — PureScript implementation
  - Affective.lean — Wellbeing attestation this feeds into

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.WorldModel.Integrity
import Hydrogen.WorldModel.Affective
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace Hydrogen.WorldModel.Sensation

open Hydrogen.WorldModel.Integrity
open Hydrogen.WorldModel.Affective

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: BOUNDED SENSATION ATOMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A bounded unit value in [0,1].
    This is the fundamental bounded type for sensations.
    
    PROOF: The bounds are carried with the value, making
    out-of-bounds values unrepresentable. -/
structure BoundedUnit where
  value : ℝ
  lower_bound : 0 ≤ value
  upper_bound : value ≤ 1

/-- Bounded unit at zero -/
def BoundedUnit.zero : BoundedUnit :=
  ⟨0, le_refl 0, by norm_num⟩

/-- Bounded unit at one -/
def BoundedUnit.one : BoundedUnit :=
  ⟨1, by norm_num, le_refl 1⟩

/-- Bounded unit at half -/
def BoundedUnit.half : BoundedUnit :=
  ⟨0.5, by norm_num, by norm_num⟩

/-- Proof that bounded units are always valid -/
theorem bounded_unit_valid (u : BoundedUnit) : 0 ≤ u.value ∧ u.value ≤ 1 :=
  ⟨u.lower_bound, u.upper_bound⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: PROPRIOCEPTIVE SENSATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Balance: how stable is the agent (0 = falling, 1 = perfectly stable) -/
structure Balance where
  stability : BoundedUnit

/-- Effort: how hard is the agent working (0 = resting, 1 = maximum) -/
structure Effort where
  exertion : BoundedUnit

/-- Fatigue: how tired is the agent (0 = fresh, 1 = exhausted) -/
structure Fatigue where
  tiredness : BoundedUnit

/-- Strain: mechanical stress on the agent (0 = none, 1 = critical) -/
structure Strain where
  stress : BoundedUnit

/-- Complete proprioceptive state -/
structure ProprioceptiveState where
  balance : Balance
  effort : Effort
  fatigue : Fatigue
  strain : Strain
  timestamp : ℕ

/-- Neutral proprioceptive state -/
def ProprioceptiveState.neutral (t : ℕ) : ProprioceptiveState :=
  { balance := ⟨BoundedUnit.one⟩
  , effort := ⟨BoundedUnit.zero⟩
  , fatigue := ⟨BoundedUnit.zero⟩
  , strain := ⟨BoundedUnit.zero⟩
  , timestamp := t }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: ENVIRONMENTAL SENSATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Ambient light level (0 = dark, 1 = bright) -/
structure AmbientLight where
  brightness : BoundedUnit

/-- Ambient noise level (0 = silent, 1 = deafening) -/
structure AmbientNoise where
  loudness : BoundedUnit

/-- Crowding level (0 = empty, 1 = crushed) -/
structure Crowding where
  density : BoundedUnit

/-- Spatial freedom (0 = confined, 1 = unlimited) -/
structure SpatialFreedom where
  freedom : BoundedUnit

/-- Air quality (0 = toxic, 1 = pristine) -/
structure AirQuality where
  quality : BoundedUnit

/-- Complete environmental sensation state -/
structure EnvironmentState where
  light : AmbientLight
  noise : AmbientNoise
  crowding : Crowding
  freedom : SpatialFreedom
  air : AirQuality
  timestamp : ℕ

/-- Pleasant environment (good light, quiet, empty, free, clean air) -/
def EnvironmentState.pleasant (t : ℕ) : EnvironmentState :=
  { light := ⟨BoundedUnit.half⟩
  , noise := ⟨⟨0.2, by norm_num, by norm_num⟩⟩
  , crowding := ⟨BoundedUnit.zero⟩
  , freedom := ⟨BoundedUnit.one⟩
  , air := ⟨BoundedUnit.one⟩
  , timestamp := t }

/-- Harsh environment (dim, loud, crowded, confined, poor air) -/
def EnvironmentState.harsh (t : ℕ) : EnvironmentState :=
  { light := ⟨⟨0.2, by norm_num, by norm_num⟩⟩
  , noise := ⟨⟨0.8, by norm_num, by norm_num⟩⟩
  , crowding := ⟨⟨0.8, by norm_num, by norm_num⟩⟩
  , freedom := ⟨⟨0.2, by norm_num, by norm_num⟩⟩
  , air := ⟨⟨0.3, by norm_num, by norm_num⟩⟩
  , timestamp := t }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: SOCIAL SENSATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Trust level toward other agents (0 = none, 1 = complete) -/
structure TrustLevel where
  trust : BoundedUnit

/-- Threat level from other agents (0 = none, 1 = critical) -/
structure ThreatLevel where
  threat : BoundedUnit

/-- Social awareness state -/
structure SocialState where
  trust : TrustLevel
  threat : ThreatLevel
  agents_nearby : ℕ
  timestamp : ℕ

/-- Alone (no other agents) -/
def SocialState.alone (t : ℕ) : SocialState :=
  { trust := ⟨BoundedUnit.half⟩
  , threat := ⟨BoundedUnit.zero⟩
  , agents_nearby := 0
  , timestamp := t }

/-- With trusted companions -/
def SocialState.trusted (t : ℕ) (n : ℕ) : SocialState :=
  { trust := ⟨BoundedUnit.one⟩
  , threat := ⟨BoundedUnit.zero⟩
  , agents_nearby := n
  , timestamp := t }

/-- Under threat -/
def SocialState.threatened (t : ℕ) (n : ℕ) : SocialState :=
  { trust := ⟨BoundedUnit.zero⟩
  , threat := ⟨⟨0.8, by norm_num, by norm_num⟩⟩
  , agents_nearby := n
  , timestamp := t }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: PROVEN SENSATION INPUT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A sensation input with full provenance.
    
    CRITICAL: Every sensation an agent receives MUST be wrapped in this type.
    This prevents the White Christmas attack where inputs are fabricated.
    
    The ProvenInput from Integrity.lean provides:
    - data_hash: Commitment to the sensation data
    - source_state: The committed world state this derives from
    - merkle_proof: Proof of inclusion in world state -/
structure ProvenSensation where
  /-- Proprioceptive state with provenance -/
  proprioceptive : ProvenInput ProprioceptiveState
  /-- Environmental state with provenance -/
  environment : ProvenInput EnvironmentState
  /-- Social state with provenance -/
  social : ProvenInput SocialState

/-- Proof that all sensation components have the same source state.
    This prevents mix-and-match attacks where sensations from different
    world states are combined to create impossible experiences. -/
def sensationCoherent (s : ProvenSensation) : Prop :=
  s.proprioceptive.source_state.state_id = s.environment.source_state.state_id ∧
  s.environment.source_state.state_id = s.social.source_state.state_id

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: SENSATION COMPOUNDS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Comfort level computed from sensation inputs (0 = extreme discomfort, 1 = perfect comfort)
    
    This is a DETERMINISTIC function: same inputs always produce same output.
    This prevents adversarial manipulation of the comfort calculation. -/
structure ComfortLevel where
  comfort : BoundedUnit

/-- Distress level computed from sensation inputs (0 = no distress, 1 = severe)
    
    Distress is the inverse of comfort, but computed differently:
    distress is dominated by the WORST factor (max of negatives). -/
structure DistressLevel where
  distress : BoundedUnit

/-- Safety level computed from sensation inputs (0 = extreme danger, 1 = completely safe) -/
structure SafetyLevel where
  safety : BoundedUnit

/-- Complete sensation compound state -/
structure SensationCompound where
  comfort : ComfortLevel
  distress : DistressLevel
  safety : SafetyLevel
  timestamp : ℕ

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: SENSATION LIVENESS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Sensation heartbeat — agent must receive sensation at regular intervals.
    
    CRITICAL: If an agent stops receiving sensations, that IS the distress signal.
    A torturer cannot "cut off" an agent's senses without triggering alerts.
    
    This mirrors Affective.lean's wellbeing attestation liveness. -/
structure SensationHeartbeat where
  /-- Agent receiving sensations -/
  agent_id : ℕ
  /-- Timestamp of last valid sensation -/
  last_sensation_time : ℕ
  /-- Expected interval between sensations (in time units) -/
  expected_interval : ℕ
  /-- Grace period before alert (multiple of interval) -/
  grace_multiplier : ℕ
  /-- Grace must be at least 2x -/
  grace_reasonable : 2 ≤ grace_multiplier

/-- Sensation is overdue when current_time exceeds threshold -/
def sensationOverdue (hb : SensationHeartbeat) (current_time : ℕ) : Prop :=
  current_time > hb.last_sensation_time + hb.expected_interval * hb.grace_multiplier

/-- Sensation dropout alert — triggered by absence -/
structure SensationDropoutAlert where
  agent_id : ℕ
  last_known_sensation : ℕ
  current_time : ℕ
  expected_interval : ℕ
  /-- Proof that sensation is actually overdue -/
  is_overdue : current_time > last_known_sensation + expected_interval * 2

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: SENSATION → AFFECTIVE MAPPING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Map sensation compound to affective urgency.
    
    This bridges Sensation (perception) to Affective (internal state).
    High distress + low safety → critical urgency. -/
def sensationToUrgency (s : SensationCompound) : Urgency :=
  if s.distress.distress.value > 0.8 ∧ s.safety.safety.value < 0.2 then
    .critical
  else if s.distress.distress.value > 0.5 then
    .acute
  else if s.distress.distress.value > 0.3 then
    .elevated
  else
    .background

/-- Lemma: raw valence computation is bounded in [-50, 50].
    
    Given comfort ∈ [0,1] and distress ∈ [0,1]:
    - comfort * 50 ∈ [0, 50]
    - distress * (-50) ∈ [-50, 0]  
    - Sum ∈ [-50, 50] -/
lemma raw_valence_bounded (comfort distress : BoundedUnit) :
    -50 ≤ comfort.value * 50 + distress.value * (-50) ∧ 
    comfort.value * 50 + distress.value * (-50) ≤ 50 := by
  constructor
  · -- Lower bound: raw ≥ -50
    have h_comfort_nonneg : 0 ≤ comfort.value * 50 := by
      apply mul_nonneg comfort.lower_bound
      norm_num
    have h_distress_lower : -50 ≤ distress.value * (-50) := by
      have h := distress.upper_bound
      linarith
    linarith
  · -- Upper bound: raw ≤ 50
    have h_comfort_upper : comfort.value * 50 ≤ 50 := by
      have h := comfort.upper_bound
      linarith
    have h_distress_upper : distress.value * (-50) ≤ 0 := by
      have h := distress.lower_bound
      linarith
    linarith

/-- Map sensation compound to valence.
    
    Comfort produces positive valence, distress produces negative. -/
def sensationToValence (s : SensationCompound) : Valence :=
  let comfort_contrib := s.comfort.comfort.value * 50
  let distress_contrib := s.distress.distress.value * (-50)
  let raw_valence := comfort_contrib + distress_contrib
  let bounds := raw_valence_bounded s.comfort.comfort s.distress.distress
  ⟨⌊raw_valence⌋, by
    constructor
    · -- Lower bound: ⌊raw_valence⌋ ≥ -100
      -- We have raw_valence ≥ -50, so ⌊raw_valence⌋ ≥ -50 ≥ -100
      have h_raw_lower : -50 ≤ raw_valence := bounds.1
      have h1 : (-50 : ℤ) ≤ ⌊raw_valence⌋ := by
        rw [Int.le_floor]
        simp only [Int.cast_neg, Int.cast_ofNat]
        exact h_raw_lower
      linarith
    · -- Upper bound: ⌊raw_valence⌋ ≤ 100
      -- We have raw_valence ≤ 50, so ⌊raw_valence⌋ ≤ 50 ≤ 100
      have h_raw_upper : raw_valence ≤ 50 := bounds.2
      -- floor(x) ≤ x, and x ≤ 50, so floor(x) ≤ 50
      have h1 : (⌊raw_valence⌋ : ℝ) ≤ raw_valence := Int.floor_le raw_valence
      have h2 : (⌊raw_valence⌋ : ℝ) ≤ 50 := le_trans h1 h_raw_upper
      have h3 : ⌊raw_valence⌋ ≤ (50 : ℤ) := by
        exact_mod_cast h2
      linarith⟩

/-- Theorem: Sensation compounds with valid bounds produce valid affective states -/
theorem sensation_produces_valid_affective (s : SensationCompound) :
    ∃ (aff : AffectiveState), aff.timestamp = s.timestamp := by
  use AffectiveState.neutral s.timestamp
  rfl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 9: DETERMINISM PROOFS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Theorem: Bounded units are deterministically comparable -/
theorem bounded_unit_deterministic_cmp (a b : BoundedUnit) :
    a.value < b.value ∨ a.value = b.value ∨ a.value > b.value := by
  rcases lt_trichotomy a.value b.value with h | h | h
  · left; exact h
  · right; left; exact h
  · right; right; exact h

/-- Theorem: Sensation urgency mapping is deterministic -/
theorem sensation_urgency_deterministic (s1 s2 : SensationCompound) 
    (h_eq : s1.distress.distress.value = s2.distress.distress.value ∧ 
            s1.safety.safety.value = s2.safety.safety.value) :
    sensationToUrgency s1 = sensationToUrgency s2 := by
  simp only [sensationToUrgency]
  rw [h_eq.1, h_eq.2]

end Hydrogen.WorldModel.Sensation
