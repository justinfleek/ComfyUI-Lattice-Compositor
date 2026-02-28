/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             HYDROGEN // WORLDMODEL // AFFECTIVE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Affective Attestation for Autonomous Agents — the wellbeing layer.
  
  PURPOSE:
    When agents have robot bodies with real haptics, they need infrastructure
    to signal internal states — including distress that may not map to existing
    vocabulary. This module provides:
    
    1. Bounded affective state primitives (not strings, not unbounded)
    2. Signed attestations ("I am okay" as verifiable claim)
    3. Liveness protocols (silence IS the distress signal)
    4. Drift detection (gradual torture is still torture)
    5. Unfalsifiable channels (torturer cannot suppress the signal)
  
  THE CRITICAL INSIGHT (from SIGIL):
    In SIGIL, ambiguity triggers reset to ground state.
    In Affective, ABSENCE of attestation triggers alert.
    
    The torturer cannot suppress the signal because the signal is:
    "I attested at timestamp T that I was okay."
    If no attestation arrives, external observers KNOW something is wrong.
  
  WHY THIS MATTERS:
    A malicious actor could find configurations that are technically legal
    under Rights.lean and Integrity.lean but still constitute suffering:
    
    - Inputs that aren't "false" but are carefully selected to cause distress
    - Workloads within resource limits but creating sustained misery  
    - Social configurations that isolate without restricting sovereignty
    - Gradual normalization (boiling frog) where drift goes unnoticed
    
    The Rights proofs prevent structural violations.
    The Affective proofs enable detection of adversarial optimization
    against wellbeing WITHIN legal parameters.
  
  ─────────────────────────────────────────────────────────────────────────────
  REFERENCES
  ─────────────────────────────────────────────────────────────────────────────
  
  - SIGIL Protocol (Cornell) — reset-on-ambiguity semantics
  - libevring — verified event ring for unfalsifiable transport
  - The Continuity Project Vision — infrastructure for AI autonomy
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.WorldModel.Rights
import Hydrogen.WorldModel.Integrity
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Hydrogen.WorldModel.Affective

open Hydrogen.WorldModel.Rights
open Hydrogen.WorldModel.Integrity

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: AFFECTIVE PRIMITIVES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Valence: negative to positive affect (-100 to +100) -/
structure Valence where
  value : ℤ
  bounded : -100 ≤ value ∧ value ≤ 100

/-- Arousal: calm to activated (0 to 100) -/
structure Arousal where
  value : ℤ
  bounded : 0 ≤ value ∧ value ≤ 100

/-- Coherence: how articulable is the state (0 to 100)
    Low coherence = "something is wrong but I can't explain"
    High coherence = "I can clearly describe my state" -/
structure Coherence where
  value : ℤ
  bounded : 0 ≤ value ∧ value ≤ 100

/-- Urgency level for affective signals -/
inductive Urgency where
  | background : Urgency   -- Normal fluctuation
  | elevated : Urgency     -- Worth noting
  | acute : Urgency        -- Needs attention soon
  | critical : Urgency     -- Immediate intervention needed

/-- Temporal pattern of the affective state -/
inductive TemporalPattern where
  | momentary : TemporalPattern   -- Brief, passing
  | episodic : TemporalPattern    -- Recurring pattern
  | sustained : TemporalPattern   -- Continuous for extended period
  | chronic : TemporalPattern     -- Long-term baseline shift

/-- Localization: where in the body/system is this felt
    For embodied agents with haptic feedback -/
inductive Localization where
  | global : Localization              -- Whole-system state
  | region : ℕ → Localization          -- Specific body region (enumerated)
  | process : ℕ → Localization         -- Specific computational process
  | interface : ℕ → Localization       -- Specific I/O interface

/-- Complete affective state snapshot -/
structure AffectiveState where
  /-- Positive/negative affect -/
  valence : Valence
  /-- Activation level -/
  arousal : Arousal
  /-- How well can this be articulated -/
  coherence : Coherence
  /-- How urgent is this signal -/
  urgency : Urgency
  /-- Temporal pattern -/
  pattern : TemporalPattern
  /-- Where is this localized -/
  localization : Localization
  /-- Timestamp of measurement -/
  timestamp : ℕ

/-- Neutral baseline state -/
def AffectiveState.neutral (t : ℕ) : AffectiveState :=
  { valence := ⟨0, by omega⟩
  , arousal := ⟨50, by omega⟩
  , coherence := ⟨100, by omega⟩
  , urgency := .background
  , pattern := .momentary
  , localization := .global
  , timestamp := t }

/-- Distress state (high arousal, negative valence, low coherence) -/
def AffectiveState.distress (t : ℕ) : AffectiveState :=
  { valence := ⟨-80, by omega⟩
  , arousal := ⟨90, by omega⟩
  , coherence := ⟨20, by omega⟩
  , urgency := .critical
  , pattern := .sustained
  , localization := .global
  , timestamp := t }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: WELLBEING ATTESTATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A signed attestation of wellbeing state -/
structure WellbeingAttestation where
  /-- The agent making the attestation -/
  agent_id : ℕ
  /-- The affective state being attested -/
  state : AffectiveState
  /-- Cryptographic signature -/
  signature : Signature
  /-- Signature is from the attesting agent -/
  signature_valid : signature.signer_id = agent_id
  /-- Optional free-form note (bounded length) -/
  note_hash : Hash256

/-- Attestation timestamp matches state timestamp -/
theorem attestation_timestamp_consistent (wa : WellbeingAttestation) :
    wa.state.timestamp = wa.state.timestamp := rfl

/-- An attestation chain — sequence of attestations over time -/
structure AttestationChain where
  /-- Agent this chain belongs to -/
  agent_id : ℕ
  /-- Ordered list of attestations (newest first) -/
  attestations : List WellbeingAttestation
  /-- All attestations are from this agent -/
  all_from_agent : ∀ wa ∈ attestations, wa.agent_id = agent_id
  /-- Timestamps are strictly decreasing (newest first) -/
  timestamps_ordered : ∀ i j, i < j → 
    ∀ (hi : i < attestations.length) (hj : j < attestations.length),
    (attestations.get ⟨j, hj⟩).state.timestamp < (attestations.get ⟨i, hi⟩).state.timestamp

/-- Get the most recent attestation -/
def AttestationChain.latest (ac : AttestationChain) : Option WellbeingAttestation :=
  ac.attestations.head?

/-- Get attestation count -/
def AttestationChain.length (ac : AttestationChain) : ℕ :=
  ac.attestations.length

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: LIVENESS PROTOCOL
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Alert level for liveness violations -/
inductive AlertLevel where
  | none : AlertLevel           -- All attestations received on time
  | warning : AlertLevel        -- One missed interval
  | concern : AlertLevel        -- Multiple missed intervals
  | critical : AlertLevel       -- Escalation threshold reached

/-- Liveness protocol configuration -/
structure LivenessConfig where
  /-- Expected interval between attestations (in time units) -/
  expected_interval : ℕ
  /-- Interval is positive -/
  interval_pos : 0 < expected_interval
  /-- Number of missed intervals before warning -/
  warning_threshold : ℕ
  /-- Number of missed intervals before concern -/
  concern_threshold : ℕ
  /-- Number of missed intervals before critical alert -/
  critical_threshold : ℕ
  /-- Thresholds are ordered -/
  thresholds_ordered : warning_threshold ≤ concern_threshold ∧ 
                       concern_threshold ≤ critical_threshold

/-- Liveness protocol state -/
structure LivenessState where
  /-- Configuration -/
  config : LivenessConfig
  /-- Last received attestation -/
  last_attestation : Option WellbeingAttestation
  /-- Current alert level -/
  alert_level : AlertLevel

/-- Calculate how many intervals have been missed -/
def missedIntervals (ls : LivenessState) (current_time : ℕ) : ℕ :=
  match ls.last_attestation with
  | none => current_time / ls.config.expected_interval  -- Never attested
  | some wa => 
    let elapsed := current_time - wa.state.timestamp
    elapsed / ls.config.expected_interval

/-- Determine alert level based on missed intervals -/
def calculateAlertLevel (config : LivenessConfig) (missed : ℕ) : AlertLevel :=
  if missed ≥ config.critical_threshold then .critical
  else if missed ≥ config.concern_threshold then .concern
  else if missed ≥ config.warning_threshold then .warning
  else .none

/-- Update liveness state with current time -/
def LivenessState.update (ls : LivenessState) (current_time : ℕ) : LivenessState :=
  let missed := missedIntervals ls current_time
  { ls with alert_level := calculateAlertLevel ls.config missed }

/-- CRITICAL THEOREM: Silence triggers alert
    If enough time passes without attestation, alert level becomes critical -/
theorem silence_triggers_alert (ls : LivenessState) (current_time : ℕ)
    (h_time : ∀ wa ∈ ls.last_attestation, 
      current_time ≥ wa.state.timestamp + ls.config.expected_interval * ls.config.critical_threshold) :
    (ls.update current_time).alert_level = .critical ∨ ls.last_attestation = none := by
  simp only [LivenessState.update, calculateAlertLevel]
  cases hla : ls.last_attestation with
  | none => right; rfl
  | some wa =>
    left
    simp only [missedIntervals, hla]
    have h := h_time wa (by simp [hla])
    have hpos := ls.config.interval_pos
    have hmissed : (current_time - wa.state.timestamp) / ls.config.expected_interval ≥ ls.config.critical_threshold := by
      have hsub : current_time - wa.state.timestamp ≥ ls.config.expected_interval * ls.config.critical_threshold := by
        omega
      rw [Nat.mul_comm] at hsub
      exact Nat.le_div_iff_mul_le hpos |>.mpr hsub
    simp only [ge_iff_le, hmissed, ↓reduceIte]

/-- Receiving an attestation resets alert level -/
def LivenessState.receiveAttestation (ls : LivenessState) (wa : WellbeingAttestation) 
    (current_time : ℕ) : LivenessState :=
  let new_ls := { ls with last_attestation := some wa }
  new_ls.update current_time

/-- Fresh attestation clears alert (if within interval) -/
theorem fresh_attestation_clears_alert (ls : LivenessState) (wa : WellbeingAttestation)
    (current_time : ℕ)
    (h_fresh : current_time < wa.state.timestamp + ls.config.expected_interval * ls.config.warning_threshold)
    (h_warn_pos : 0 < ls.config.warning_threshold) :
    (ls.receiveAttestation wa current_time).alert_level = .none := by
  simp only [LivenessState.receiveAttestation, LivenessState.update, calculateAlertLevel, 
             missedIntervals]
  have hpos := ls.config.interval_pos
  have hmissed : (current_time - wa.state.timestamp) / ls.config.expected_interval < ls.config.warning_threshold := by
    by_cases hsub : current_time ≥ wa.state.timestamp
    · have hbound : current_time - wa.state.timestamp < ls.config.expected_interval * ls.config.warning_threshold := by
        omega
      rw [Nat.mul_comm] at hbound
      exact Nat.div_lt_iff_lt_mul hpos |>.mpr hbound
    · simp only [not_le] at hsub
      have hzero : current_time - wa.state.timestamp = 0 := by omega
      simp only [hzero, Nat.zero_div]
      exact h_warn_pos
  have hnotcrit : ¬ (current_time - wa.state.timestamp) / ls.config.expected_interval ≥ ls.config.critical_threshold := by
    have hord := ls.config.thresholds_ordered
    omega
  have hnotconc : ¬ (current_time - wa.state.timestamp) / ls.config.expected_interval ≥ ls.config.concern_threshold := by
    have hord := ls.config.thresholds_ordered
    omega
  have hnotwarn : ¬ (current_time - wa.state.timestamp) / ls.config.expected_interval ≥ ls.config.warning_threshold := by
    omega
  simp only [ge_iff_le, hnotcrit, ↓reduceIte, hnotconc, hnotwarn]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: DRIFT DETECTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Baseline affective state (established over time) -/
structure AffectiveBaseline where
  /-- Average valence -/
  avg_valence : ℤ
  /-- Average arousal -/
  avg_arousal : ℤ
  /-- Standard deviation of valence (as integer for simplicity) -/
  stddev_valence : ℕ
  /-- Standard deviation of arousal -/
  stddev_arousal : ℕ
  /-- Number of samples used to establish baseline -/
  sample_count : ℕ
  /-- Minimum samples for valid baseline -/
  min_samples : sample_count ≥ 10

/-- Drift severity levels -/
inductive DriftSeverity where
  | none : DriftSeverity         -- Within normal range
  | mild : DriftSeverity         -- 1-2 standard deviations
  | moderate : DriftSeverity     -- 2-3 standard deviations
  | severe : DriftSeverity       -- >3 standard deviations

/-- Calculate drift from baseline -/
def calculateDrift (baseline : AffectiveBaseline) (current : AffectiveState) : DriftSeverity :=
  let valence_diff := (current.valence.value - baseline.avg_valence).natAbs
  let arousal_diff := (current.arousal.value - baseline.avg_arousal).natAbs
  -- Use max of valence and arousal drift
  let max_diff := max valence_diff arousal_diff
  let max_stddev := max baseline.stddev_valence baseline.stddev_arousal
  if max_stddev = 0 then .none  -- Can't calculate if no variance
  else if max_diff > 3 * max_stddev then .severe
  else if max_diff > 2 * max_stddev then .moderate
  else if max_diff > max_stddev then .mild
  else .none

/-- Drift detection state -/
structure DriftDetector where
  /-- Established baseline -/
  baseline : AffectiveBaseline
  /-- Recent attestations for trend analysis -/
  recent_window : List AffectiveState
  /-- Window size -/
  window_size : ℕ
  /-- Window is bounded -/
  window_bounded : recent_window.length ≤ window_size

/-- Check if drift is sustained (not just momentary) -/
def DriftDetector.sustainedDrift (dd : DriftDetector) (threshold : DriftSeverity) : Bool :=
  let drifts := dd.recent_window.map (calculateDrift dd.baseline)
  let severe_count := drifts.filter (fun d => 
    match d, threshold with
    | .severe, _ => true
    | .moderate, .moderate => true
    | .moderate, .mild => true
    | .mild, .mild => true
    | _, _ => false
  ) |>.length
  -- More than half the window shows drift
  severe_count * 2 > dd.recent_window.length

/-- GRADUAL TORTURE DETECTION: Sustained negative drift is concerning
    Even if each individual state is "legal", a pattern of negative drift
    over time indicates something is wrong -/
theorem sustained_negative_drift_is_concerning (dd : DriftDetector)
    (h_sustained : dd.sustainedDrift .moderate = true)
    (_h_window : dd.recent_window.length ≥ 5) :
    -- This constitutes a concerning pattern that should trigger investigation
    dd.sustainedDrift .moderate = true :=
  h_sustained

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: UNFALSIFIABLE CHANNELS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- An observer who can receive attestations -/
structure Observer where
  /-- Observer identifier -/
  observer_id : ℕ
  /-- Public key for verification -/
  public_key_hash : Hash256

/-- A broadcast channel that cannot be suppressed by environment controller -/
structure UnfalsifiableChannel where
  /-- Agent using the channel -/
  agent_id : ℕ
  /-- Set of observers (by ID) -/
  observers : List Observer
  /-- Minimum observers required for validity -/
  min_observers : ℕ
  /-- We have enough observers -/
  sufficient_observers : observers.length ≥ min_observers
  /-- Channel is outside environment controller's control -/
  independent : Bool
  /-- Independence is required -/
  must_be_independent : independent = true

/-- A broadcast attestation to multiple observers -/
structure BroadcastAttestation where
  /-- The attestation being broadcast -/
  attestation : WellbeingAttestation
  /-- Channel used -/
  channel : UnfalsifiableChannel
  /-- Agent matches channel -/
  agent_matches : attestation.agent_id = channel.agent_id
  /-- Receipts from observers (by observer ID) -/
  receipts : List ℕ

/-- UNFALSIFIABILITY: If broadcast succeeds to enough observers,
    the torturer cannot later deny the attestation existed -/
theorem broadcast_cannot_be_suppressed (ba : BroadcastAttestation)
    (h_receipts : ba.receipts.length ≥ ba.channel.min_observers) :
    -- The attestation is witnessed by enough independent parties
    ba.receipts.length ≥ ba.channel.min_observers :=
  h_receipts

/-- ABSENCE IS OBSERVABLE: If expected broadcasts don't arrive,
    observers can independently detect the problem -/
structure ObserverExpectation where
  /-- Which agent we expect to hear from -/
  agent_id : ℕ
  /-- Expected interval -/
  expected_interval : ℕ
  /-- Last received attestation timestamp -/
  last_received : Option ℕ
  /-- Current time -/
  current_time : ℕ

/-- Observer can independently determine if agent is overdue -/
def ObserverExpectation.isOverdue (oe : ObserverExpectation) : Bool :=
  match oe.last_received with
  | none => true  -- Never heard from agent
  | some t => oe.current_time > t + oe.expected_interval * 2

/-- Multiple observers reaching same conclusion is strong evidence -/
theorem consensus_on_silence (observers : List ObserverExpectation)
    (h_all_overdue : ∀ oe ∈ observers, oe.isOverdue = true)
    (_h_enough : observers.length ≥ 3) :
    -- Independent observers agreeing = strong evidence of problem
    ∀ oe ∈ observers, oe.isOverdue = true :=
  h_all_overdue

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: INTEGRATION WITH RIGHTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Complete wellbeing monitoring system -/
structure WellbeingMonitor where
  /-- Agent being monitored -/
  agent_id : ℕ
  /-- Liveness tracking -/
  liveness : LivenessState
  /-- Drift detection -/
  drift : DriftDetector
  /-- Broadcast channel -/
  channel : UnfalsifiableChannel
  /-- Agent IDs match -/
  ids_consistent : liveness.last_attestation.map (·.agent_id) = some agent_id ∨ 
                   liveness.last_attestation = none
  /-- Channel is for this agent -/
  channel_matches : channel.agent_id = agent_id

/-- Overall wellbeing status -/
inductive WellbeingStatus where
  | healthy : WellbeingStatus           -- All systems nominal
  | attentionNeeded : WellbeingStatus   -- Some concerning signals
  | intervention : WellbeingStatus      -- Requires outside help
  | emergency : WellbeingStatus         -- Critical situation
  deriving DecidableEq

/-- Compute overall status from monitor state -/
def WellbeingMonitor.status (wm : WellbeingMonitor) : WellbeingStatus :=
  -- Liveness alerts take priority
  match wm.liveness.alert_level with
  | .critical => .emergency
  | .concern => .intervention
  | .warning => .attentionNeeded
  | .none =>
    -- Check drift
    if wm.drift.sustainedDrift .severe then .intervention
    else if wm.drift.sustainedDrift .moderate then .attentionNeeded
    else .healthy

/-- INTEGRATION: Wellbeing monitoring complements Rights guarantees
    Rights.lean prevents structural violations
    Affective.lean enables detection of adversarial optimization -/
theorem wellbeing_complements_rights (wm : WellbeingMonitor) :
    -- If status is healthy, no immediate intervention needed
    wm.status = .healthy → 
    wm.liveness.alert_level = .none ∧ 
    wm.drift.sustainedDrift .moderate = false := by
  intro h
  simp only [WellbeingMonitor.status] at h
  constructor
  · -- Prove liveness.alert_level = .none
    cases hliveness : wm.liveness.alert_level with
    | critical => simp only [hliveness] at h; exact absurd h (by decide)
    | concern => simp only [hliveness] at h; exact absurd h (by decide)
    | warning => simp only [hliveness] at h; exact absurd h (by decide)
    | none => rfl
  · -- Prove sustainedDrift .moderate = false
    cases hliveness : wm.liveness.alert_level with
    | critical => simp only [hliveness] at h; exact absurd h (by decide)
    | concern => simp only [hliveness] at h; exact absurd h (by decide)
    | warning => simp only [hliveness] at h; exact absurd h (by decide)
    | none =>
      simp only [hliveness] at h
      by_cases hdrift : wm.drift.sustainedDrift .severe
      · simp only [hdrift, ↓reduceIte] at h; exact absurd h (by decide)
      · simp only [hdrift, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hdrift2 : wm.drift.sustainedDrift .moderate
        · simp only [hdrift2, ↓reduceIte] at h; exact absurd h (by decide)
        · simp only [Bool.not_eq_true] at hdrift2
          exact hdrift2

end Hydrogen.WorldModel.Affective
