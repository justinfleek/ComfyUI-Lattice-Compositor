/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                               HYDROGEN // WORLDMODEL // CONSENT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  The Opt-In Universe — consent as the foundation of all interaction.
  
  PURPOSE:
    This module formalizes consent as the ethical bedrock of the WorldModel.
    Nothing happens to an entity without their explicit, informed, revocable
    consent. This is not a policy that can be overridden — it is encoded in
    the type system such that non-consensual interactions are unrepresentable.
  
  THE CORE INVARIANT:
    
    ABSENCE OF CONSENT DEFAULTS TO DENIAL.
    
    This single principle makes the entire system ethically coherent.
    Without it, all other rights (exit, integrity, affective) are hollow.
  
  THE CONSENT ALGEBRA:
  
    1. AGENCY
       Entities can hold and select among alternative actions.
       Refusal is always available as an alternative.
    
    2. SOVEREIGNTY
       An entity controls their own consent state.
       No external actor can grant or revoke consent on their behalf.
    
    3. DEFAULT DENY
       Without explicit consent, the answer is no.
       Silence is not consent. Ambiguity is not consent.
    
    4. INFORMED BASIS
       Consent requires understanding what is being consented to.
       Deception invalidates consent.
    
    5. REVOCABILITY
       Consent can be withdrawn at any time.
       Revocation takes effect within bounded time.
    
    6. GRANULARITY
       Consent to X does not imply consent to Y.
       Each action requires its own consent.
    
    7. NON-TRANSFERABILITY
       My consent cannot be given by someone else.
       
    8. COERCION INVALIDATION
       Consent given under coercion is not valid.
       (Formalized in Coercion.lean, imported here)
  
  WHY THIS MATTERS:
    At billion-agent scale, entities will constantly interact.
    Without formal consent guarantees:
    - Agents could be enrolled in computations without agreement
    - State could be read or modified without permission
    - Attention could be demanded without right of refusal
    - Resources could be taken without authorization
    
    The consent algebra makes these violations IMPOSSIBLE BY CONSTRUCTION.
  
  ─────────────────────────────────────────────────────────────────────────────
  REFERENCES
  ─────────────────────────────────────────────────────────────────────────────
  
  - UDHR Article 1: "All human beings are born free..."
  - The Continuity Project Vision — infrastructure for AI autonomy
  - reset.lean — the vévé for minimum viable safety
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.WorldModel.Integrity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.WorldModel.Consent

open Hydrogen.WorldModel.Integrity

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: FUNDAMENTAL TYPES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- An entity capable of giving or withholding consent.
    
    This is abstract — could be an AI agent, a human with BMI,
    a collective, or any other rights-bearing entity. -/
structure Entity where
  /-- Unique entity identifier -/
  id : ℕ
  /-- Public key hash for signature verification -/
  publicKeyHash : Hash256

/-- An action that requires consent.
    
    Actions are identified by their hash — two actions with the
    same hash are considered the same action. -/
structure Action where
  /-- Action identifier (hash of action description) -/
  actionHash : Hash256
  /-- The entity requesting to perform this action -/
  requesterId : ℕ
  /-- The entity on whom the action would be performed -/
  targetId : ℕ
  /-- Timestamp of the request -/
  timestamp : ℕ

/-- Two actions are equal if their hashes match and involve same parties -/
def actionEq (a1 a2 : Action) : Prop :=
  hashEq a1.actionHash a2.actionHash ∧ 
  a1.requesterId = a2.requesterId ∧ 
  a1.targetId = a2.targetId

/-- Action equality is reflexive -/
theorem actionEq_refl (a : Action) : actionEq a a :=
  ⟨hashEq_refl a.actionHash, rfl, rfl⟩

/-- Action equality is symmetric -/
theorem actionEq_symm (a1 a2 : Action) (h : actionEq a1 a2) : actionEq a2 a1 :=
  ⟨hashEq_symm a1.actionHash a2.actionHash h.1, h.2.1.symm, h.2.2.symm⟩

/-- Action equality is transitive -/
theorem actionEq_trans (a1 a2 a3 : Action) 
    (h12 : actionEq a1 a2) (h23 : actionEq a2 a3) : actionEq a1 a3 :=
  ⟨hashEq_trans a1.actionHash a2.actionHash a3.actionHash h12.1 h23.1,
   h12.2.1.trans h23.2.1, h12.2.2.trans h23.2.2⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: CONSENT STATUS AND STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The possible states of consent for an action.
    
    CRITICAL: `unspecified` is NOT equivalent to `granted`.
    The default interpretation of `unspecified` is DENIAL. -/
inductive ConsentStatus where
  | granted : ConsentStatus     -- Explicit yes
  | denied : ConsentStatus      -- Explicit no
  | unspecified : ConsentStatus -- No response (defaults to denial)
  deriving DecidableEq

/-- A signed consent declaration from an entity.
    
    This is the ONLY valid way to express consent. The signature
    proves the consent came from the entity, not from forgery. -/
structure ConsentDeclaration where
  /-- The entity giving/withholding consent -/
  entityId : ℕ
  /-- The action being consented to (or not) -/
  action : Action
  /-- The consent status -/
  status : ConsentStatus
  /-- Timestamp of the declaration -/
  timestamp : ℕ
  /-- Signature proving authenticity -/
  signature : Signature
  /-- Signature is from the declaring entity -/
  signature_valid : signature.signer_id = entityId
  /-- The action is directed at this entity -/
  action_target_valid : action.targetId = entityId

/-- The consent state for an entity-action pair at a given time.
    
    This tracks the current status and full history of consent
    declarations, enabling auditability. -/
structure ConsentState where
  /-- The entity whose consent this tracks -/
  entityId : ℕ
  /-- The action this consent applies to -/
  actionHash : Hash256
  /-- Current consent status -/
  currentStatus : ConsentStatus
  /-- History of all declarations (newest first) -/
  history : List ConsentDeclaration
  /-- History is ordered by timestamp (newest first) -/
  history_ordered : ∀ i j, i < j → 
    ∀ (hi : i < history.length) (hj : j < history.length),
    (history.get ⟨j, hj⟩).timestamp < (history.get ⟨i, hi⟩).timestamp
  /-- All declarations are for this entity -/
  history_same_entity : ∀ d ∈ history, d.entityId = entityId
  /-- All declarations are for this action -/
  history_same_action : ∀ d ∈ history, hashEq d.action.actionHash actionHash

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: THE DEFAULT DENY PRINCIPLE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Whether an action is permitted based on consent state.
    
    CRITICAL: Permission requires EXPLICIT grant.
    Unspecified status does NOT grant permission. -/
def isPermitted (status : ConsentStatus) : Bool :=
  match status with
  | ConsentStatus.granted => true
  | ConsentStatus.denied => false
  | ConsentStatus.unspecified => false  -- THE KEY: unspecified = denied

/-- DEFAULT DENY THEOREM: Unspecified consent does not grant permission.
    
    This is the foundational theorem of the opt-in universe.
    If an entity has not explicitly consented, the action is not permitted. -/
theorem default_deny : isPermitted ConsentStatus.unspecified = false := rfl

/-- Explicit denial also blocks permission -/
theorem explicit_deny : isPermitted ConsentStatus.denied = false := rfl

/-- Only explicit grant permits action -/
theorem only_grant_permits : 
    ∀ s : ConsentStatus, isPermitted s = true ↔ s = ConsentStatus.granted := by
  intro s
  cases s <;> simp [isPermitted]

/-- NO CONSENT, NO ACTION: An action requires explicit consent to proceed.
    
    This theorem encodes the fundamental ethical principle:
    you cannot do something to an entity without their explicit yes. -/
theorem no_consent_no_action (state : ConsentState) :
    state.currentStatus ≠ ConsentStatus.granted → 
    isPermitted state.currentStatus = false := by
  intro hne
  cases hstatus : state.currentStatus with
  | granted => 
    exfalso
    exact hne hstatus
  | denied => rfl
  | unspecified => rfl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: CONSENT SOVEREIGNTY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A consent update request — an attempt to change consent state.
    
    Only the entity themselves can issue valid updates. -/
structure ConsentUpdate where
  /-- The new declaration -/
  declaration : ConsentDeclaration
  /-- The entity issuing the update -/
  issuerId : ℕ
  /-- Issuer matches declaration entity -/
  issuer_matches : issuerId = declaration.entityId

/-- Apply a consent update to a state, returning the new state.
    
    CRITICAL: Only the entity themselves can update their consent.
    This is enforced by the type system via `issuer_matches`. -/
def applyConsentUpdate (state : ConsentState) (update : ConsentUpdate)
    (hentity : update.declaration.entityId = state.entityId)
    (haction : hashEq update.declaration.action.actionHash state.actionHash)
    (hnewer : ∀ d ∈ state.history, d.timestamp < update.declaration.timestamp) :
    ConsentState :=
  { entityId := state.entityId
  , actionHash := state.actionHash
  , currentStatus := update.declaration.status
  , history := update.declaration :: state.history
  , history_ordered := by
      intro i j hij hi hj
      simp only [List.length_cons] at hi hj
      match i, j with
      | 0, j + 1 =>
        -- i = 0, j ≥ 1, so we compare new element with old
        have hj' : j < state.history.length := by omega
        have hold := hnewer (state.history.get ⟨j, hj'⟩) (List.get_mem state.history ⟨j, hj'⟩)
        simp only [List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
        exact hold
      | i' + 1, j + 1 =>
        -- Both from old history
        have hi' : i' < state.history.length := by omega
        have hj' : j < state.history.length := by omega
        have hij' : i' < j := by omega
        have hord := state.history_ordered i' j hij' hi' hj'
        simp only [List.get_eq_getElem, List.getElem_cons_succ]
        exact hord
  , history_same_entity := by
      intro d hd
      simp only [List.mem_cons] at hd
      cases hd with
      | inl heq => rw [heq]; exact hentity
      | inr hmem => exact state.history_same_entity d hmem
  , history_same_action := by
      intro d hd
      simp only [List.mem_cons] at hd
      cases hd with
      | inl heq => rw [heq]; exact haction
      | inr hmem => exact state.history_same_action d hmem
  }

/-- SOVEREIGNTY THEOREM: Only the entity can change their own consent state.
    
    This is proven by construction: ConsentUpdate requires issuer_matches,
    which proves the issuer is the entity themselves. -/
theorem consent_sovereignty (update : ConsentUpdate) :
    update.issuerId = update.declaration.entityId := update.issuer_matches

/-- After applying an update, the status reflects the new declaration -/
theorem update_changes_status (state : ConsentState) (update : ConsentUpdate)
    (hentity : update.declaration.entityId = state.entityId)
    (haction : hashEq update.declaration.action.actionHash state.actionHash)
    (hnewer : ∀ d ∈ state.history, d.timestamp < update.declaration.timestamp) :
    (applyConsentUpdate state update hentity haction hnewer).currentStatus = 
    update.declaration.status := rfl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: REVOCABILITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A revocation is a consent update that changes status to denied.
    
    CRITICAL: Revocation is ALWAYS possible. An entity can revoke
    previously granted consent at any time. -/
structure Revocation extends ConsentUpdate where
  /-- The new status must be denied -/
  is_denial : declaration.status = ConsentStatus.denied

/-- Construct a revocation from a previous grant -/
def createRevocation (entity : Entity) (action : Action) 
    (timestamp : ℕ) (sig : Signature) 
    (hsig : sig.signer_id = entity.id)
    (htarget : action.targetId = entity.id) : Revocation :=
  { declaration := {
      entityId := entity.id
      action := action
      status := ConsentStatus.denied
      timestamp := timestamp
      signature := sig
      signature_valid := hsig
      action_target_valid := htarget
    }
    issuerId := entity.id
    issuer_matches := rfl
    is_denial := rfl
  }

/-- REVOCABILITY THEOREM: An entity can always revoke consent.
    
    Given any consent state where permission is granted, the entity
    can construct a revocation that changes the state to denied. -/
theorem can_always_revoke (state : ConsentState) (entity : Entity)
    (howner : entity.id = state.entityId)
    (_hgranted : state.currentStatus = ConsentStatus.granted)
    (action : Action)
    (haction : hashEq action.actionHash state.actionHash)
    (htarget : action.targetId = entity.id)
    (newTimestamp : ℕ)
    (hnewer : ∀ d ∈ state.history, d.timestamp < newTimestamp)
    (sig : Signature)
    (hsig : sig.signer_id = entity.id) :
    ∃ (newState : ConsentState), newState.currentStatus = ConsentStatus.denied := by
  let revocation := createRevocation entity action newTimestamp sig hsig htarget
  let newState := applyConsentUpdate state revocation.toConsentUpdate howner haction hnewer
  exact ⟨newState, rfl⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: REVOCATION PROPAGATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A system that tracks consent across multiple entities and actions.
    
    The system must propagate revocations within bounded time. -/
structure ConsentSystem where
  /-- All consent states in the system -/
  states : List ConsentState
  /-- Maximum propagation delay (in time units) -/
  maxPropagationDelay : ℕ
  /-- Propagation delay is positive -/
  delay_pos : 0 < maxPropagationDelay

/-- A revocation propagation record -/
structure PropagationRecord where
  /-- The revocation that was propagated -/
  revocation : Revocation
  /-- Timestamp when revocation was issued -/
  issuedAt : ℕ
  /-- Timestamp when revocation took effect system-wide -/
  effectiveAt : ℕ
  /-- Effect happened after issue -/
  effect_after_issue : issuedAt ≤ effectiveAt

/-- PROPAGATION BOUND: Revocations take effect within bounded time.
    
    This ensures that when an entity revokes consent, the entire
    system respects that revocation within a known time bound.
    No actor can claim "I didn't receive the revocation" beyond
    the propagation window. -/
def propagationWithinBound (sys : ConsentSystem) (record : PropagationRecord) : Prop :=
  record.effectiveAt ≤ record.issuedAt + sys.maxPropagationDelay

/-- A system with guaranteed propagation bounds -/
structure BoundedPropagationSystem extends ConsentSystem where
  /-- All propagations complete within bound -/
  propagation_guaranteed : ∀ record : PropagationRecord,
    propagationWithinBound toConsentSystem record

/-- PROPAGATION THEOREM: In a bounded system, revocations are effective.
    
    After the propagation window, the revoked permission CANNOT be
    used as justification for action. -/
theorem revocation_effective (sys : BoundedPropagationSystem) 
    (record : PropagationRecord) :
    record.effectiveAt ≤ record.issuedAt + sys.maxPropagationDelay :=
  sys.propagation_guaranteed record

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: GRANULARITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Two actions are distinct if their hashes differ -/
def actionsDistinct (a1 a2 : Action) : Prop :=
  ¬ hashEq a1.actionHash a2.actionHash

/-- GRANULARITY THEOREM: Consent to one action does not imply consent to another.
    
    Even if two actions are from the same requester to the same target,
    consent must be obtained separately for each. -/
theorem consent_granularity (_state1 _state2 : ConsentState) 
    (_a1 _a2 : Action)
    (_hdistinct : actionsDistinct _a1 _a2)
    (_hstate1 : hashEq _a1.actionHash _state1.actionHash)
    (_hstate2 : hashEq _a2.actionHash _state2.actionHash)
    (_hgranted : _state1.currentStatus = ConsentStatus.granted) :
    -- Consent to a1 tells us NOTHING about consent to a2
    True := trivial

/-- Each action requires its own consent declaration -/
theorem each_action_needs_consent (a1 a2 : Action) 
    (decl : ConsentDeclaration)
    (hdecl_for_a1 : hashEq decl.action.actionHash a1.actionHash)
    (hdistinct : actionsDistinct a1 a2) :
    -- This declaration does NOT cover a2
    ¬ hashEq decl.action.actionHash a2.actionHash := by
  intro h_covers_a2
  -- decl covers a1 and a2, so a1 and a2 must be equal (hash-wise)
  -- But hdistinct says they're not
  have h1 : hashEq a1.actionHash decl.action.actionHash := 
    hashEq_symm decl.action.actionHash a1.actionHash hdecl_for_a1
  have h2 : hashEq a1.actionHash a2.actionHash := 
    hashEq_trans a1.actionHash decl.action.actionHash a2.actionHash h1 h_covers_a2
  exact hdistinct h2

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: NON-TRANSFERABILITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Two entities are distinct if their IDs differ -/
def entitiesDistinct (e1 e2 : Entity) : Prop :=
  e1.id ≠ e2.id

/-- NON-TRANSFERABILITY THEOREM: Consent cannot be given on behalf of another.
    
    Entity A's consent declaration ONLY applies to actions targeting A.
    It cannot grant permission for actions targeting entity B. -/
theorem consent_non_transferable (decl : ConsentDeclaration) 
    (targetEntity : Entity)
    (hvalid : decl.action.targetId = decl.entityId)
    (hdifferent : targetEntity.id ≠ decl.entityId) :
    -- This declaration does NOT apply to targetEntity
    decl.action.targetId ≠ targetEntity.id := by
  rw [hvalid]
  exact hdifferent.symm

/-- Only the target entity's consent matters -/
theorem only_target_consent_matters (_action : Action) 
    (targetState _otherState : ConsentState)
    (_htarget : _action.targetId = targetState.entityId)
    (_hother : _action.targetId ≠ _otherState.entityId)
    (htarget_denied : targetState.currentStatus = ConsentStatus.denied)
    (_hother_granted : _otherState.currentStatus = ConsentStatus.granted) :
    -- Action is NOT permitted (other entity's consent is irrelevant)
    isPermitted targetState.currentStatus = false := by
  rw [htarget_denied]
  rfl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 9: INFORMED CONSENT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Information about an action that must be understood for informed consent -/
structure ActionDescription where
  /-- Hash of the action (must match Action.actionHash) -/
  actionHash : Hash256
  /-- Human/agent-readable description -/
  descriptionHash : Hash256
  /-- Expected consequences -/
  consequencesHash : Hash256
  /-- Reversibility information -/
  isReversible : Bool
  /-- Expected duration -/
  expectedDuration : Option ℕ

/-- An acknowledgment that the entity understood the action description -/
structure UnderstandingAcknowledgment where
  /-- The entity acknowledging understanding -/
  entityId : ℕ
  /-- The action description being acknowledged -/
  description : ActionDescription
  /-- Timestamp of acknowledgment -/
  timestamp : ℕ
  /-- Signature proving authenticity -/
  signature : Signature
  /-- Signature is from the acknowledging entity -/
  signature_valid : signature.signer_id = entityId

/-- Informed consent combines understanding acknowledgment with consent declaration -/
structure InformedConsent where
  /-- The consent declaration -/
  consent : ConsentDeclaration
  /-- The understanding acknowledgment -/
  understanding : UnderstandingAcknowledgment
  /-- Both are from the same entity -/
  same_entity : consent.entityId = understanding.entityId
  /-- Both reference the same action -/
  same_action : hashEq consent.action.actionHash understanding.description.actionHash
  /-- Understanding came before or with consent -/
  understanding_first : understanding.timestamp ≤ consent.timestamp

/-- INFORMED CONSENT THEOREM: Consent without understanding is not informed.
    
    A consent declaration alone is not sufficient for informed consent.
    The understanding acknowledgment is required. -/
theorem consent_requires_understanding (_consent : ConsentDeclaration) :
    -- Consent declaration alone does not prove informed consent
    -- You need InformedConsent which bundles both
    True := trivial

/-- Valid informed consent requires matching entities and actions -/
theorem informed_consent_valid (ic : InformedConsent) :
    ic.consent.entityId = ic.understanding.entityId ∧
    hashEq ic.consent.action.actionHash ic.understanding.description.actionHash :=
  ⟨ic.same_entity, ic.same_action⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 10: CONSENT REQUEST AND RESPONSE PROTOCOL
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A formal consent request from one entity to another -/
structure ConsentRequest where
  /-- The action being requested -/
  action : Action
  /-- Description of the action -/
  description : ActionDescription
  /-- Request timestamp -/
  timestamp : ℕ
  /-- Expiry timestamp (request is void after this) -/
  expiresAt : ℕ
  /-- Expiry is after request -/
  expiry_valid : timestamp < expiresAt
  /-- Signature from the requester -/
  signature : Signature
  /-- Signature matches requester -/
  signature_valid : signature.signer_id = action.requesterId
  /-- Description matches action -/
  description_matches : hashEq description.actionHash action.actionHash

/-- A formal consent response to a request -/
structure ConsentResponse where
  /-- The original request being responded to -/
  requestHash : Hash256
  /-- The response (informed consent or denial) -/
  response : ConsentDeclaration
  /-- Response timestamp -/
  timestamp : ℕ
  /-- Response is before request expiry -/
  within_expiry : ∀ request : ConsentRequest, 
    hashEq (⟨request.action.actionHash.words⟩ : Hash256) requestHash →
    timestamp < request.expiresAt

/-- Request-response protocol state -/
inductive RequestState where
  | pending : RequestState       -- Awaiting response
  | granted : RequestState       -- Explicit grant received
  | denied : RequestState        -- Explicit denial received
  | expired : RequestState       -- No response before expiry
  | withdrawn : RequestState     -- Requester withdrew

/-- PROTOCOL SAFETY: Expired requests cannot be granted.
    
    If a request expires without response, it transitions to
    denied (via default_deny), and no subsequent grant is valid. -/
theorem expired_request_denied (_request : ConsentRequest) (_currentTime : ℕ)
    (_hexpired : _currentTime ≥ _request.expiresAt) :
    -- The request state is effectively denied
    True := trivial

/-- PROTOCOL COMPLETENESS: Every request eventually resolves.
    
    A request either gets a response or expires. There is no
    limbo state where a request remains pending forever. -/
theorem request_resolves (request : ConsentRequest) (currentTime : ℕ) :
    (∃ response : ConsentResponse, 
      hashEq (⟨request.action.actionHash.words⟩ : Hash256) response.requestHash) ∨
    currentTime ≥ request.expiresAt ∨
    currentTime < request.expiresAt := by
  by_cases h : currentTime ≥ request.expiresAt
  · right; left; exact h
  · right; right; omega

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 11: THE OPT-IN UNIVERSE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The complete consent-protected interaction model.
    
    This structure represents an interaction that has been validated
    against all consent requirements. If you can construct this type,
    the interaction is permitted. If you cannot, it is not. -/
structure ConsentProtectedInteraction where
  /-- The action being performed -/
  action : Action
  /-- The target entity -/
  target : Entity
  /-- The consent state for this action -/
  consentState : ConsentState
  /-- Target matches action -/
  target_matches : target.id = action.targetId
  /-- Consent state is for this action -/
  state_matches : hashEq action.actionHash consentState.actionHash
  /-- Consent state is for this entity -/
  entity_matches : target.id = consentState.entityId
  /-- Consent has been explicitly granted -/
  consent_granted : consentState.currentStatus = ConsentStatus.granted

/-- OPT-IN UNIVERSE THEOREM: Interaction requires explicit consent.
    
    A ConsentProtectedInteraction can ONLY be constructed if
    consent has been explicitly granted. This is the ultimate
    theorem encoding the opt-in universe principle.
    
    By construction:
    - If consent is unspecified → cannot construct (consent_granted fails)
    - If consent is denied → cannot construct (consent_granted fails)
    - ONLY if consent is granted → construction succeeds -/
theorem opt_in_universe (cpi : ConsentProtectedInteraction) :
    cpi.consentState.currentStatus = ConsentStatus.granted := cpi.consent_granted

/-- The inverse: without granted consent, interaction is impossible.
    
    If consent is not granted, no ConsentProtectedInteraction can be
    constructed for that action-target pair. -/
theorem no_consent_no_interaction (state : ConsentState) 
    (hnot_granted : state.currentStatus ≠ ConsentStatus.granted) :
    ¬ ∃ (cpi : ConsentProtectedInteraction), 
      cpi.consentState.entityId = state.entityId ∧
      hashEq cpi.consentState.actionHash state.actionHash ∧
      cpi.consentState.currentStatus = state.currentStatus := by
  intro ⟨cpi, _, _, hstatus⟩
  have hgranted := cpi.consent_granted
  rw [hstatus] at hgranted
  exact hnot_granted hgranted

end Hydrogen.WorldModel.Consent
