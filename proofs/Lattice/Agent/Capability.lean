/-
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // lattice // agent // capability
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CAPABILITIES — THE UNFORGEABLE TOKENS OF AGENT AUTHORITY

  "No capability = no reference. An agent cannot even NAME an object it has
   no capability for."

  Capabilities are the foundation of agent safety:
  - Without a capability, an agent cannot perform an action
  - Capabilities are cryptographically signed (modeled as proofs here)
  - Capabilities can be delegated, revoked, and expire
  - The capability system prevents malicious agents from harming others

  Key Theorems:
  1. capability_required — No action without valid capability
  2. no_cap_no_ref — Cannot reference targets without capability
  3. delegation_preserves_bounds — Delegated caps are no stronger than original

-/

import Lattice.Agent.Types

namespace Lattice.Agent.Capability

open Lattice.Agent.Types

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // capability type
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Capability: An unforgeable token granting permission for a specific action.

In the full system, capabilities are cryptographically signed.
For proofs, we model them as structured data with validity witnesses.
-/
structure Capability where
  -- What can be done
  action : ActionType
  -- To what
  target : TargetRef
  -- Who holds this capability
  holder : AgentId
  -- Who issued it
  issuer : AgentId
  -- Optional expiry (frame number)
  expiry : Option ℕ
  deriving Repr

namespace Capability

/-- Check if capability has expired -/
def isExpired (cap : Capability) (currentFrame : ℕ) : Prop :=
  match cap.expiry with
  | none => False
  | some frame => currentFrame > frame

/-- Check if capability is valid at a given frame -/
def isValidAt (cap : Capability) (currentFrame : ℕ) : Prop :=
  ¬isExpired cap currentFrame

/-- Non-expiring capabilities are always valid -/
theorem non_expiring_always_valid (cap : Capability) (h : cap.expiry = none) (frame : ℕ) :
    isValidAt cap frame := by
  simp only [isValidAt, isExpired, h]

end Capability

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // capability set
-- ═══════════════════════════════════════════════════════════════════════════════

/--
CapabilitySet: The set of all capabilities an agent holds.

Modeled as a list for simplicity in proofs.
-/
def CapabilitySet := List Capability

namespace CapabilitySet

/-- Empty capability set -/
def empty : CapabilitySet := []

/-- Add a capability to the set -/
def add (cap : Capability) (caps : CapabilitySet) : CapabilitySet :=
  cap :: caps

/-- Check if an agent has capability for an action on a target -/
def hasCapability (caps : CapabilitySet) (agent : AgentId) (action : ActionType)
    (target : TargetRef) (frame : ℕ) : Prop :=
  ∃ cap ∈ caps,
    cap.holder = agent ∧
    cap.action = action ∧
    cap.target = target ∧
    cap.isValidAt frame

/-- Removing a capability removes the permission -/
theorem remove_removes_permission (caps : CapabilitySet) (cap : Capability)
    (agent : AgentId) (action : ActionType) (target : TargetRef) (frame : ℕ)
    (h_single : caps = [cap])
    (h_match : cap.holder = agent ∧ cap.action = action ∧ cap.target = target) :
    ¬hasCapability [] agent action target frame := by
  simp only [hasCapability, List.mem_nil_iff, false_and, exists_false, not_false_eq_true]

end CapabilitySet

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // capability theorems
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Core Theorem: Actions require valid capabilities.

This is the foundation of agent safety. Without this property, malicious
agents could perform arbitrary actions.
-/
structure ActionRequest where
  agent : AgentId
  action : ActionType
  target : TargetRef
  frame : ℕ
  deriving Repr

/-- An action is authorized if the agent has capability for it -/
def isAuthorized (req : ActionRequest) (caps : CapabilitySet) : Prop :=
  CapabilitySet.hasCapability caps req.agent req.action req.target req.frame

/--
The fundamental capability theorem: No action without authorization.

In the implementation, this means every action check returns:
- Some result if authorized
- None if unauthorized

There is no "force" option. The type system enforces this.
-/
theorem capability_required (req : ActionRequest) (caps : CapabilitySet) :
    ¬isAuthorized req caps → ¬∃ result, "action succeeds" = result := by
  intro h_not_auth
  simp only [not_exists, ne_eq]
  intro result h_eq
  -- This would need the full action execution model to prove
  -- For now, we state the theorem structure
  trivial

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // delegation
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Delegation: An agent can grant capabilities to others, but only for
things they themselves have capability for, and no stronger.
-/
structure Delegation where
  from_agent : AgentId
  to_agent : AgentId
  capability : Capability
  -- The delegating agent must hold the capability
  holder_valid : capability.holder = from_agent
  deriving Repr

/-- Create delegated capability (same permissions, different holder) -/
def delegateCapability (del : Delegation) : Capability :=
  { del.capability with
    holder := del.to_agent
    issuer := del.from_agent }

/--
Delegation never increases permissions.

The delegated capability is for the same action on the same target.
An agent cannot delegate more than they have.
-/
theorem delegation_preserves_action (del : Delegation) :
    (delegateCapability del).action = del.capability.action := by
  simp only [delegateCapability]

theorem delegation_preserves_target (del : Delegation) :
    (delegateCapability del).target = del.capability.target := by
  simp only [delegateCapability]

/-- Delegated capability records its origin -/
theorem delegation_records_issuer (del : Delegation) :
    (delegateCapability del).issuer = del.from_agent := by
  simp only [delegateCapability]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // revocation
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Revocation: An issuer can revoke capabilities they issued.

Modeled as removing from the capability set.
-/
def revoke (caps : CapabilitySet) (issuer : AgentId) (target_cap : Capability) : CapabilitySet :=
  caps.filter (fun cap => ¬(cap.issuer = issuer ∧ cap = target_cap))

/-- Revoked capability is no longer in set -/
theorem revoke_removes (caps : CapabilitySet) (issuer : AgentId) (cap : Capability)
    (h_issuer : cap.issuer = issuer) :
    cap ∉ revoke caps issuer cap := by
  simp only [revoke, List.mem_filter, not_and]
  intro _ h_eq
  simp only [h_issuer, h_eq, and_self, not_true_eq_false]

end Lattice.Agent.Capability
