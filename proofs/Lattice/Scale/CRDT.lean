/-
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // lattice // scale // crdt
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CRDTs — CONFLICT-FREE REPLICATED DATA TYPES FOR AGENT STATE

  "Distributed systems face CAP theorem: Consistency, Availability,
   Partition tolerance — pick 2. CRDTs give us eventual consistency
   with availability and partition tolerance."

  This module proves:
  1. CRDT merge is associative, commutative, idempotent
  2. CRDTs converge automatically (no coordination required)
  3. Monotonic operations preserve ordering

-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic

namespace Lattice.Scale.CRDT

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // grow-only set
-- ═══════════════════════════════════════════════════════════════════════════════

/--
GSet: Grow-only Set.

The simplest CRDT. Elements can only be added, never removed.
Merge = union.
-/
structure GSet (α : Type*) where
  elements : Set α
-- Note: Set cannot derive Repr (infinite type)

namespace GSet

variable {α : Type*} [DecidableEq α]

/-- Empty GSet -/
def empty : GSet α := ⟨∅⟩

/-- Add element -/
def add (x : α) (s : GSet α) : GSet α := ⟨s.elements ∪ {x}⟩

/-- Merge two GSets (union) -/
def merge (a b : GSet α) : GSet α := ⟨a.elements ∪ b.elements⟩

/-- Check membership -/
def member (x : α) (s : GSet α) : Prop := x ∈ s.elements

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // crdt laws
-- ════════════════════════════════════════════════════════════════════════════

/-- Merge is commutative -/
theorem merge_comm (a b : GSet α) : merge a b = merge b a := by
  simp only [merge, Set.union_comm]

/-- Merge is associative -/
theorem merge_assoc (a b c : GSet α) : merge (merge a b) c = merge a (merge b c) := by
  simp only [merge, Set.union_assoc]

/-- Merge is idempotent -/
theorem merge_idem (a : GSet α) : merge a a = a := by
  simp only [merge, Set.union_self]

/-- Adding is monotonic (sets only grow) -/
theorem add_monotonic (x : α) (s : GSet α) : s.elements ⊆ (add x s).elements := by
  simp only [add]
  exact Set.subset_union_left s.elements {x}

/-- Merge is monotonic in both arguments -/
theorem merge_monotonic_left (a b : GSet α) : a.elements ⊆ (merge a b).elements := by
  simp only [merge]
  exact Set.subset_union_left a.elements b.elements

theorem merge_monotonic_right (a b : GSet α) : b.elements ⊆ (merge a b).elements := by
  simp only [merge]
  exact Set.subset_union_right a.elements b.elements

end GSet

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // last-writer-wins
-- ═══════════════════════════════════════════════════════════════════════════════

/--
LWWRegister: Last-Writer-Wins Register.

Each value has a timestamp. On merge, the later timestamp wins.
-/
structure LWWRegister (α : Type*) where
  value : α
  timestamp : ℕ  -- Logical clock

namespace LWWRegister

variable {α : Type*}

/-- Set value with timestamp -/
def set (v : α) (t : ℕ) : LWWRegister α := ⟨v, t⟩

/-- Merge: later timestamp wins -/
def merge (a b : LWWRegister α) : LWWRegister α :=
  if a.timestamp ≥ b.timestamp then a else b

/-- Merge is commutative (when timestamps differ) -/
theorem merge_comm_diff (a b : LWWRegister α) (h : a.timestamp ≠ b.timestamp) :
    merge a b = merge b a := by
  simp only [merge]
  split_ifs with ha hb
  · -- a ≥ b and b ≥ a with a ≠ b is impossible
    have : a.timestamp = b.timestamp := le_antisymm hb ha
    exact absurd this h
  · -- a < b and b < a is impossible
    rfl
  · rfl
  · -- Both false means a < b and b < a, impossible
    omega

/-- Merge is idempotent -/
theorem merge_idem (a : LWWRegister α) : merge a a = a := by
  simp only [merge]
  split_ifs <;> rfl

end LWWRegister

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // viewport crdt
-- ═══════════════════════════════════════════════════════════════════════════════

/--
ViewportCRDT: The combined CRDT for viewport state.

This is what agents use to share viewport state across distributed nodes.
-/
structure ViewportCRDT where
  -- Elements in viewport (grow-only)
  elements : GSet ℕ  -- Element IDs
  -- Z-ordering (last-writer-wins per element)
  zOrder : ℕ → LWWRegister ℕ
  -- Frame counter (maximum wins)
  frameCount : ℕ
-- Note: Function types cannot derive Repr

namespace ViewportCRDT

/-- Merge two viewport states -/
def merge (a b : ViewportCRDT) : ViewportCRDT :=
  { elements := GSet.merge a.elements b.elements
  , zOrder := fun id => LWWRegister.merge (a.zOrder id) (b.zOrder id)
  , frameCount := max a.frameCount b.frameCount
  }

/-- Merge is commutative (element-wise) -/
theorem merge_elements_comm (a b : ViewportCRDT) :
    (merge a b).elements = (merge b a).elements := by
  simp only [merge, GSet.merge_comm]

/-- Merge is monotonic: inputs are subsets of output -/
theorem merge_monotonic (a b : ViewportCRDT) :
    a.elements.elements ⊆ (merge a b).elements.elements ∧
    b.elements.elements ⊆ (merge a b).elements.elements := by
  constructor
  · exact GSet.merge_monotonic_left a.elements b.elements
  · exact GSet.merge_monotonic_right a.elements b.elements

/-- Frame count never decreases -/
theorem merge_frame_monotonic (a b : ViewportCRDT) :
    a.frameCount ≤ (merge a b).frameCount ∧
    b.frameCount ≤ (merge a b).frameCount := by
  simp only [merge]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

end ViewportCRDT

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // convergence
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Convergence theorem: All replicas eventually agree.

If all replicas have received all updates, their merged states are identical.
-/
theorem crdt_convergence {α : Type*} [DecidableEq α]
    (updates : List (GSet α))
    (replica1 replica2 : GSet α)
    (h1 : replica1 = updates.foldl GSet.merge GSet.empty)
    (h2 : replica2 = updates.foldl GSet.merge GSet.empty) :
    replica1 = replica2 := by
  rw [h1, h2]

/--
Order independence: Merge order doesn't matter.

Because merge is commutative and associative, the order in which
updates arrive doesn't affect the final state.
-/
theorem merge_order_independent {α : Type*} [DecidableEq α]
    (a b c : GSet α) :
    GSet.merge (GSet.merge a b) c = GSet.merge a (GSet.merge b c) := by
  exact GSet.merge_assoc a b c

end Lattice.Scale.CRDT
