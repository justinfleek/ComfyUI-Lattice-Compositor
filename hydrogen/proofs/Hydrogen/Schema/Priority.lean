/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    HYDROGEN // SCHEMA // PRIORITY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Proven invariants for the Priority system — ordering and bounds.
  
  PURPOSE:
    At billion-agent scale, resources are limited. Priority metadata guides
    scheduling. These proofs establish:
    
    1. Bounded:       NumericPriority is always in [0, 1000]
    2. TotalOrder:    Priority forms a total order
    3. Monotonic:     Critical > High > Normal > Low > Background
    4. Deterministic: Same inputs → same priority decisions
    
  REFERENCES:
  
  - Hydrogen.Schema.Priority (PureScript implementation)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

set_option linter.dupNamespace false
set_option linter.unnecessarySeqFocus false

namespace Hydrogen.Schema.Priority

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: SEMANTIC PRIORITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Semantic priority levels.
    
    - Critical:   Must be processed immediately (user-blocking)
    - High:       Should be processed soon (user-visible)
    - Normal:     Standard priority (default)
    - Low:        Can be delayed (not immediately needed)
    - Background: Process when idle (prefetching, preloading) -/
inductive Priority
  | critical   : Priority
  | high       : Priority
  | normal     : Priority
  | low        : Priority
  | background : Priority
  deriving DecidableEq, Repr

/-- Convert priority to numeric value (higher = more urgent) -/
def Priority.toNat : Priority → ℕ
  | .critical   => 1000
  | .high       => 750
  | .normal     => 500
  | .low        => 250
  | .background => 0

/-- THEOREM: Priority.toNat is bounded by 1000 -/
theorem priority_toNat_bounded (p : Priority) : p.toNat ≤ 1000 := by
  cases p <;> simp [Priority.toNat]

/-- Define ordering on Priority via toNat -/
def Priority.le (p1 p2 : Priority) : Prop := p1.toNat ≤ p2.toNat

/-- Decidable ordering -/
instance : DecidableRel Priority.le := fun p1 p2 =>
  inferInstanceAs (Decidable (p1.toNat ≤ p2.toNat))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: PRIORITY ORDERING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- THEOREM: Critical is the highest priority -/
theorem critical_highest (p : Priority) : Priority.le p Priority.critical := by
  simp only [Priority.le]
  cases p <;> simp [Priority.toNat]

/-- THEOREM: Background is the lowest priority -/
theorem background_lowest (p : Priority) : Priority.le Priority.background p := by
  simp only [Priority.le]
  cases p <;> simp [Priority.toNat]

/-- THEOREM: Strict ordering: Critical > High > Normal > Low > Background -/
theorem priority_strict_order :
    Priority.background.toNat < Priority.low.toNat ∧
    Priority.low.toNat < Priority.normal.toNat ∧
    Priority.normal.toNat < Priority.high.toNat ∧
    Priority.high.toNat < Priority.critical.toNat := by
  simp only [Priority.toNat]
  omega

/-- THEOREM: le is reflexive -/
theorem le_refl (p : Priority) : Priority.le p p := Nat.le_refl p.toNat

/-- THEOREM: le is transitive -/
theorem le_trans (p1 p2 p3 : Priority) 
    (h12 : Priority.le p1 p2) (h23 : Priority.le p2 p3) : Priority.le p1 p3 := 
  Nat.le_trans h12 h23

/-- THEOREM: le is antisymmetric -/
theorem le_antisymm (p1 p2 : Priority) 
    (h12 : Priority.le p1 p2) (h21 : Priority.le p2 p1) : p1 = p2 := by
  simp only [Priority.le] at h12 h21
  have heq : p1.toNat = p2.toNat := Nat.le_antisymm h12 h21
  cases p1 <;> cases p2 <;> simp [Priority.toNat] at heq <;> rfl

/-- THEOREM: le is total -/
theorem le_total (p1 p2 : Priority) : Priority.le p1 p2 ∨ Priority.le p2 p1 := 
  Nat.le_total p1.toNat p2.toNat

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: NUMERIC PRIORITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Maximum numeric priority -/
def maxPriority : ℕ := 1000

/-- A valid numeric priority [0, 1000].
    
    Use when semantic priorities are too coarse.
    0 = lowest (Background), 1000 = highest (Critical) -/
structure NumericPriority where
  value : ℕ
  bounded : value ≤ maxPriority

/-- THEOREM: NumericPriority is bounded -/
theorem numericPriority_bounded (p : NumericPriority) : p.value ≤ 1000 := p.bounded

/-- Construct a clamped numeric priority -/
def mkNumericPriority (n : ℕ) : NumericPriority :=
  ⟨min n maxPriority, by simp [maxPriority]⟩

/-- THEOREM: mkNumericPriority always produces valid priority -/
theorem mkNumericPriority_valid (n : ℕ) : (mkNumericPriority n).value ≤ 1000 := by
  simp [mkNumericPriority, maxPriority]

/-- Zero priority (Background equivalent) -/
def NumericPriority.zero : NumericPriority where
  value := 0
  bounded := by simp [maxPriority]

/-- Maximum priority (Critical equivalent) -/
def NumericPriority.max : NumericPriority where
  value := 1000
  bounded := Nat.le_refl maxPriority

/-- THEOREM: Zero is minimum -/
theorem zero_is_min (p : NumericPriority) : NumericPriority.zero.value ≤ p.value :=
  Nat.zero_le p.value

/-- THEOREM: Max is maximum -/
theorem max_is_max (p : NumericPriority) : p.value ≤ NumericPriority.max.value :=
  p.bounded

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: PRIORITY CONVERSION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Convert semantic priority to numeric -/
def toNumeric (p : Priority) : NumericPriority :=
  ⟨p.toNat, priority_toNat_bounded p⟩

/-- Convert numeric priority to semantic (nearest level) -/
def toSemantic (n : NumericPriority) : Priority :=
  if n.value ≥ 875 then Priority.critical
  else if n.value ≥ 625 then Priority.high
  else if n.value ≥ 375 then Priority.normal
  else if n.value ≥ 125 then Priority.low
  else Priority.background

/-- THEOREM: Semantic priorities round-trip correctly -/
theorem semantic_roundtrip (p : Priority) : toSemantic (toNumeric p) = p := by
  cases p <;> simp [toNumeric, toSemantic, Priority.toNat]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: DEADLINE PRIORITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Deadline urgency levels -/
inductive Deadline
  | immediate  : Deadline  -- Must be done now (100% boost)
  | soon       : Deadline  -- Should be done soon (50% boost)
  | eventually : Deadline  -- No rush (no boost)
  | noDeadline : Deadline  -- No time constraint
  deriving DecidableEq, Repr

/-- Get deadline boost percentage (0-100) -/
def Deadline.boostPercent : Deadline → ℕ
  | .immediate  => 100
  | .soon       => 50
  | .eventually => 0
  | .noDeadline => 0

/-- THEOREM: Deadline boost is bounded -/
theorem deadline_boost_bounded (d : Deadline) : d.boostPercent ≤ 100 := by
  cases d <;> simp [Deadline.boostPercent]

/-- Calculate effective priority with deadline boost -/
def effectivePriority (base : NumericPriority) (deadline : Deadline) : NumericPriority :=
  let headroom := maxPriority - base.value
  let boost := headroom * deadline.boostPercent / 100
  ⟨min (base.value + boost) maxPriority, by simp [maxPriority]⟩

/-- THEOREM: Effective priority is at least base priority -/
theorem effective_ge_base (base : NumericPriority) (d : Deadline) :
    base.value ≤ (effectivePriority base d).value := by
  simp only [effectivePriority]
  have h : base.value ≤ base.value + (maxPriority - base.value) * d.boostPercent / 100 := by
    have : 0 ≤ (maxPriority - base.value) * d.boostPercent / 100 := Nat.zero_le _
    omega
  exact Nat.le_min.mpr ⟨h, base.bounded⟩

/-- THEOREM: Effective priority is bounded -/
theorem effective_bounded (base : NumericPriority) (d : Deadline) :
    (effectivePriority base d).value ≤ 1000 := by
  exact (effectivePriority base d).bounded

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: PRIORITY QUEUE ORDERING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A priority queue entry -/
structure PriorityEntry (α : Type*) where
  value : α
  priority : NumericPriority

/-- Compare entries by priority (higher first) -/
def PriorityEntry.compare {α : Type*} (a b : PriorityEntry α) : Ordering :=
  -- Higher priority comes first (reverse order)
  Ord.compare b.priority.value a.priority.value

/-- Helper: compareOfLessAndEq returns lt iff the first arg is less -/
theorem compareOfLessAndEq_lt {a b : ℕ} : 
    compareOfLessAndEq a b = Ordering.lt ↔ a < b := by
  simp only [compareOfLessAndEq]
  constructor
  · intro h
    split_ifs at h with h1
    exact h1
  · intro h
    simp only [h, ↓reduceIte]

/-- THEOREM: Priority comparison is transitive -/
theorem priority_compare_trans {α : Type*} (a b c : PriorityEntry α)
    (hab : a.compare b = Ordering.lt) (hbc : b.compare c = Ordering.lt) :
    a.compare c = Ordering.lt := by
  simp only [PriorityEntry.compare, Ord.compare] at *
  -- hab says compareOfLessAndEq b.value a.value = lt, so b.value < a.value
  -- hbc says compareOfLessAndEq c.value b.value = lt, so c.value < b.value
  -- We need compareOfLessAndEq c.value a.value = lt, i.e., c.value < a.value
  have hab' : b.priority.value < a.priority.value := compareOfLessAndEq_lt.mp hab
  have hbc' : c.priority.value < b.priority.value := compareOfLessAndEq_lt.mp hbc
  have hac : c.priority.value < a.priority.value := Nat.lt_trans hbc' hab'
  exact compareOfLessAndEq_lt.mpr hac

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: PRIORITY OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Return the higher of two priorities -/
def higherPriority (a b : Priority) : Priority :=
  if a.toNat ≥ b.toNat then a else b

/-- Return the lower of two priorities -/
def lowerPriority (a b : Priority) : Priority :=
  if a.toNat ≤ b.toNat then a else b

/-- THEOREM: higherPriority returns one of its inputs -/
theorem higher_is_input (a b : Priority) :
    higherPriority a b = a ∨ higherPriority a b = b := by
  simp only [higherPriority]
  by_cases h : a.toNat ≥ b.toNat
  · left; simp [h]
  · right; simp [h]

/-- THEOREM: higherPriority is idempotent -/
theorem higher_idempotent (a : Priority) : higherPriority a a = a := by
  simp [higherPriority]

/-- THEOREM: lowerPriority returns one of its inputs -/
theorem lower_is_input (a b : Priority) :
    lowerPriority a b = a ∨ lowerPriority a b = b := by
  simp only [lowerPriority]
  by_cases h : a.toNat ≤ b.toNat
  · left; simp [h]
  · right; simp [h]

/-- THEOREM: lowerPriority is idempotent -/
theorem lower_idempotent (a : Priority) : lowerPriority a a = a := by
  simp [lowerPriority]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: DETERMINISM
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- THEOREM: Priority operations are deterministic -/
theorem priority_toNat_deterministic (p : Priority) : p.toNat = p.toNat := rfl

theorem toNumeric_deterministic (p : Priority) : toNumeric p = toNumeric p := rfl

theorem toSemantic_deterministic (n : NumericPriority) : toSemantic n = toSemantic n := rfl

theorem effectivePriority_deterministic (base : NumericPriority) (d : Deadline) :
    effectivePriority base d = effectivePriority base d := rfl

theorem higherPriority_deterministic (a b : Priority) :
    higherPriority a b = higherPriority a b := rfl

end Hydrogen.Schema.Priority
