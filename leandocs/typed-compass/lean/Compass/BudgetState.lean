/-
  Compass.BudgetState - Budget control with refill and consume proofs
  
  Contains Grok-provided theorems:
  - P0-B1: Refill Bounded
  - P0-B2: Refill Monotonic
  - P0-B3: Consume Fails Insufficient
  - P0-B4: Consume Success Remaining
-/

import Compass.Core

namespace Compass.BudgetState

open Compass.Core

/-! ## Budget State -/

structure BudgetState where
  current : Nat
  max : Nat
  invariant : current ≤ max
  deriving Repr

/-! ## Refill Operation -/

def refill (bs : BudgetState) (amt : Nat) : BudgetState :=
  let newCurrent := bs.current + amt
  if h : newCurrent ≤ bs.max then
    { current := newCurrent, max := bs.max, invariant := h }
  else
    { current := bs.max, max := bs.max, invariant := Nat.le_refl _ }

/-! ## THEOREM P0-B1: Refill Bounded

    After refill, current tokens never exceed max.
-/

theorem refill_bounded (bs : BudgetState) (amt : Nat) :
    (refill bs amt).current ≤ (refill bs amt).max := by
  simp [refill]
  split
  · assumption
  · exact Nat.le_refl _

/-! ## THEOREM P0-B2: Refill Monotonic

    Refill never decreases current tokens (monotonically increasing).
-/

theorem refill_monotonic (bs : BudgetState) (amt : Nat) :
    bs.current ≤ (refill bs amt).current := by
  simp [refill]
  split
  · exact Nat.le_add_right _ _
  · exact bs.invariant

/-! ## Consume Operation -/

def consume (bs : BudgetState) (amt : Nat) : Option BudgetState :=
  if bs.current ≥ amt then
    some { 
      current := bs.current - amt, 
      max := bs.max,
      invariant := Nat.le_trans (Nat.sub_le _ _) bs.invariant 
    }
  else
    none

/-! ## THEOREM P0-B3: Consume Fails Insufficient

    Consume returns none when current budget is insufficient.
-/

theorem consume_fails_insufficient (bs : BudgetState) (amt : Nat) 
    (h_insuff : bs.current < amt) :
    consume bs amt = none := by
  simp only [consume]
  split
  · rename_i h
    exact absurd h (Nat.not_le_of_lt h_insuff)
  · rfl

/-! ## THEOREM P0-B4: Consume Success Remaining

    When consume succeeds, the new current equals old current minus amount,
    and the invariant is preserved.
-/

theorem consume_success_remaining (bs : BudgetState) (amt : Nat) 
    (h_suff : bs.current ≥ amt) :
    ∃ newBs : BudgetState, 
      consume bs amt = some newBs ∧ 
      newBs.current = bs.current - amt ∧ 
      newBs.current ≤ newBs.max := by
  simp only [consume, h_suff, ite_true]
  exact ⟨_, rfl, rfl, Nat.le_trans (Nat.sub_le _ _) bs.invariant⟩

/-! ## THEOREM P0-B5: Consume Preserves Max

    Consume never changes the max budget.
-/

theorem consume_preserves_max (bs : BudgetState) (amt : Nat) (newBs : BudgetState)
    (h : consume bs amt = some newBs) :
    newBs.max = bs.max := by
  simp only [consume] at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
  · simp only [reduceCtorEq] at h

/-! ## THEOREM P0-B6: Budget Invariant Always Holds

    For any BudgetState, current ≤ max is always true by construction.
-/

theorem budget_invariant_holds (bs : BudgetState) : bs.current ≤ bs.max :=
  bs.invariant

/-! ## Alert Levels -/

inductive AlertLevel where
  | Info : AlertLevel
  | Warning : AlertLevel
  | Critical : AlertLevel
  | Exhausted : AlertLevel
  deriving DecidableEq, Repr, Inhabited

def AlertLevel.toString : AlertLevel → String
  | .Info => "info"
  | .Warning => "warning"
  | .Critical => "critical"
  | .Exhausted => "exhausted"

def AlertLevel.fromString : String → Option AlertLevel
  | "info" => some .Info
  | "warning" => some .Warning
  | "critical" => some .Critical
  | "exhausted" => some .Exhausted
  | _ => none

theorem alert_level_roundtrip (a : AlertLevel) :
    AlertLevel.fromString (AlertLevel.toString a) = some a := by
  cases a <;> rfl

instance : Extractable AlertLevel where
  encode a := .str (AlertLevel.toString a)
  decode j := do
    let s ← j.asString
    AlertLevel.fromString s
  roundtrip a := by simp [Json.asString, alert_level_roundtrip]

/-! ## Budget Tier -/

inductive BudgetTier where
  | Normal : BudgetTier      -- > 50% remaining
  | Cautious : BudgetTier    -- 25-50% remaining
  | Minimal : BudgetTier     -- 10-25% remaining
  | Exhausted : BudgetTier   -- < 10% remaining
  deriving DecidableEq, Repr, Inhabited

def BudgetTier.toString : BudgetTier → String
  | .Normal => "normal"
  | .Cautious => "cautious"
  | .Minimal => "minimal"
  | .Exhausted => "exhausted"

def BudgetTier.fromString : String → Option BudgetTier
  | "normal" => some .Normal
  | "cautious" => some .Cautious
  | "minimal" => some .Minimal
  | "exhausted" => some .Exhausted
  | _ => none

theorem budget_tier_roundtrip (t : BudgetTier) :
    BudgetTier.fromString (BudgetTier.toString t) = some t := by
  cases t <;> rfl

instance : Extractable BudgetTier where
  encode t := .str (BudgetTier.toString t)
  decode j := do
    let s ← j.asString
    BudgetTier.fromString s
  roundtrip t := by simp [Json.asString, budget_tier_roundtrip]

/-! ## Tier Calculation -/

def calculateTier (current max : Nat) : BudgetTier :=
  if max = 0 then .Exhausted
  else
    let pct := current * 100 / max
    if pct > 50 then .Normal
    else if pct > 25 then .Cautious
    else if pct > 10 then .Minimal
    else .Exhausted

/-! ## THEOREM: Exhausted tier means low budget -/

-- If calculateTier returns Exhausted and max > 0, then pct ≤ 10
theorem exhausted_means_low (current max : Nat) (h_pos : max > 0) :
    calculateTier current max = .Exhausted → current * 100 / max ≤ 10 := by
  intro h_exh
  simp only [calculateTier] at h_exh
  -- Since max > 0, the first branch (max = 0) is false
  simp only [Nat.pos_iff_ne_zero.mp h_pos, ↓reduceIte] at h_exh
  -- Now h_exh says the if-chain reached Exhausted
  -- This means: ¬(pct > 50) ∧ ¬(pct > 25) ∧ ¬(pct > 10)
  -- We need to show pct ≤ 10
  split at h_exh
  case isTrue => contradiction  -- pct > 50 implies Normal, not Exhausted
  case isFalse h50 =>
    split at h_exh
    case isTrue => contradiction  -- pct > 25 implies Cautious
    case isFalse h25 =>
      split at h_exh
      case isTrue => contradiction  -- pct > 10 implies Minimal
      case isFalse h10 =>
        -- h10 : ¬(current * 100 / max > 10), which is current * 100 / max ≤ 10
        exact Nat.not_lt.mp h10

/-! ## Extractable Instance for BudgetState -/

-- Pattern matching decode for transparent reduction (no do-notation)
def decodeBudgetState : Json → Option BudgetState
  | .obj [("current", .int c), ("max", .int m)] =>
    if h : c.toNat ≤ m.toNat then
      some { current := c.toNat, max := m.toNat, invariant := h }
    else
      none
  | _ => none

theorem budget_state_roundtrip (bs : BudgetState) :
    decodeBudgetState (.obj [("current", .int bs.current), ("max", .int bs.max)]) = some bs := by
  simp only [decodeBudgetState]
  -- Goal: if h : (↑bs.current).toNat ≤ (↑bs.max).toNat then some {...} else none = some bs
  -- (↑n : Int).toNat = n for Nat n (definitionally)
  -- So condition is bs.current ≤ bs.max
  split
  case isTrue h => rfl
  case isFalse h => exact absurd bs.invariant h

instance : Extractable BudgetState where
  encode bs := .obj [
    ("current", .int bs.current),
    ("max", .int bs.max)
  ]
  decode := decodeBudgetState
  roundtrip := budget_state_roundtrip

end Compass.BudgetState
