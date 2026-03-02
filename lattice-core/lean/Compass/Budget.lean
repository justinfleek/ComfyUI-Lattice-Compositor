/-
  Compass.Budget - Budget control with refill and consume proofs
-/

import Compass.Core

namespace Compass.Budget

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

/-! ## THEOREM P0-B1: Refill Bounded -/

theorem refill_bounded (bs : BudgetState) (amt : Nat) :
    (refill bs amt).current ≤ (refill bs amt).max := by
  simp only [refill]
  split
  · assumption
  · exact Nat.le_refl _

/-! ## THEOREM P0-B2: Refill Monotonic -/

theorem refill_monotonic (bs : BudgetState) (amt : Nat) :
    bs.current ≤ (refill bs amt).current := by
  simp only [refill]
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

/-! ## THEOREM P0-B3: Consume Fails Insufficient -/

theorem consume_fails_insufficient (bs : BudgetState) (amt : Nat) 
    (h_insuff : bs.current < amt) :
    consume bs amt = none := by
  simp only [consume]
  split
  · rename_i h
    exact absurd h (Nat.not_le_of_lt h_insuff)
  · rfl

/-! ## THEOREM P0-B4: Consume Success Remaining -/

theorem consume_success_remaining (bs : BudgetState) (amt : Nat) 
    (h_suff : bs.current ≥ amt) :
    ∃ newBs : BudgetState, 
      consume bs amt = some newBs ∧ 
      newBs.current = bs.current - amt ∧ 
      newBs.current ≤ newBs.max := by
  simp only [consume, h_suff, ite_true]
  exact ⟨_, rfl, rfl, Nat.le_trans (Nat.sub_le _ _) bs.invariant⟩

/-! ## Extractable Instance -/

-- Pattern matching decode for transparent reduction (no do-notation)
def decodeBudgetState : Json → Option BudgetState
  | .obj [("current", .int c), ("max", .int m)] =>
    if h : c.toNat ≤ m.toNat then
      some { current := c.toNat, max := m.toNat, invariant := h }
    else
      none
  | _ => none

theorem budget_roundtrip (bs : BudgetState) :
    decodeBudgetState (.obj [("current", .int bs.current), ("max", .int bs.max)]) = some bs := by
  simp only [decodeBudgetState]
  split
  case isTrue h =>
    rfl
  case isFalse h =>
    exact absurd bs.invariant h

instance : Extractable BudgetState where
  encode bs := .obj [
    ("current", .int bs.current),
    ("max", .int bs.max)
  ]
  decode := decodeBudgetState
  roundtrip := budget_roundtrip

end Compass.Budget
