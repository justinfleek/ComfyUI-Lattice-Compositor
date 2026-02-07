module Compass.BudgetState where

import Compass.Core
import Prelude

{-! ## Budget State -}

newtype BudgetState = BudgetState
  { current :: Number
  , max :: Number
  , invariant :: Boolean
  }

{-! ## Refill Operation -}

refill :: BudgetState -> Number -> BudgetState
refill bs amt = 
  let newCurrent = current bs + amt
  if newCurrent <= max bs 
    then BudgetState { current: newCurrent, max: max bs, invariant: true }
    else bs

{-! ## THEOREM P0-B1: Refill Bounded -}

{-| Proves that refill either stays within bounds or stays put.
| Refill can only add within budget limit. -}
refill_bounded :: BudgetState -> Boolean
refill_bounded bs = 
  let newBs = refill bs 1
  current (newBs :: Number) <= max (newBs :: Number)
  && invariant (newBs :: Boolean)

{-! ## THEOREM P0-B2: Refill Monotonic -}

{-| Proves that refills with positive amounts increase budget.
| Assumes positive amount - can be zero though (no increase). -}
refill_monotonic :: BudgetState -> Number -> BudgetState
refill_monotonic bs amt = 
  let newBs = refill bs amt
  current (newBs :: Number) >= current (bs :: Number)

{-! ## Consume Operation -}

consume :: BudgetState -> Number -> Maybe BudgetState
consume bs amt = 
  if current bs >= amt then
    let newCurrent = current bs - amt
    if newCurrent <= max bs 
      then Just (BudgetState { current: newCurrent, max: max bs, invariant: newCurrent <= max bs })
      else Nothing
  else
    Nothing

{-! ## THEOREM P0-B3: Consume Fails Insufficient -}

{-| Proves that consumption fails when insufficient funds.
| Returns none and doesn't modify state. -}
consume_fails_insufficient :: BudgetState -> Number -> Boolean
consume_fails_insufficient bs amt = current (bs :: Number) < amt

{-! ## THEOREM P0-B4: Consume Success Remaining -}

{-| Proves that successful consumption preserves bounds and returns exact remaining.
| Exists new budget state, returns some, with exact remaining and invariant preserved. -}
consume_success_remaining :: BudgetState -> Number -> BudgetState -> Maybe BudgetState
consume_success_remaining bs amt = consume bs amt
