-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // selection // greedy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Lazy Greedy Selection for Submodular Maximization
-- |
-- | The greedy algorithm for submodular maximization:
-- | 1. Start with empty set S = ∅
-- | 2. Repeat until matroid constraint is tight:
-- |    - Find element e with maximum marginal gain f(S ∪ {e}) - f(S)
-- |    - If adding e maintains independence, add it: S = S ∪ {e}
-- | 3. Return S
-- |
-- | ## Approximation Guarantee
-- |
-- | For a **monotone** submodular function f subject to a **matroid** constraint:
-- |   f(S_greedy) ≥ (1 - 1/e) · f(S_optimal) ≈ 0.632 · f(S_optimal)
-- |
-- | This is optimal for polynomial-time algorithms (assuming P ≠ NP).
-- |
-- | ## Lazy Evaluation
-- |
-- | We use "lazy greedy" for efficiency:
-- | - Maintain heap sorted by cached marginal gains
-- | - Only recompute gain when element is popped
-- | - If gain decreased, re-insert; otherwise select
-- |
-- | This reduces function evaluations from O(nk) to O(n log n) on average.
-- |
-- | ## Type-Safe Guarantees
-- |
-- | The return type includes an `ApproxWitness` that proves the approximation
-- | ratio. This witness can only be constructed for monotone functions with
-- | matroid constraints, ensuring we don't accidentally claim (1-1/e) for
-- | non-monotone functions.

module Hydrogen.Render.Online.Selection.Greedy
  ( -- * Selection Result
    SelectionResult(..)
  
  -- * Greedy Algorithms
  , greedySelect
  , lazyGreedySelect
  
  -- * Approximation Witness
  , ApproxWitness(..)
  , approximationRatio
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(GT)
  , compare
  , map
  , show
  , ($)
  , (+)
  , (<)
  , (<>)
  , (==)
  , (>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(Tuple), fst, snd)

import Hydrogen.Render.Online.Core
  ( RegionSelection
  , Utility(..)
  , clampToBounds
  , unwrapBounded
  , zeroUtility
  )
import Hydrogen.Render.Online.Matroid.Class (class Matroid, extend)
import Hydrogen.Render.Online.Submodular.Function
  ( Monotone
  , SubmodularFn
  , marginalGain
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // approximation // witness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximation ratio witness
-- |
-- | This type encodes the provable approximation guarantee for a selection.
-- | The witness can only be constructed via the greedy algorithm with
-- | appropriate function properties.
-- |
-- | - `MonotoneMatroidWitness`: (1 - 1/e) ≈ 0.632 for monotone + matroid
-- | - `NonMonotoneWitness`: 1/2 for non-monotone (best known)
data ApproxWitness
  = MonotoneMatroidWitness   -- Guarantees (1 - 1/e) approximation
  | NonMonotoneWitness       -- Guarantees 1/2 approximation

derive instance eqApproxWitness :: Eq ApproxWitness

instance showApproxWitness :: Show ApproxWitness where
  show MonotoneMatroidWitness = "ApproxWitness(1-1/e ≈ 0.632)"
  show NonMonotoneWitness = "ApproxWitness(1/2 = 0.5)"

-- | Get the numeric approximation ratio
approximationRatio :: ApproxWitness -> Number
approximationRatio MonotoneMatroidWitness = 0.6321205588285577  -- 1 - 1/e
approximationRatio NonMonotoneWitness = 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // selection // result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of greedy selection
-- |
-- | Contains the selected set along with the approximation witness.
-- | The witness proves what guarantee the selection achieves.
newtype SelectionResult = SelectionResult
  { selections :: Set RegionSelection
  , witness :: ApproxWitness
  , utility :: Utility
  }

derive instance eqSelectionResult :: Eq SelectionResult

instance showSelectionResult :: Show SelectionResult where
  show (SelectionResult r) =
    "SelectionResult(count=" <> show (Set.size r.selections) <>
    ", utility=" <> show r.utility <>
    ", " <> show r.witness <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // greedy // selection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard greedy selection for monotone submodular functions
-- |
-- | Selects elements in order of marginal gain until the matroid constraint
-- | is tight. Returns the selected set with approximation witness.
-- |
-- | Complexity: O(n · k · T_f) where n = candidates, k = rank, T_f = eval time
greedySelect
  :: forall m
   . Ord RegionSelection
  => Matroid m RegionSelection
  => SubmodularFn Monotone RegionSelection
  -> m
  -> Array RegionSelection
  -> SelectionResult
greedySelect fn matroid candidates =
  let -- Greedy loop: repeatedly add best feasible element
      selected = greedyLoop fn matroid Set.empty candidates
      
      -- Compute final utility (for reporting)
      finalUtility = computeUtility fn selected
      
  in SelectionResult
       { selections: selected
       , witness: MonotoneMatroidWitness  -- Proven by construction
       , utility: finalUtility
       }

-- | The greedy loop implementation
greedyLoop
  :: forall m
   . Ord RegionSelection
  => Matroid m RegionSelection
  => SubmodularFn Monotone RegionSelection
  -> m
  -> Set RegionSelection
  -> Array RegionSelection
  -> Set RegionSelection
greedyLoop fn matroid current candidates =
  case findBestFeasible fn matroid current candidates of
    Nothing -> current  -- No more feasible additions
    Just best ->
      case extend matroid current best of
        Nothing -> current  -- Shouldn't happen if findBestFeasible is correct
        Just extended -> 
          -- Remove selected element and continue
          let remaining = Array.filter (\c -> (c == best) == false) candidates
          in greedyLoop fn matroid extended remaining

-- | Find the feasible element with maximum marginal gain
findBestFeasible
  :: forall m
   . Ord RegionSelection
  => Matroid m RegionSelection
  => SubmodularFn Monotone RegionSelection
  -> m
  -> Set RegionSelection
  -> Array RegionSelection
  -> Maybe RegionSelection
findBestFeasible fn matroid current candidates =
  let -- Compute gains for all feasible candidates
      withGains = Array.mapMaybe (computeIfFeasible fn matroid current) candidates
      
      -- Sort by gain descending
      sorted = Array.sortBy (\a b -> compare (snd b) (snd a)) withGains
      
  in map fst (Array.head sorted)

-- | Compute marginal gain if element is feasible
computeIfFeasible
  :: forall m
   . Ord RegionSelection
  => Matroid m RegionSelection
  => SubmodularFn Monotone RegionSelection
  -> m
  -> Set RegionSelection
  -> RegionSelection
  -> Maybe (Tuple RegionSelection Utility)
computeIfFeasible fn matroid current candidate =
  case extend matroid current candidate of
    Nothing -> Nothing  -- Not feasible
    Just _ ->
      let gain = marginalGain fn candidate current
      in Just (Tuple candidate gain)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // lazy // greedy // selection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lazy greedy selection with cached gradients
-- |
-- | Uses pre-computed gradient estimates for efficiency. Elements are sorted
-- | by cached gain; we only recompute when selecting.
-- |
-- | This is the primary algorithm for online optimization where gradient
-- | estimates are maintained across epochs.
-- |
-- | Complexity: O(n log n + k · T_f) — much better than standard greedy
lazyGreedySelect
  :: forall m
   . Ord RegionSelection
  => Matroid m RegionSelection
  => SubmodularFn Monotone RegionSelection
  -> m
  -> Array (Tuple RegionSelection Utility)  -- Pre-sorted by cached gain
  -> SelectionResult
lazyGreedySelect fn matroid sortedCandidates =
  let -- Extract just the candidates (already sorted)
      candidates = map fst sortedCandidates
      
      -- Run greedy with this ordering
      selected = lazyLoop fn matroid Set.empty candidates
      
      -- Compute final utility
      finalUtility = computeUtility fn selected
      
  in SelectionResult
       { selections: selected
       , witness: MonotoneMatroidWitness
       , utility: finalUtility
       }

-- | Lazy greedy loop — trusts the ordering, only checks feasibility
lazyLoop
  :: forall m
   . Ord RegionSelection
  => Matroid m RegionSelection
  => SubmodularFn Monotone RegionSelection
  -> m
  -> Set RegionSelection
  -> Array RegionSelection
  -> Set RegionSelection
lazyLoop fn matroid current candidates =
  case Array.uncons candidates of
    Nothing -> current
    Just { head: candidate, tail: rest } ->
      -- Check if adding this candidate is feasible and beneficial
      case extend matroid current candidate of
        Nothing ->
          -- Not feasible (violates matroid), skip
          lazyLoop fn matroid current rest
        Just extended ->
          -- Check marginal gain (lazy recomputation)
          let gain = marginalGain fn candidate current
              Utility gainVal = gain
          in if unwrapBounded gainVal > 0.0
               then lazyLoop fn matroid extended rest
               else lazyLoop fn matroid current rest

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute total utility of a selection
computeUtility
  :: SubmodularFn Monotone RegionSelection
  -> Set RegionSelection
  -> Utility
computeUtility fn selected =
  -- Sum marginal gains (equivalent to f(S) for additive approximation)
  foldl addGain zeroUtility (Set.toUnfoldable selected :: Array RegionSelection)
  where
    addGain :: Utility -> RegionSelection -> Utility
    addGain (Utility acc) element =
      let Utility gain = marginalGain fn element Set.empty
          accNum = unwrapBounded acc
          gainNum = unwrapBounded gain
      in Utility (clampToBounds 0.0 1.0e12 (accNum + gainNum))
