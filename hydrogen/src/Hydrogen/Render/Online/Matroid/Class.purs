-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // matroid // class
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matroid Typeclass
-- |
-- | A matroid M = (E, I) is a combinatorial structure where:
-- | - E is a finite ground set
-- | - I ⊆ 2^E is a family of "independent" sets
-- |
-- | Matroid Axioms:
-- | 1. ∅ ∈ I (empty set is independent)
-- | 2. If A ∈ I and B ⊆ A, then B ∈ I (hereditary property)
-- | 3. If A, B ∈ I and |A| < |B|, then ∃x ∈ B\A such that A ∪ {x} ∈ I (exchange)
-- |
-- | ## Why Matroids Matter
-- |
-- | Greedy maximization of a monotone submodular function subject to a matroid
-- | constraint achieves (1 - 1/e) ≈ 0.632 approximation. This is optimal for
-- | polynomial-time algorithms.
-- |
-- | ## Common Matroids
-- |
-- | - **Cardinality**: I = {S : |S| ≤ k}
-- | - **Partition**: Ground set partitioned, at most k_i from each partition
-- | - **Uniform**: Any k elements can be chosen
-- |
-- | For render quality allocation, we use a **partition matroid** over render
-- | tiers (foveal/peripheral/background) with tier-specific bounds.

module Hydrogen.Render.Online.Matroid.Class
  ( -- * Matroid Typeclass
    class Matroid
  , independent
  , rank
  , extend
  
  -- * Matroid Operations
  , isMaximal
  , couldAdd
  , selectGreedy
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , map
  , not
  , otherwise
  , show
  , unit
  , ($)
  , (&&)
  , (+)
  , (<)
  , (<<<)
  , (<>)
  , (==)
  , (>=)
  , (||)
  )

import Data.Array as Array
import Data.Foldable (class Foldable, foldl, any)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(Tuple), fst, snd)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // matroid // typeclass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matroid typeclass
-- |
-- | A matroid is parameterized by:
-- | - `m`: The matroid structure (defines the constraint)
-- | - `v`: The element type of the ground set
-- |
-- | The functional dependency `m -> v` ensures that a matroid uniquely
-- | determines its element type.
-- |
-- | ## Laws
-- |
-- | 1. `independent m Set.empty == true` (empty set is independent)
-- | 2. `independent m a && Set.isSubsetOf b a ==> independent m b` (hereditary)
-- | 3. Exchange axiom (not easily expressed as a law, verified by construction)
class Matroid m v | m -> v where
  -- | Check if a set is independent (feasible within the constraint)
  -- |
  -- | Returns true if the set satisfies the matroid constraint.
  independent :: m -> Set v -> Boolean
  
  -- | Get the rank of the matroid (size of largest independent set)
  -- |
  -- | For a partition matroid with k_i per partition, rank = Σ k_i
  rank :: m -> Int
  
  -- | Try to extend an independent set with a new element
  -- |
  -- | Returns Just(extended set) if adding the element preserves independence,
  -- | Nothing otherwise.
  -- |
  -- | Precondition: The input set must be independent.
  extend :: m -> Set v -> v -> Maybe (Set v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // matroid // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if an independent set is maximal (cannot be extended)
-- |
-- | A set S is maximal if no element can be added while maintaining independence.
-- | By the matroid exchange axiom, all maximal independent sets have the same
-- | size (the rank).
isMaximal :: forall m v. Ord v => Matroid m v => m -> Set v -> Array v -> Boolean
isMaximal matroid current candidates =
  not (any (\c -> canExtend matroid current c) candidates)

-- | Check if a specific element could be added to maintain independence
canExtend :: forall m v. Ord v => Matroid m v => m -> Set v -> v -> Boolean
canExtend matroid current candidate =
  case extend matroid current candidate of
    Just _ -> true
    Nothing -> false

-- | Check if any of the candidates could be added
couldAdd :: forall m v. Ord v => Matroid m v => m -> Set v -> Array v -> Boolean
couldAdd matroid current candidates =
  any (canExtend matroid current) candidates

-- | Greedy selection subject to matroid constraint
-- |
-- | Given a list of elements sorted by decreasing value, greedily select
-- | elements while respecting the matroid constraint.
-- |
-- | For monotone submodular functions, this achieves (1 - 1/e) approximation.
-- |
-- | Arguments:
-- | - `matroid`: The matroid constraint
-- | - `candidates`: Elements sorted by decreasing marginal gain
-- |
-- | Returns: A maximal independent set of selected elements
selectGreedy
  :: forall m v
   . Ord v
  => Matroid m v
  => m
  -> Array v
  -> Set v
selectGreedy matroid candidates =
  foldl (tryAdd matroid) Set.empty candidates

-- | Try to add an element to the current selection
tryAdd :: forall m v. Ord v => Matroid m v => m -> Set v -> v -> Set v
tryAdd matroid current candidate =
  case extend matroid current candidate of
    Just extended -> extended
    Nothing -> current
