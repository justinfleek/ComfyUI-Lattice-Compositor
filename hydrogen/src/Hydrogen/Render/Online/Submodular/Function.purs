-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // submodular // function
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Submodular Function Types with Phantom Monotonicity
-- |
-- | A function f: 2^V → ℝ is submodular if for all A ⊆ B ⊆ V and x ∉ B:
-- |   f(A ∪ {x}) - f(A) ≥ f(B ∪ {x}) - f(B)
-- |
-- | This is the "diminishing returns" property: adding an element to a smaller
-- | set provides at least as much gain as adding it to a larger set.
-- |
-- | ## Monotonicity as Phantom Type
-- |
-- | We use phantom types `Monotone` and `NonMonotone` to track function properties
-- | at compile time. This ensures we cannot accidentally use a non-monotone function
-- | where a monotone one is required for correctness guarantees.
-- |
-- | - Monotone + Matroid: Greedy achieves (1 - 1/e) ≈ 0.632 approximation
-- | - Non-monotone: Best known is 1/2 approximation
-- |
-- | ## Curvature as Value
-- |
-- | Curvature κ ∈ [0,1] is value-level because it's typically computed from
-- | the function's parameters, not statically known. κ = 0 means modular (linear),
-- | κ = 1 means maximally curved (steepest diminishing returns).

module Hydrogen.Render.Online.Submodular.Function
  ( -- * Monotonicity Phantom Types
    Monotone
  , NonMonotone
  
  -- * Curvature Type
  , Curvature(..)
  , mkCurvature
  , unwrapCurvature
  , zeroCurvature
  , maxCurvature
  
  -- * Submodular Function Type
  , SubmodularFn(..)
  , evaluate
  , marginalGain
  , getCurvature
  
  -- * Constructors
  , mkMonotoneSubmodular
  , mkNonMonotoneSubmodular
  
  -- * Properties
  , class IsMonotoneFn
  , isMonotone
  , approximationBound
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , compare
  , show
  , ($)
  , (<>)
  , (>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Set (Set)

import Hydrogen.Render.Online.Core
  ( BoundedNumber
  , Utility(..)
  , clampToBounds
  , mkBoundedNumber
  , unwrapBounded
  , zeroUtility
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                           // monotonicity // phantom // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Phantom type marker for monotone submodular functions
-- |
-- | A function f is monotone if: A ⊆ B implies f(A) ≤ f(B)
-- | This guarantees (1 - 1/e) approximation with greedy + matroid.
data Monotone

-- | Phantom type marker for non-monotone submodular functions
-- |
-- | Non-monotone functions may decrease when adding elements.
-- | Best known approximation is 1/2.
data NonMonotone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // curvature // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Curvature parameter κ ∈ [0, 1]
-- |
-- | Curvature measures the "steepness" of diminishing returns:
-- |
-- | - κ = 0: Modular (linear) — no diminishing returns
-- | - κ = 1: Maximally curved — steepest diminishing returns
-- |
-- | For a monotone submodular function with curvature κ, greedy achieves
-- | at least (1 - κ/e) approximation, which is tighter than (1 - 1/e)
-- | when κ < 1.
newtype Curvature = Curvature BoundedNumber

derive instance eqCurvature :: Eq Curvature
derive instance ordCurvature :: Ord Curvature

instance showCurvature :: Show Curvature where
  show (Curvature bn) = "Curvature(" <> show (unwrapBounded bn) <> ")"

-- | Construct curvature within valid bounds
mkCurvature :: Number -> Maybe Curvature
mkCurvature k = case mkBoundedNumber 0.0 1.0 k of
  Just bn -> Just (Curvature bn)
  Nothing -> Nothing

-- | Extract the curvature value
unwrapCurvature :: Curvature -> Number
unwrapCurvature (Curvature bn) = unwrapBounded bn

-- | Zero curvature — modular function
zeroCurvature :: Curvature
zeroCurvature = Curvature (clampToBounds 0.0 1.0 0.0)

-- | Maximum curvature — steepest diminishing returns
maxCurvature :: Curvature
maxCurvature = Curvature (clampToBounds 0.0 1.0 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // submodular // function // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A submodular function with phantom monotonicity marker
-- |
-- | The `mono` parameter is phantom — it doesn't appear in the runtime
-- | representation. It exists only to track the monotonicity property
-- | at compile time.
-- |
-- | Type parameters:
-- | - `mono`: Phantom type indicating Monotone or NonMonotone
-- | - `a`: The element type of the ground set
-- |
-- | Invariants (enforced by construction):
-- | - Submodularity: f(A ∪ {x}) - f(A) ≥ f(B ∪ {x}) - f(B) for A ⊆ B
-- | - If mono = Monotone: f(A) ≤ f(B) for A ⊆ B
newtype SubmodularFn mono a = SubmodularFn
  { evalFn :: Set a -> Utility
  , marginalFn :: a -> Set a -> Utility
  , curvatureVal :: Curvature
  }

-- | Evaluate the submodular function on a set
evaluate :: forall mono a. SubmodularFn mono a -> Set a -> Utility
evaluate (SubmodularFn r) = r.evalFn

-- | Compute the marginal gain of adding an element to a set
marginalGain :: forall mono a. SubmodularFn mono a -> a -> Set a -> Utility
marginalGain (SubmodularFn r) = r.marginalFn

-- | Get the curvature of the function
getCurvature :: forall mono a. SubmodularFn mono a -> Curvature
getCurvature (SubmodularFn r) = r.curvatureVal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Construct a monotone submodular function
-- |
-- | The caller MUST ensure that:
-- | 1. The function is submodular (diminishing returns)
-- | 2. The function is monotone (larger sets have larger value)
-- |
-- | These properties cannot be verified at runtime for arbitrary functions,
-- | so the caller takes responsibility for correctness.
-- |
-- | For verified functions, use the Coverage module which constructs
-- | functions that are monotone by mathematical definition.
mkMonotoneSubmodular
  :: forall a
   . Ord a
  => (Set a -> Utility)
  -> (a -> Set a -> Utility)
  -> Curvature
  -> SubmodularFn Monotone a
mkMonotoneSubmodular evalFn marginalFn curvatureVal = SubmodularFn
  { evalFn
  , marginalFn
  , curvatureVal
  }

-- | Construct a non-monotone submodular function
-- |
-- | Non-monotone submodular functions arise in applications like
-- | summarization where diversity is important and too many similar
-- | elements can decrease value.
mkNonMonotoneSubmodular
  :: forall a
   . Ord a
  => (Set a -> Utility)
  -> (a -> Set a -> Utility)
  -> Curvature
  -> SubmodularFn NonMonotone a
mkNonMonotoneSubmodular evalFn marginalFn curvatureVal = SubmodularFn
  { evalFn
  , marginalFn
  , curvatureVal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type class for checking monotonicity at value level
-- |
-- | This reflects the phantom type to runtime for cases where
-- | we need to branch on monotonicity.
class IsMonotoneFn mono where
  isMonotone :: forall a. SubmodularFn mono a -> Boolean

instance isMonotoneFnMonotone :: IsMonotoneFn Monotone where
  isMonotone _ = true

instance isMonotoneFnNonMonotone :: IsMonotoneFn NonMonotone where
  isMonotone _ = false

-- | Get the approximation bound for greedy algorithm
-- |
-- | Returns the worst-case approximation ratio:
-- | - Monotone: (1 - 1/e) ≈ 0.632
-- | - Non-monotone: 1/2 = 0.5
-- |
-- | With curvature κ, monotone can achieve (1 - κ/e), but we
-- | return the conservative bound here.
approximationBound :: forall mono a. IsMonotoneFn mono => SubmodularFn mono a -> Number
approximationBound fn =
  if isMonotone fn
    then 0.6321205588285577  -- 1 - 1/e
    else 0.5
