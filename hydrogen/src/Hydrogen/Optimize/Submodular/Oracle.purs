-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // optimize // submodular // oracle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Submodular Oracle Implementations.
-- |
-- | ## Theoretical Foundation
-- |
-- | A submodular function f : 2^V → ℝ₊ satisfies diminishing returns:
-- |
-- |   f(A ∪ {e}) - f(A) ≥ f(B ∪ {e}) - f(B)  for all A ⊆ B, e ∉ B
-- |
-- | This module provides constructors for common submodular functions:
-- |
-- | ### Coverage Functions
-- |
-- | f(S) = |⋃_{e ∈ S} N(e)| where N(e) is the "neighborhood" of e.
-- |
-- | Examples:
-- | - Set cover: elements cover subsets of a universe
-- | - Influence maximization: users influence their social network neighbors
-- | - UI coverage: widgets cover user tasks/needs
-- |
-- | ### Weighted Coverage
-- |
-- | f(S) = Σ_{u ∈ ⋃_{e ∈ S} N(e)} w(u)
-- |
-- | Weighted version where covering element u contributes weight w(u).
-- |
-- | ### Facility Location
-- |
-- | f(S) = Σ_u max_{e ∈ S} sim(u, e)
-- |
-- | Each user u gets utility from their most similar selected facility.
-- | Classic diminishing returns: adding facilities helps less as coverage grows.
-- |
-- | ### Quality-Weighted Coverage
-- |
-- | The council's design: q(s) = q_max · (1 - e^{-αs})
-- |
-- | Models UI widget quality as saturating function of "activation" s.
-- |
-- | ## Billion-Agent Context
-- |
-- | Agents select UI elements to maximize coverage of user needs:
-- | - Elements: buttons, cards, charts, etc.
-- | - Coverage: user tasks each element helps with
-- | - Weights: importance/frequency of each task
-- |
-- | Submodularity ensures diminishing returns: the 5th button adds less
-- | value than the 1st, preventing over-cluttered interfaces.
-- |
-- | ## References
-- |
-- | - Nemhauser, Wolsey, Fisher. "Analysis of Approximations for
-- |   Maximizing Submodular Set Functions" Math. Program. 1978
-- | - Krause, Golovin. "Submodular Function Maximization" 2014
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Types (core types)
-- | - Hydrogen.Math.Core (exp, log)

module Hydrogen.Optimize.Submodular.Oracle
  ( -- * Oracle Constructors
    mkCoverageOracle
  , mkWeightedCoverageOracle
  , mkFacilityLocationOracle
  , mkSaturatingQualityOracle
  
  -- * Coverage Helpers
  , CoverageSpec(CoverageSpec)
  , mkCoverageSpec
  , coverageNeighborhood
  
  -- * Facility Location Helpers
  , FacilitySpec(FacilitySpec)
  , mkFacilitySpec
  , facilitySimilarity
  
  -- * Quality Function
  , QualityParams(QualityParams)
  , mkQualityParams
  , qualityValue
  , qualityMarginal
  
  -- * Oracle Operations
  , evalOracle
  , marginalGainOracle
  , greedyMaximize
  , lazyGreedyMaximize
  
  -- * Oracle Composition
  , sumOracles
  , scaleOracle
  , restrictOracle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , compare
  , map
  , max
  , negate
  , not
  , (+)
  , (-)
  , (*)
  , (>=)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set (Set)
import Data.Set as Set
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple (Tuple(Tuple), fst, snd)

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Tensor.Dimension (dim)
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  , SubmodularOracle(SubmodularOracle)
  , SetValue(SetValue)
  , MarginalGain(MarginalGain)
  , class Matroid
  , canExtend
  , extensionElements
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // coverage oracle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coverage specification for a ground set.
-- |
-- | Each element e ∈ V has a neighborhood N(e) ⊆ U (universe of coverable items).
-- | The coverage function is f(S) = |⋃_{e ∈ S} N(e)|.
newtype CoverageSpec v = CoverageSpec
  { groundSet :: GroundSet v
  , universe :: Set Int                    -- ^ Universe U to cover
  , neighborhoods :: Map Int (Set Int)     -- ^ Element index → covered items
  }

derive instance eqCoverageSpec :: Eq (CoverageSpec v)

-- | Create a coverage specification.
mkCoverageSpec 
  :: forall v
   . GroundSet v 
  -> Set Int 
  -> Map Int (Set Int) 
  -> CoverageSpec v
mkCoverageSpec groundSet universe neighborhoods = CoverageSpec
  { groundSet
  , universe
  , neighborhoods
  }

-- | Get the neighborhood of an element.
coverageNeighborhood :: forall v. CoverageSpec v -> Element v -> Set Int
coverageNeighborhood (CoverageSpec { neighborhoods }) (Element i) =
  case Map.lookup i neighborhoods of
    Nothing -> Set.empty
    Just n -> n

-- | Create a coverage oracle.
-- |
-- | f(S) = |⋃_{e ∈ S} N(e)|
-- |
-- | This is a classic monotone submodular function.
mkCoverageOracle :: forall v. CoverageSpec v -> SubmodularOracle v
mkCoverageOracle spec@(CoverageSpec { groundSet, universe }) = SubmodularOracle
  { eval: evalCoverage spec
  , marginal: marginalCoverage spec
  , groundSet: groundSet
  , fMax: Just (SetValue (intToNumber (Set.size universe)))
  }
  where
    intToNumber :: Int -> Number
    intToNumber n = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 n)

-- | Evaluate coverage function.
evalCoverage :: forall v. CoverageSpec v -> ElementSet v -> SetValue
evalCoverage spec s =
  let covered = unionNeighborhoods spec s
  in SetValue (intToNum (Set.size covered))
  where
    intToNum :: Int -> Number
    intToNum n = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 n)

-- | Compute union of neighborhoods for a set of elements.
unionNeighborhoods :: forall v. CoverageSpec v -> ElementSet v -> Set Int
unionNeighborhoods spec s =
  let elements = Set.toUnfoldable s :: Array (Element v)
      neighborhoods = map (coverageNeighborhood spec) elements
  in foldl Set.union Set.empty neighborhoods

-- | Marginal gain for coverage function.
marginalCoverage :: forall v. CoverageSpec v -> Element v -> ElementSet v -> MarginalGain
marginalCoverage spec e s =
  let currentCovered = unionNeighborhoods spec s
      elementNeighborhood = coverageNeighborhood spec e
      newlyCovered = Set.difference elementNeighborhood currentCovered
  in MarginalGain (intToNum (Set.size newlyCovered))
  where
    intToNum :: Int -> Number
    intToNum n = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // weighted coverage oracle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a weighted coverage oracle.
-- |
-- | f(S) = Σ_{u ∈ ⋃_{e ∈ S} N(e)} w(u)
-- |
-- | Weighted coverage where each item u in the universe has weight w(u).
mkWeightedCoverageOracle 
  :: forall v
   . CoverageSpec v 
  -> Map Int Number      -- ^ Weights: item index → weight
  -> SubmodularOracle v
mkWeightedCoverageOracle spec@(CoverageSpec { groundSet, universe }) weights = 
  SubmodularOracle
    { eval: evalWeightedCoverage spec weights
    , marginal: marginalWeightedCoverage spec weights
    , groundSet: groundSet
    , fMax: Just (SetValue (totalWeight universe weights))
    }

-- | Total weight of a set of items.
totalWeight :: Set Int -> Map Int Number -> Number
totalWeight items weights =
  let itemArray = Set.toUnfoldable items :: Array Int
  in foldl (\acc i -> acc + lookupWeight i weights) 0.0 itemArray

-- | Look up weight, default to 1.0 if not found.
lookupWeight :: Int -> Map Int Number -> Number
lookupWeight i weights =
  case Map.lookup i weights of
    Nothing -> 1.0
    Just w -> w

-- | Evaluate weighted coverage.
evalWeightedCoverage 
  :: forall v
   . CoverageSpec v 
  -> Map Int Number 
  -> ElementSet v 
  -> SetValue
evalWeightedCoverage spec weights s =
  let covered = unionNeighborhoods spec s
  in SetValue (totalWeight covered weights)

-- | Marginal gain for weighted coverage.
marginalWeightedCoverage 
  :: forall v
   . CoverageSpec v 
  -> Map Int Number 
  -> Element v 
  -> ElementSet v 
  -> MarginalGain
marginalWeightedCoverage spec weights e s =
  let currentCovered = unionNeighborhoods spec s
      elementNeighborhood = coverageNeighborhood spec e
      newlyCovered = Set.difference elementNeighborhood currentCovered
  in MarginalGain (totalWeight newlyCovered weights)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // facility location oracle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Facility location specification.
-- |
-- | Users U and facilities F (which is the ground set V).
-- | Each user u has similarity sim(u, f) to each facility f.
-- | f(S) = Σ_u max_{f ∈ S} sim(u, f)
newtype FacilitySpec v = FacilitySpec
  { groundSet :: GroundSet v
  , users :: Set Int                       -- ^ User indices
  , similarities :: Map Int (Map Int Number)  -- ^ user → (facility → similarity)
  }

derive instance eqFacilitySpec :: Eq (FacilitySpec v)

-- | Create a facility location specification.
mkFacilitySpec 
  :: forall v
   . GroundSet v 
  -> Set Int 
  -> Map Int (Map Int Number) 
  -> FacilitySpec v
mkFacilitySpec groundSet users similarities = FacilitySpec
  { groundSet
  , users
  , similarities
  }

-- | Get similarity between a user and a facility.
facilitySimilarity :: forall v. FacilitySpec v -> Int -> Element v -> Number
facilitySimilarity (FacilitySpec { similarities }) user (Element facility) =
  case Map.lookup user similarities of
    Nothing -> 0.0
    Just facilityMap -> case Map.lookup facility facilityMap of
      Nothing -> 0.0
      Just sim -> sim

-- | Create a facility location oracle.
-- |
-- | f(S) = Σ_u max_{f ∈ S} sim(u, f)
-- |
-- | Classic monotone submodular function for facility/diversity selection.
mkFacilityLocationOracle :: forall v. FacilitySpec v -> SubmodularOracle v
mkFacilityLocationOracle spec@(FacilitySpec { groundSet }) = SubmodularOracle
  { eval: evalFacilityLocation spec
  , marginal: marginalFacilityLocation spec
  , groundSet: groundSet
  , fMax: Nothing  -- Depends on similarity matrix, not easily bounded
  }

-- | Evaluate facility location function.
evalFacilityLocation :: forall v. FacilitySpec v -> ElementSet v -> SetValue
evalFacilityLocation spec@(FacilitySpec { users }) s =
  let userArray = Set.toUnfoldable users :: Array Int
      userUtilities = map (userUtility spec s) userArray
  in SetValue (foldl (+) 0.0 userUtilities)

-- | Utility for a single user given selected facilities.
userUtility :: forall v. FacilitySpec v -> ElementSet v -> Int -> Number
userUtility spec s user =
  let facilities = Set.toUnfoldable s :: Array (Element v)
      sims = map (facilitySimilarity spec user) facilities
  in foldl max 0.0 sims

-- | Marginal gain for facility location.
marginalFacilityLocation 
  :: forall v
   . FacilitySpec v 
  -> Element v 
  -> ElementSet v 
  -> MarginalGain
marginalFacilityLocation spec@(FacilitySpec { users }) e s =
  let userArray = Set.toUnfoldable users :: Array Int
      gains = map (userMarginalGain spec e s) userArray
  in MarginalGain (foldl (+) 0.0 gains)

-- | Marginal gain for a single user.
userMarginalGain :: forall v. FacilitySpec v -> Element v -> ElementSet v -> Int -> Number
userMarginalGain spec e s user =
  let currentMax = userUtility spec s user
      newSim = facilitySimilarity spec user e
  in max 0.0 (newSim - currentMax)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // saturating quality oracle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quality function parameters (council design).
-- |
-- | q(s) = q_max · (1 - e^{-αs})
-- |
-- | Models UI element quality as a saturating function of "activation" s.
-- | - q_max: maximum achievable quality
-- | - α: rate of saturation (higher = faster saturation)
-- | - s: element activation/importance score
newtype QualityParams = QualityParams
  { qMax :: Number        -- ^ Maximum quality (bounded in [0, 1])
  , alpha :: Number       -- ^ Saturation rate (bounded in [0.001, 100])
  }

derive instance eqQualityParams :: Eq QualityParams

-- | Create quality parameters with bounds enforcement.
mkQualityParams :: Number -> Number -> QualityParams
mkQualityParams qMax alpha = QualityParams
  { qMax: Math.clamp 0.0 1.0 qMax
  , alpha: Math.clamp 0.001 100.0 alpha
  }

-- | Evaluate quality function: q(s) = q_max · (1 - e^{-αs})
qualityValue :: QualityParams -> Number -> Number
qualityValue (QualityParams { qMax, alpha }) s =
  qMax * (1.0 - Math.exp (negate alpha * s))

-- | Marginal quality from increasing activation by δ.
-- |
-- | q'(s) = q_max · α · e^{-αs}
qualityMarginal :: QualityParams -> Number -> Number -> Number
qualityMarginal (QualityParams { qMax, alpha }) s delta =
  qualityValue (QualityParams { qMax, alpha }) (s + delta) -
  qualityValue (QualityParams { qMax, alpha }) s

-- | Create a saturating quality oracle.
-- |
-- | Each element e has an activation score a(e).
-- | f(S) = Σ_{e ∈ S} q(a(e))
-- |
-- | The function becomes submodular when activations have diminishing returns
-- | (e.g., through interaction effects modeled externally).
mkSaturatingQualityOracle 
  :: forall v
   . GroundSet v 
  -> Map Int Number      -- ^ Element index → activation score
  -> QualityParams
  -> SubmodularOracle v
mkSaturatingQualityOracle groundSet activations params = SubmodularOracle
  { eval: evalSaturating activations params
  , marginal: marginalSaturating activations params
  , groundSet: groundSet
  , fMax: Nothing  -- Depends on number of elements
  }

-- | Evaluate saturating quality function.
evalSaturating 
  :: forall v
   . Map Int Number 
  -> QualityParams 
  -> ElementSet v 
  -> SetValue
evalSaturating activations params s =
  let elements = Set.toUnfoldable s :: Array (Element v)
      qualities = map (elementQuality activations params) elements
  in SetValue (foldl (+) 0.0 qualities)

-- | Quality of a single element.
elementQuality :: forall v. Map Int Number -> QualityParams -> Element v -> Number
elementQuality activations params (Element i) =
  let activation = case Map.lookup i activations of
        Nothing -> 0.0
        Just a -> a
  in qualityValue params activation

-- | Marginal gain for saturating quality (modular when no interactions).
marginalSaturating 
  :: forall v
   . Map Int Number 
  -> QualityParams 
  -> Element v 
  -> ElementSet v 
  -> MarginalGain
marginalSaturating activations params e _ =
  -- In pure modular form, marginal gain is just the element's quality
  MarginalGain (elementQuality activations params e)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // oracle operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate an oracle on a set.
evalOracle :: forall v. SubmodularOracle v -> ElementSet v -> SetValue
evalOracle (SubmodularOracle { eval }) s = eval s

-- | Compute marginal gain using the oracle.
marginalGainOracle :: forall v. SubmodularOracle v -> Element v -> ElementSet v -> MarginalGain
marginalGainOracle (SubmodularOracle { marginal }) e s = marginal e s

-- | Greedy maximization of a submodular function.
-- |
-- | Starting from the empty set, greedily adds the element with maximum
-- | marginal gain until the matroid constraint is saturated.
-- |
-- | For monotone submodular + matroid: achieves (1 - 1/e) approximation.
greedyMaximize 
  :: forall m v
   . Matroid m v
  => m 
  -> SubmodularOracle v 
  -> ElementSet v
greedyMaximize matroid oracle = greedyLoop matroid oracle Set.empty

-- | Greedy iteration loop.
greedyLoop 
  :: forall m v
   . Matroid m v
  => m 
  -> SubmodularOracle v 
  -> ElementSet v 
  -> ElementSet v
greedyLoop matroid oracle current =
  let candidates = extensionElements matroid current
      ranked = rankCandidates oracle current candidates
  in case Array.head ranked of
    Nothing -> current
    Just (Tuple _ bestElement) ->
      greedyLoop matroid oracle (Set.insert bestElement current)

-- | Rank candidates by marginal gain (descending).
rankCandidates 
  :: forall v
   . SubmodularOracle v 
  -> ElementSet v 
  -> Array (Element v) 
  -> Array (Tuple MarginalGain (Element v))
rankCandidates oracle current candidates =
  let withGains = map (\e -> Tuple (marginalGainOracle oracle e current) e) candidates
  in Array.sortBy (\a b -> compare (snd b) (snd a)) withGains

-- | Lazy greedy maximization with priority queue.
-- |
-- | Optimization: elements are re-evaluated only when they might be selected.
-- | Exploits submodularity: marginal gains only decrease.
-- |
-- | Same theoretical guarantee, often 10-100x faster in practice.
lazyGreedyMaximize 
  :: forall m v
   . Ord (Element v)
  => Matroid m v
  => m 
  -> SubmodularOracle v 
  -> ElementSet v
lazyGreedyMaximize matroid oracle@(SubmodularOracle { groundSet }) =
  let (GroundSet { elements }) = groundSet
      initial = initializeHeap oracle elements
  in lazyGreedyLoop matroid oracle Set.empty initial

-- | Initialize heap with all elements and their initial marginal gains.
initializeHeap 
  :: forall v
   . SubmodularOracle v 
  -> Array (Element v) 
  -> Array (Tuple MarginalGain (Element v))
initializeHeap oracle elements =
  let withGains = map (\e -> Tuple (marginalGainOracle oracle e Set.empty) e) elements
  in Array.sortBy (\a b -> compare (fst b) (fst a)) withGains  -- Descending

-- | Lazy greedy loop.
lazyGreedyLoop 
  :: forall m v
   . Ord (Element v)
  => Matroid m v
  => m 
  -> SubmodularOracle v 
  -> ElementSet v 
  -> Array (Tuple MarginalGain (Element v))
  -> ElementSet v
lazyGreedyLoop matroid oracle current heap =
  case Array.uncons heap of
    Nothing -> current
    Just { head: Tuple oldGain e, tail: rest } ->
      if not (canExtend matroid e current)
        then lazyGreedyLoop matroid oracle current rest  -- Skip, can't extend
        else
          let newGain = marginalGainOracle oracle e current
          in if newGain >= oldGain
               -- Gain hasn't decreased, select this element
               then lazyGreedyLoop matroid oracle 
                      (Set.insert e current) 
                      rest
               -- Gain decreased, reinsert with updated gain
               else lazyGreedyLoop matroid oracle current
                      (reinsertHeap (Tuple newGain e) rest)

-- | Reinsert element into heap maintaining descending order.
reinsertHeap 
  :: forall v
   . Tuple MarginalGain (Element v) 
  -> Array (Tuple MarginalGain (Element v))
  -> Array (Tuple MarginalGain (Element v))
reinsertHeap item heap =
  let insertPos = findInsertPos (fst item) heap 0
      before = Array.take insertPos heap
      after = Array.drop insertPos heap
  in before <> [item] <> after

-- | Find position to insert maintaining descending order.
findInsertPos :: forall v. MarginalGain -> Array (Tuple MarginalGain (Element v)) -> Int -> Int
findInsertPos gain heap idx =
  case Array.index heap idx of
    Nothing -> idx
    Just (Tuple g _) -> 
      if gain >= g then idx else findInsertPos gain heap (idx + 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // oracle composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum of two submodular oracles.
-- |
-- | (f + g)(S) = f(S) + g(S)
-- |
-- | Sum of submodular functions is submodular.
sumOracles :: forall v. SubmodularOracle v -> SubmodularOracle v -> SubmodularOracle v
sumOracles (SubmodularOracle o1) (SubmodularOracle o2) = SubmodularOracle
  { eval: \s ->
      let (SetValue v1) = o1.eval s
          (SetValue v2) = o2.eval s
      in SetValue (v1 + v2)
  , marginal: \e s ->
      let (MarginalGain g1) = o1.marginal e s
          (MarginalGain g2) = o2.marginal e s
      in MarginalGain (g1 + g2)
  , groundSet: o1.groundSet
  , fMax: case o1.fMax of
      Nothing -> Nothing
      Just (SetValue m1) -> case o2.fMax of
        Nothing -> Nothing
        Just (SetValue m2) -> Just (SetValue (m1 + m2))
  }

-- | Scale an oracle by a constant.
-- |
-- | (c · f)(S) = c · f(S)
-- |
-- | Scaling preserves submodularity for c > 0.
scaleOracle :: forall v. Number -> SubmodularOracle v -> SubmodularOracle v
scaleOracle c (SubmodularOracle o) = SubmodularOracle
  { eval: \s ->
      let (SetValue v) = o.eval s
      in SetValue (c * v)
  , marginal: \e s ->
      let (MarginalGain g) = o.marginal e s
      in MarginalGain (c * g)
  , groundSet: o.groundSet
  , fMax: map (\(SetValue m) -> SetValue (c * m)) o.fMax
  }

-- | Restrict oracle to a subset of the ground set.
-- |
-- | f|_T(S) = f(S ∩ T)
-- |
-- | Restriction preserves submodularity.
restrictOracle :: forall v. ElementSet v -> SubmodularOracle v -> SubmodularOracle v
restrictOracle restriction (SubmodularOracle o) = SubmodularOracle
  { eval: \s ->
      let restricted = Set.intersection s restriction
      in o.eval restricted
  , marginal: \e s ->
      if Set.member e restriction
        then o.marginal e (Set.intersection s restriction)
        else MarginalGain 0.0
  , groundSet: restrictGroundSet o.groundSet restriction
  , fMax: o.fMax  -- Upper bound still valid
  }

-- | Restrict ground set to subset.
restrictGroundSet :: forall v. GroundSet v -> ElementSet v -> GroundSet v
restrictGroundSet (GroundSet { elements }) restriction =
  let restricted = Array.filter (\e -> Set.member e restriction) elements
      newSize = Array.length restricted
  in GroundSet { size: dim newSize, elements: restricted }
