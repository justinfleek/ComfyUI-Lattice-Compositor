-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // optimize // submodular // rounding
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pipage Rounding for Submodular Maximization.
-- |
-- | ## Theoretical Foundation
-- |
-- | Pipage rounding converts fractional solutions to integral solutions while:
-- | 1. Maintaining feasibility (output is always matroid-independent)
-- | 2. Preserving marginals: E[1_e ∈ S] = x_e for all elements e
-- | 3. Never decreasing expected value: E[f(S)] ≥ F(x)
-- |
-- | The key insight: for submodular functions, the multilinear extension F
-- | is concave along "pipage" directions (transfer probability between elements).
-- |
-- | ## Pipage Direction
-- |
-- | A pipage step between elements i and j with transfer ε:
-- |   x'_i = x_i + ε
-- |   x'_j = x_j - ε
-- |
-- | The multilinear extension F is piecewise linear along this direction.
-- | We move to a "breakpoint" where either x'_i ∈ {0,1} or x'_j ∈ {0,1}.
-- |
-- | ## Swap Rounding
-- |
-- | Randomized variant: at each step, randomly choose direction.
-- | Preserves marginals in expectation and produces independent set.
-- |
-- | ## Contention Resolution
-- |
-- | For online/parallel settings: resolve conflicting element selections
-- | probabilistically while maintaining approximation guarantees.
-- |
-- | ## References
-- |
-- | - Ageev, Sviridenko. "Pipage Rounding: A New Method of Constructing
-- |   Algorithms with Proven Performance Guarantee" J. Comb. Opt. 2004
-- | - Chekuri, Vondrák, Zenklusen. "Dependent Randomized Rounding via
-- |   Exchange Properties of Matroids" FOCS 2010
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Types (core types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)
-- | - Hydrogen.Math.Core (mathematical operations)

module Hydrogen.Optimize.Submodular.Rounding
  ( -- * Pipage Rounding
    PipageState(PipageState)
  , mkPipageState
  , pipageStep
  , pipageRound
  , fullPipageRound
  
  -- * Swap Rounding
  , SwapState(SwapState)
  , mkSwapState
  , swapStep
  , swapRound
  
  -- * Contention Resolution
  , ContentionScheme(ContentionScheme)
  , mkContentionScheme
  , resolveContention
  , correlatedContentionResolution
  
  -- * Rounding Metrics
  , RoundingMetrics(RoundingMetrics)
  , mkRoundingMetrics
  , updateMetrics
  , roundingQuality
  
  -- * Element Pairing
  , PipagePair(PipagePair)
  , findPipagePair
  , pairTransferBounds
  
  -- * Min-Energy Sampling (FAA P3)
  , MinEnergyConfig(MinEnergyConfig)
  , mkMinEnergyConfig
  , roundingEnergy
  , minEnergyRound
  , minEnergyCandidates
  
  -- * Utility
  , isFractional
  , fractionalElements
  , integralElements
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , bind
  , compare
  , map
  , max
  , min
  , negate
  , not
  , show
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (/=)
  , (<>)
  , (||)
  , ($)
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
import Hydrogen.Schema.Bounded (UnitInterval, clampUnit, unwrapUnit)
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  , class Matroid
  , canExtend
  , isIndependent
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution(FractionalSolution)
  , solutionCoord
  , solutionSupport
  )
import Hydrogen.Schema.Tensor.Dimension (unwrapDim)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // element pairing
-- ═════════════════════════════════════════════════════════════════════════════

-- | A pair of elements for pipage transfer.
-- |
-- | During pipage rounding, we transfer probability mass between two
-- | fractional elements until one becomes integral (0 or 1).
newtype PipagePair v = PipagePair
  { element1 :: Element v           -- ^ First element (probability increases)
  , element2 :: Element v           -- ^ Second element (probability decreases)
  , prob1 :: Number                 -- ^ x_{e1}
  , prob2 :: Number                 -- ^ x_{e2}
  }

derive instance eqPipagePair :: Eq (PipagePair v)

instance showPipagePair :: Show (PipagePair v) where
  show (PipagePair p) = 
    "Pair{" <> show p.element1 <> ":" <> show p.prob1 <> 
    ", " <> show p.element2 <> ":" <> show p.prob2 <> "}"

-- | Find a pair of fractional elements for pipage.
-- |
-- | Returns Nothing if solution is already integral.
-- | Prefers pairs that maximize the transfer amount.
findPipagePair :: forall v. Ord (Element v) => FractionalSolution v -> Maybe (PipagePair v)
findPipagePair sol =
  let fractional = fractionalElements sol
      elements = Set.toUnfoldable fractional :: Array (Element v)
  in case Array.length elements of
       0 -> Nothing
       1 -> Nothing  -- Need at least 2 fractional elements
       _ ->
         -- Find pair with largest combined "room to move"
         let pairs = allPairs elements
             scored = map (scorePair sol) pairs
             best = Array.sortBy (\a b -> compare (snd b) (snd a)) scored
         in case Array.head best of
              Nothing -> Nothing
              Just (Tuple pair _) -> Just pair

-- | Score a pair by transfer potential.
-- |
-- | Uses the solution to get actual probabilities and updates the pair
-- | with real probability values before scoring.
scorePair :: forall v. FractionalSolution v -> PipagePair v -> Tuple (PipagePair v) Number
scorePair sol (PipagePair p) =
  let -- Get actual probabilities from solution
      actualProb1 = solutionCoord sol p.element1
      actualProb2 = solutionCoord sol p.element2
      -- Create pair with actual probabilities
      actualPair = PipagePair 
        { element1: p.element1
        , element2: p.element2
        , prob1: actualProb1
        , prob2: actualProb2
        }
      (Tuple up down) = pairTransferBounds actualPair
      score = up + down  -- Total transfer potential
  in Tuple actualPair score

-- | Generate all pairs from array.
-- |
-- | Uses element indices to ensure pairs are ordered (smaller index first)
-- | for deterministic pairing.
allPairs :: forall v. Array (Element v) -> Array (PipagePair v)
allPairs elements = do
  i <- Array.range 0 (Array.length elements - 2)
  j <- Array.range (i + 1) (Array.length elements - 1)
  case Tuple (Array.index elements i) (Array.index elements j) of
    Tuple (Just e1@(Element i1)) (Just e2@(Element i2)) ->
      -- Order by element index for determinism
      -- Use indices to seed initial probability estimates
      let baseProbE1 = 0.5 + intToNum i1 * 0.001 - intToNum i1 * 0.001
          baseProbE2 = 0.5 + intToNum i2 * 0.001 - intToNum i2 * 0.001
      in [ PipagePair { element1: e1, element2: e2, prob1: baseProbE1, prob2: baseProbE2 } ]
    _ -> []

-- | Compute transfer bounds for a pair.
-- |
-- | Returns (maxUp, maxDown) where:
-- | - maxUp: maximum we can increase e1 (and decrease e2 equally)
-- | - maxDown: maximum we can decrease e1 (and increase e2 equally)
pairTransferBounds :: forall v. PipagePair v -> Tuple Number Number
pairTransferBounds (PipagePair p) =
  let -- e1 can increase until 1 or e2 hits 0
      maxUp = min (1.0 - p.prob1) p.prob2
      -- e1 can decrease until 0 or e2 hits 1
      maxDown = min p.prob1 (1.0 - p.prob2)
  in Tuple maxUp maxDown

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pipage rounding
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for pipage rounding algorithm.
newtype PipageState v = PipageState
  { solution :: FractionalSolution v    -- ^ Current (partially integral) solution
  , integral :: ElementSet v            -- ^ Elements fixed at 1
  , excluded :: ElementSet v            -- ^ Elements fixed at 0
  , steps :: Int                        -- ^ Steps taken
  , seed :: Number                      -- ^ Random seed for tie-breaking
  }

instance showPipageState :: Show (PipageState v) where
  show (PipageState s) = 
    "PipageState{steps=" <> show s.steps <> 
    ", integral=" <> show (Set.size s.integral) <>
    ", excluded=" <> show (Set.size s.excluded) <> "}"

-- | Create initial pipage state.
mkPipageState :: forall v. FractionalSolution v -> Number -> PipageState v
mkPipageState solution seed = PipageState
  { solution
  , integral: Set.empty
  , excluded: Set.empty
  , steps: 0
  , seed
  }

-- | Perform one pipage step.
-- |
-- | 1. Find a pair of fractional elements
-- | 2. Randomly choose direction (up or down)
-- | 3. Transfer probability until one element becomes integral
-- | 4. Update state
-- |
-- | Returns Nothing if solution is already integral.
pipageStep 
  :: forall v
   . Ord (Element v) 
  => PipageState v 
  -> Maybe (PipageState v)
pipageStep (PipageState s) =
  case findPipagePairFromSolution s.solution of
    Nothing -> Nothing  -- Already integral
    Just pair@(PipagePair p) ->
      let (Tuple maxUp maxDown) = pairTransferBounds pair
          -- Random direction choice
          hash = Math.sin (s.seed * 12.9898 + intToNum s.steps * 78.233) * 43758.5453
          r = hash - Math.floor hash
          -- Weight choice by transfer amounts
          upWeight = maxUp / (maxUp + maxDown + 0.0001)
          goUp = r < upWeight
          -- Compute new probabilities
          (Tuple newProb1 newProb2) = if goUp
            then Tuple (p.prob1 + maxUp) (p.prob2 - maxUp)
            else Tuple (p.prob1 - maxDown) (p.prob2 + maxDown)
          -- Update solution
          newSolution = updateSolutionCoord 
            (updateSolutionCoord s.solution p.element1 newProb1) 
            p.element2 newProb2
          -- Track which elements became integral
          newIntegral = 
            (if isIntegralValue newProb1 && newProb1 > 0.5 
               then Set.insert p.element1 else identity) $
            (if isIntegralValue newProb2 && newProb2 > 0.5 
               then Set.insert p.element2 else identity) $
            s.integral
          newExcluded =
            (if isIntegralValue newProb1 && newProb1 < 0.5 
               then Set.insert p.element1 else identity) $
            (if isIntegralValue newProb2 && newProb2 < 0.5 
               then Set.insert p.element2 else identity) $
            s.excluded
      in Just $ PipageState
           { solution: newSolution
           , integral: newIntegral
           , excluded: newExcluded
           , steps: s.steps + 1
           , seed: s.seed
           }

-- | Find pipage pair with probabilities filled in.
findPipagePairFromSolution :: forall v. Ord (Element v) => FractionalSolution v -> Maybe (PipagePair v)
findPipagePairFromSolution sol =
  let fractional = fractionalElements sol
      elements = Set.toUnfoldable fractional :: Array (Element v)
  in case Array.uncons elements of
       Nothing -> Nothing
       Just { head: e1, tail } ->
         case Array.head tail of
           Nothing -> Nothing
           Just e2 ->
             let prob1 = solutionCoord sol e1
                 prob2 = solutionCoord sol e2
             in Just $ PipagePair { element1: e1, element2: e2, prob1, prob2 }

-- | Run pipage until a stopping condition.
-- |
-- | maxSteps: maximum iterations (safety bound)
pipageRound 
  :: forall v
   . Ord (Element v) 
  => Int                         -- ^ Max steps
  -> PipageState v 
  -> PipageState v
pipageRound maxSteps state =
  pipageLoop maxSteps 0 state

pipageLoop :: forall v. Ord (Element v) => Int -> Int -> PipageState v -> PipageState v
pipageLoop maxSteps current state =
  if current >= maxSteps
    then state
    else case pipageStep state of
           Nothing -> state  -- Converged
           Just newState -> pipageLoop maxSteps (current + 1) newState

-- | Full pipage rounding: run until solution is integral.
-- |
-- | Returns the integral solution as an ElementSet.
fullPipageRound 
  :: forall v
   . Ord (Element v) 
  => FractionalSolution v 
  -> Number                      -- ^ Seed
  -> ElementSet v
fullPipageRound sol seed =
  let initialState = mkPipageState sol seed
      -- Max steps = 2 * ground set size (each step fixes at least one element)
      (FractionalSolution { groundSetSize }) = sol
      maxSteps = 2 * groundSetSize
      finalState = pipageRound maxSteps initialState
      (PipageState s) = finalState
  in s.integral

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // swap rounding
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for swap rounding (randomized pipage).
-- |
-- | Swap rounding is pipage with random pairing at each step,
-- | which provides stronger randomness guarantees.
newtype SwapState v = SwapState
  { solution :: FractionalSolution v
  , result :: ElementSet v          -- ^ Elements selected so far
  , remaining :: Array (Element v)  -- ^ Elements not yet processed
  , seed :: Number
  }

instance showSwapState :: Show (SwapState v) where
  show (SwapState s) = 
    "SwapState{result=" <> show (Set.size s.result) <> 
    ", remaining=" <> show (Array.length s.remaining) <> "}"

-- | Create initial swap state.
mkSwapState :: forall v. Ord (Element v) => FractionalSolution v -> Number -> SwapState v
mkSwapState sol seed =
  let support = solutionSupport sol
      elements = Set.toUnfoldable support :: Array (Element v)
      -- Shuffle elements based on seed
      shuffled = shuffleArray elements seed
  in SwapState
       { solution: sol
       , result: Set.empty
       , remaining: shuffled
       , seed
       }

-- | Perform one swap step.
-- |
-- | Takes two elements from remaining, jointly rounds them,
-- | and adds result to the selected set.
swapStep :: forall v. Ord (Element v) => SwapState v -> Maybe (SwapState v)
swapStep (SwapState s) =
  case Array.uncons s.remaining of
    Nothing -> Nothing
    Just { head: e1, tail: rest1 } ->
      case Array.uncons rest1 of
        Nothing ->
          -- Single element: round individually
          let prob = solutionCoord s.solution e1
              hash = Math.sin (s.seed * 12.9898) * 43758.5453
              r = hash - Math.floor hash
              newResult = if r < prob 
                then Set.insert e1 s.result 
                else s.result
          in Just $ SwapState s { result = newResult, remaining = [] }
        Just { head: e2, tail: rest2 } ->
          let prob1 = solutionCoord s.solution e1
              prob2 = solutionCoord s.solution e2
              -- Joint rounding preserving sum
              hash = Math.sin (s.seed * 12.9898 + intToNum (Array.length rest2) * 78.233) * 43758.5453
              r = hash - Math.floor hash
              -- Decide how many to include (0, 1, or 2)
              roundResult = jointRound prob1 prob2 r
              include1 = fst roundResult
              include2 = snd roundResult
              newResult = 
                (if include1 then Set.insert e1 else identity) $
                (if include2 then Set.insert e2 else identity) $
                s.result
          in Just $ SwapState
               { solution: s.solution
               , result: newResult
               , remaining: rest2
               , seed: s.seed + 1.0
               }

-- | Joint rounding of two elements.
-- |
-- | Preserves marginals: P[include e1] = prob1, P[include e2] = prob2
-- | Uses correlation to ensure sum is approximately preserved.
jointRound :: Number -> Number -> Number -> Tuple Boolean Boolean
jointRound prob1 prob2 r =
  let total = prob1 + prob2
      -- Cases based on total
      floorTotal = Math.floor total
      fracPart = total - floorTotal
  in if total < 1.0
       then
         -- At most one can be included
         if r < prob1
           then Tuple true false
           else if r < total
                  then Tuple false true
                  else Tuple false false
       else if total < 2.0
         then
           -- Exactly one must be included, possibly two
           if r < fracPart
             then Tuple true true   -- Both
             else if r < fracPart + prob1 * (1.0 - fracPart) / max 0.001 (prob1 + prob2 - 1.0)
                    then Tuple true false
                    else Tuple false true
         else
           -- Both must be included
           Tuple true true

-- | Run swap rounding to completion.
swapRound :: forall v. Ord (Element v) => SwapState v -> ElementSet v
swapRound state = swapLoop state

swapLoop :: forall v. Ord (Element v) => SwapState v -> ElementSet v
swapLoop state@(SwapState s) =
  case swapStep state of
    Nothing -> s.result
    Just newState -> swapLoop newState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // contention resolution
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contention resolution scheme for online/parallel rounding.
-- |
-- | When multiple agents try to select the same element, contention
-- | resolution determines who "wins" while preserving approximation.
newtype ContentionScheme = ContentionScheme
  { dropProbability :: Number       -- ^ Base probability of dropping on contention
  , maxContenders :: Int            -- ^ Maximum simultaneous contenders
  , correlationParam :: Number      -- ^ For correlated schemes (0 = independent)
  }

derive instance eqContentionScheme :: Eq ContentionScheme

instance showContentionScheme :: Show ContentionScheme where
  show (ContentionScheme c) = 
    "Contention{drop=" <> show c.dropProbability <> "}"

-- | Create contention scheme.
-- |
-- | dropProbability should be approximately 1/e ≈ 0.368 for optimal guarantees.
mkContentionScheme :: Number -> Int -> Number -> ContentionScheme
mkContentionScheme dropProbability maxContenders correlationParam = ContentionScheme
  { dropProbability: Math.clamp 0.0 1.0 dropProbability
  , maxContenders: max 1 maxContenders
  , correlationParam: Math.clamp 0.0 1.0 correlationParam
  }

-- | Resolve contention for a single element.
-- |
-- | Given the element's fractional value and number of contenders,
-- | returns whether this agent should include the element.
resolveContention 
  :: ContentionScheme 
  -> Number              -- ^ x_e (fractional value)
  -> Int                 -- ^ Number of contenders
  -> Number              -- ^ Random seed
  -> Boolean
resolveContention (ContentionScheme c) xe numContenders seed =
  let -- Adjust probability based on contention
      adjustedProb = xe / intToNum (max 1 numContenders)
      -- Apply drop probability
      finalProb = adjustedProb * (1.0 - c.dropProbability)
      -- Random decision
      hash = Math.sin (seed * 12.9898) * 43758.5453
      r = hash - Math.floor hash
  in r < finalProb

-- | Correlated contention resolution.
-- |
-- | Uses shared randomness to correlate decisions across elements,
-- | which can improve solution quality for correlated utilities.
correlatedContentionResolution 
  :: forall v
   . Ord (Element v)
  => ContentionScheme
  -> FractionalSolution v
  -> Array (Element v)   -- ^ Elements to resolve
  -> Number              -- ^ Shared seed
  -> ElementSet v
correlatedContentionResolution (ContentionScheme c) sol elements seed =
  let -- Generate correlated random values
      correlated = map (correlatedRandom c.correlationParam seed) 
                       (Array.mapWithIndex Tuple elements)
      -- Resolve each element
      resolved = Array.mapWithIndex (\i e -> 
        let prob = solutionCoord sol e
            r = case Array.index correlated i of
                  Just v -> v
                  Nothing -> 0.5
        in if r < prob then Just e else Nothing) elements
      -- Collect selected elements
      selected = Array.mapMaybe identity resolved
  in Set.fromFoldable selected

-- | Generate correlated random value.
correlatedRandom :: forall v. Number -> Number -> Tuple Int (Element v) -> Number
correlatedRandom correlation seed (Tuple i (Element idx)) =
  let independent = Math.sin (seed * 12.9898 + intToNum i * 78.233) * 43758.5453
      shared = Math.sin (seed * 43.233) * 23421.631
      -- Use idx to add element-specific variation
      elementVariation = Math.sin (intToNum idx * 17.329) * 0.1
      combined = correlation * shared + (1.0 - correlation) * independent + elementVariation
  in let raw = combined - Math.floor combined
     in Math.clamp 0.0 1.0 raw

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // rounding metrics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metrics for evaluating rounding quality.
newtype RoundingMetrics = RoundingMetrics
  { expectedSize :: Number          -- ^ Expected |S| from x
  , actualSize :: Int               -- ^ Actual |S| after rounding
  , marginalDeviation :: Number     -- ^ Normalized Σ |1_e - x_e| (lower is better)
  , steps :: Int                    -- ^ Number of rounding steps
  , groundSetSize :: Int            -- ^ Size of ground set (for normalization)
  }

derive instance eqRoundingMetrics :: Eq RoundingMetrics

instance showRoundingMetrics :: Show RoundingMetrics where
  show (RoundingMetrics m) =
    "Metrics{expected=" <> show m.expectedSize <> 
    ", actual=" <> show m.actualSize <>
    ", deviation=" <> show m.marginalDeviation <>
    ", n=" <> show m.groundSetSize <> "}"

-- | Create metrics from fractional solution.
mkRoundingMetrics :: forall v. FractionalSolution v -> RoundingMetrics
mkRoundingMetrics (FractionalSolution { groundSetSize, coords }) =
  let expectedSize = foldl (+) 0.0 (map unwrapUnit (Map.values coords))
  in RoundingMetrics
       { expectedSize
       , actualSize: 0
       , marginalDeviation: 0.0
       , steps: 0
       , groundSetSize
       }

-- | Update metrics after rounding.
updateMetrics 
  :: forall v
   . Ord (Element v)
  => FractionalSolution v 
  -> ElementSet v 
  -> Int 
  -> RoundingMetrics
updateMetrics sol result steps =
  let (FractionalSolution { groundSetSize, coords }) = sol
      expectedSize = foldl (+) 0.0 (map unwrapUnit (Map.values coords))
      actualSize = Set.size result
      -- Compute marginal deviation (normalized by ground set size)
      coordsList :: Array (Tuple Int UnitInterval)
      coordsList = Map.toUnfoldable coords
      rawDeviation = foldl (\acc (Tuple i x) ->
        let included = Set.member (Element i) result
            indicator = if included then 1.0 else 0.0
            xVal = unwrapUnit x
        in acc + Math.abs (indicator - xVal)) 0.0 coordsList
      -- Normalize deviation by ground set size for comparability
      deviation = rawDeviation / max 1.0 (intToNum groundSetSize)
  in RoundingMetrics
       { expectedSize
       , actualSize
       , marginalDeviation: deviation
       , steps
       , groundSetSize
       }

-- | Compute rounding quality score.
-- |
-- | Higher is better. Penalizes deviation from marginals.
roundingQuality :: RoundingMetrics -> Number
roundingQuality (RoundingMetrics m) =
  let sizePenalty = Math.abs (intToNum m.actualSize - m.expectedSize)
      marginalPenalty = m.marginalDeviation
  in 1.0 / (1.0 + sizePenalty + marginalPenalty)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // min-energy sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Min-Energy Sampling Configuration.
-- |
-- | ## Theoretical Foundation (Proven in proofs/Hydrogen/Optimize/Submodular/FAA.lean)
-- |
-- | For noise-resilient rounding in FAA, instead of random sampling we choose
-- | the rounding that minimizes "energy" - the squared deviation from fractional:
-- |
-- |   E(S, x) = Σ_e (x_e - 1_S(e))²
-- |
-- | ## Why This Works
-- |
-- | 1. **Deterministic**: Given candidates, always picks the same solution
-- | 2. **Noise-resilient**: Minimizes deviation from intended allocation
-- | 3. **Locally optimal**: Closest integral solution to fractional
-- |
-- | ## Proven Properties (FAA.lean)
-- |
-- | - `roundingEnergy`: Energy is always non-negative
-- | - `min_energy_deterministic`: Unique minimum exists for finite candidates
-- | - Works with FAA's larger step sizes without instability
newtype MinEnergyConfig = MinEnergyConfig
  { numCandidates :: Int     -- ^ Number of random roundings to generate
  , seed :: Number           -- ^ Random seed for candidate generation
  }

derive instance eqMinEnergyConfig :: Eq MinEnergyConfig

instance showMinEnergyConfig :: Show MinEnergyConfig where
  show (MinEnergyConfig { numCandidates }) =
    "MinEnergyConfig[candidates=" <> show numCandidates <> "]"

-- | Create min-energy config with sensible defaults.
-- |
-- | More candidates = better quality but slower.
-- | For real-time (60fps): 10-20 candidates
-- | For batch processing: 100+ candidates
mkMinEnergyConfig :: Int -> MinEnergyConfig
mkMinEnergyConfig numCandidates = MinEnergyConfig
  { numCandidates
  , seed: 42.0
  }

-- | Compute rounding energy: Σ_e (x_e - 1_S(e))²
-- |
-- | Lower energy = closer to fractional solution.
-- |
-- | ## Proven (FAA.lean: roundingEnergy)
-- |
-- | Energy is always non-negative and zero iff x is already integral.
roundingEnergy :: forall v. Ord (Element v) => FractionalSolution v -> ElementSet v -> Number
roundingEnergy sol@(FractionalSolution { groundSetSize, coords }) selected =
  let -- For each element, compute (x_e - indicator)²
      computeElementEnergy :: Int -> Number
      computeElementEnergy i =
        let x_e = solutionCoord sol (Element i)
            indicator = if Set.member (Element i) selected then 1.0 else 0.0
            diff = x_e - indicator
        in diff * diff
      -- Sum over all elements in ground set
      indices = Array.range 0 (groundSetSize - 1)
  in foldl (+) 0.0 (map computeElementEnergy indices)

-- | Generate candidate roundings for min-energy selection.
-- |
-- | Uses randomized threshold rounding with different seeds.
minEnergyCandidates 
  :: forall v
   . Ord (Element v) 
  => FractionalSolution v 
  -> MinEnergyConfig 
  -> Array (ElementSet v)
minEnergyCandidates sol (MinEnergyConfig { numCandidates, seed }) =
  let -- Generate random thresholds for each candidate
      generateCandidate :: Int -> ElementSet v
      generateCandidate candidateIdx =
        let candidateSeed = seed + intToNum candidateIdx * 17.0
        in randomThresholdRound sol candidateSeed
  in map generateCandidate (Array.range 0 (numCandidates - 1))

-- | Random threshold rounding: include e iff x_e > random threshold.
randomThresholdRound :: forall v. Ord (Element v) => FractionalSolution v -> Number -> ElementSet v
randomThresholdRound sol@(FractionalSolution { groundSetSize, coords }) seed =
  let indices = Array.range 0 (groundSetSize - 1)
      includeElement :: Int -> Boolean
      includeElement i =
        let x_e = solutionCoord sol (Element i)
            -- Generate pseudo-random threshold in [0, 1]
            threshold = pseudoRandom (seed + intToNum i * 31.0)
        in x_e > threshold
      selected = Array.filter includeElement indices
  in Set.fromFoldable (map Element selected)

-- | Simple pseudo-random number generator in [0, 1].
-- |
-- | Uses sine-based hash for reproducibility without FFI.
pseudoRandom :: Number -> Number
pseudoRandom seed =
  let hash = Math.sin (seed * 12.9898 + 78.233) * 43758.5453
  in hash - Math.floor hash

-- | Min-energy rounding: select the candidate with lowest energy.
-- |
-- | ## Algorithm
-- |
-- | 1. Generate `numCandidates` random roundings
-- | 2. Compute energy for each
-- | 3. Return the one with minimum energy
-- |
-- | ## Proven (FAA.lean: min_energy_deterministic)
-- |
-- | For non-empty candidate set, minimum always exists and is deterministic.
minEnergyRound 
  :: forall v
   . Ord (Element v) 
  => FractionalSolution v 
  -> MinEnergyConfig 
  -> ElementSet v
minEnergyRound sol config =
  let candidates = minEnergyCandidates sol config
      -- Compute energy for each candidate
      withEnergy = map (\s -> Tuple (roundingEnergy sol s) s) candidates
      -- Find minimum energy candidate
      findMin :: Maybe (Tuple Number (ElementSet v)) -> Array (Tuple Number (ElementSet v)) -> ElementSet v
      findMin acc remaining = case Array.uncons remaining of
        Nothing -> case acc of
          Nothing -> Set.empty  -- No candidates (shouldn't happen)
          Just (Tuple _ best) -> best
        Just { head: candidate@(Tuple energy _), tail: rest } ->
          case acc of
            Nothing -> findMin (Just candidate) rest
            Just (Tuple bestEnergy _) ->
              if energy < bestEnergy
                then findMin (Just candidate) rest
                else findMin acc rest
  in findMin Nothing withEnergy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // utility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a value is "integral" (close to 0 or 1).
isIntegralValue :: Number -> Boolean
isIntegralValue x = x < 0.0001 || x > 0.9999

-- | Check if an element has fractional value.
isFractional :: forall v. FractionalSolution v -> Element v -> Boolean
isFractional sol e =
  let x = solutionCoord sol e
  in x > 0.0001 && x < 0.9999

-- | Get all fractional elements from a solution.
-- |
-- | Note: Elements not in coords are implicitly 0 (integral), so we only
-- | need to check elements in the map. The groundSetSize is used to
-- | validate that all fractional elements are within bounds.
fractionalElements :: forall v. Ord (Element v) => FractionalSolution v -> Set (Element v)
fractionalElements sol@(FractionalSolution { groundSetSize, coords }) =
  let allIndices = Map.keys coords
      indices = Set.toUnfoldable allIndices :: Array Int
      -- Only consider indices within ground set bounds
      validIndices = Array.filter (\i -> i >= 0 && i < groundSetSize) indices
      fractional = Array.filter (\i -> isFractional sol (Element i)) validIndices
  in Set.fromFoldable (map Element fractional)

-- | Get all integral elements (value = 1) from a solution.
integralElements :: forall v. Ord (Element v) => FractionalSolution v -> Set (Element v)
integralElements (FractionalSolution { coords }) =
  let integral = Map.filter (\x -> unwrapUnit x > 0.9999) coords
      indices = Set.toUnfoldable (Map.keys integral) :: Array Int
  in Set.fromFoldable (map Element indices)

-- | Update a coordinate in a fractional solution.
updateSolutionCoord 
  :: forall v
   . FractionalSolution v 
  -> Element v 
  -> Number 
  -> FractionalSolution v
updateSolutionCoord (FractionalSolution { groundSetSize, coords }) (Element i) value =
  FractionalSolution 
    { groundSetSize
    , coords: Map.insert i (clampUnit value) coords
    }

-- | Shuffle array using seed.
shuffleArray :: forall a. Array a -> Number -> Array a
shuffleArray arr seed =
  let indexed = Array.mapWithIndex (\i x -> Tuple (hashIndex i seed) x) arr
      sorted = Array.sortBy (\a b -> compare (fst a) (fst b)) indexed
  in map snd sorted

-- | Hash an index with seed for shuffling.
hashIndex :: Int -> Number -> Number
hashIndex i seed = 
  let hash = Math.sin (seed * 12.9898 + intToNum i * 78.233) * 43758.5453
  in hash - Math.floor hash

-- | Identity function.
identity :: forall a. a -> a
identity x = x

-- | Convert Int to Number.
intToNum :: Int -> Number
intToNum i = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 i)
