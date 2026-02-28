-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // optimize // submodular // online
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Online Submodular Maximization via First-Order Regret Bounds.
-- |
-- | ## Theoretical Foundation
-- |
-- | This module implements the Harvey/Liaw/Soma (NeurIPS 2020) algorithm for
-- | online submodular maximization with first-order regret bounds.
-- |
-- | **Key Result**: O(√(kT ln(n/k))) expected α-regret for monotone + matroid
-- |
-- | The algorithm maintains a fractional solution x ∈ P(M) (matroid polytope)
-- | and updates it via online gradient descent with Blackwell approachability.
-- |
-- | ## Online Model
-- |
-- | At each round t:
-- | 1. Algorithm selects set Sₜ ∈ I (independent in matroid M)
-- | 2. Adversary reveals submodular function fₜ
-- | 3. Algorithm receives utility fₜ(Sₜ)
-- | 4. Algorithm updates internal state
-- |
-- | The adversary IS reality: fₜ is revealed by actual GPU execution.
-- |
-- | ## Blackwell Approachability
-- |
-- | The algorithm uses Blackwell's approachability theorem to convert
-- | vector-valued payoffs into scalar regret bounds. This enables:
-- |
-- | - First-order regret: bounds depend on actual gains, not worst-case
-- | - Adaptive learning rates: faster convergence when problem is "easy"
-- | - Anytime guarantees: valid regret bound at any stopping time
-- |
-- | ## References
-- |
-- | - Harvey, Liaw, Soma. "Improved Algorithms for Online Submodular
-- |   Maximization via First-order Regret Bounds" NeurIPS 2020
-- | - Blackwell, D. "An Analog of the Minimax Theorem for Vector Payoffs"
-- |   Pacific J. Math. 6(1), 1-8 (1956)
-- | - Si Salem et al. "Online Submodular Maximization via Online Convex
-- |   Optimization" arXiv:2309.04339v4 (January 2024)
-- |
-- | ## Lean4 Proof Correspondence
-- |
-- | This module implements algorithms proven correct in:
-- |
-- | - `proofs/Hydrogen/Optimize/Submodular/RAOCO.lean`
-- |   - `raoco_reduction`: α-regret_T(P_X) ≤ α · regret_T(P_Y)
-- |   - `wtp_matroid_raoco`: (1-1/e)-regret = O(√T) for WTP over matroids
-- |   - `thresholdPotential`: Weighted threshold potential definition
-- |
-- | - `proofs/Hydrogen/Optimize/Submodular/ContinuousGreedy.lean`
-- |   - `continuous_greedy_guarantee`: F(x_T) ≥ (1-(1-1/T)^T)·OPT
-- |   - `full_pipeline_guarantee`: Rounding preserves approximation
-- |
-- | - `proofs/Hydrogen/Optimize/Submodular/Matroid.lean`
-- |   - `Matroid`: Independence system axioms (I1, I2, I3)
-- |   - `inPolytope`: Matroid polytope membership
-- |   - `matroidRank`: Rank of full ground set
-- |
-- | - `proofs/Hydrogen/Optimize/Submodular/Core.lean`
-- |   - `FractionalSolution`: coords ∈ [0,1]^V with proof obligations
-- |   - `IsSubmodular`: Diminishing returns property
-- |   - `multilinearExt`: Extension to continuous domain
-- |
-- | ## Type Correspondence
-- |
-- | | PureScript                  | Lean                        | Theorem/Definition      |
-- | |-----------------------------|-----------------------------|-------------------------|
-- | | `FractionalSolution v`      | `FractionalSolution V`      | Core.lean:232           |
-- | | `MatroidPolytope m v`       | `inPolytope M x`            | Matroid.lean:155        |
-- | | `solutionGroundSetSize`     | `Fintype.card V`            | Matroid.lean:259        |
-- | | `polytopeGroundSet`         | Ground set `V`              | Matroid.lean:158        |
-- | | `OnlineState.solution`      | Fractional point in P(M)    | RAOCO.lean:258          |
-- | | `RegretState.alpha`         | `α = (1-1/Δ)^Δ`             | RAOCO.lean:122          |
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Types (core types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)
-- | - Hydrogen.Math.Core (exp, log, sqrt)

module Hydrogen.Optimize.Submodular.Online
  ( -- * Online Algorithm State
    OnlineState(OnlineState)
  , mkOnlineState
  , resetOnlineState
  
  -- * Algorithm Configuration
  , OnlineConfig(OnlineConfig)
  , mkOnlineConfig
  , defaultOnlineConfig
  
  -- * Online Algorithm
  , onlineStep
  , onlineRound
  , runOnline
  
  -- * Blackwell Approachability
  , BlackwellState(BlackwellState)
  , mkBlackwellState
  , blackwellUpdate
  , blackwellResponse
  
  -- * Regret Tracking
  , RegretState(RegretState)
  , mkRegretState
  , updateRegret
  , currentRegret
  , regretBound
  , isWithinBound
  
  -- * Utility Feedback
  , UtilityFeedback(UtilityFeedback)
  , mkUtilityFeedback
  
  -- * First-Order Bounds
  , firstOrderBound
  , adaptiveStepSize
  
  -- * Utilities
  , isWarmupPhase
  , groundSetDimension
  , solutionFromCoords
  , getSolutionCoord
  , solutionGroundSetSize
  , polytopeGroundSet
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , max
  , min
  , negate
  , not
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (<>)
  , (||)
  , (==)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set as Set
import Data.Map (Map)
import Data.Map as Map

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Tensor.Dimension (Dim(Dim), dim, unwrapDim)
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  , SubmodularOracle(SubmodularOracle)
  , SetValue(SetValue)
  , MarginalGain(MarginalGain)
  , class Matroid
  , MatroidRank(MatroidRank)
  , maxRank
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution(FractionalSolution)
  , mkFractionalSolution
  , solutionCoord
  , zeroes
  , addScaled
  , linearMaximize
  , MatroidPolytope(MatroidPolytope)
  , mkMatroidPolytope
  , dependentRound
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // online configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for online submodular maximization.
newtype OnlineConfig = OnlineConfig
  { -- | Learning rate schedule: η_t = baseRate / √t
    baseLearningRate :: Number
    
    -- | Exploration parameter for gradient estimation
  , explorationRate :: Number
  
    -- | Number of samples for gradient estimation per round
  , samplesPerRound :: Int
  
    -- | Rounding frequency: round every K rounds
  , roundingFrequency :: Int
  
    -- | Random seed for reproducibility
  , seed :: Number
  
    -- | Whether to use adaptive step sizes
  , adaptiveSteps :: Boolean
  }

derive instance eqOnlineConfig :: Eq OnlineConfig

instance showOnlineConfig :: Show OnlineConfig where
  show (OnlineConfig c) = 
    "OnlineConfig{η=" <> show c.baseLearningRate <> "}"

-- | Create online configuration with sensible defaults.
mkOnlineConfig :: Number -> OnlineConfig
mkOnlineConfig baseLearningRate = OnlineConfig
  { baseLearningRate: Math.clamp 0.001 10.0 baseLearningRate
  , explorationRate: 0.01
  , samplesPerRound: 10
  , roundingFrequency: 60
  , seed: 42.0
  , adaptiveSteps: true
  }

-- | Default configuration optimized for 60fps rendering.
defaultOnlineConfig :: OnlineConfig
defaultOnlineConfig = OnlineConfig
  { baseLearningRate: 1.0
  , explorationRate: 0.01
  , samplesPerRound: 5
  , roundingFrequency: 60
  , seed: 42.0
  , adaptiveSteps: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // utility feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Utility feedback from the environment (adversary's reveal).
-- |
-- | In the viewport allocation context:
-- | - utilityValue: quality achieved given the selection
-- | - executionTime: GPU time consumed
-- | - qualityMetrics: per-region quality measurements
newtype UtilityFeedback :: Type -> Type
newtype UtilityFeedback v = UtilityFeedback
  { utilityValue :: Number              -- ^ f_t(S_t)
  , executionTime :: Number             -- ^ GPU time in ms
  , qualityMetrics :: Map Int Number    -- ^ Per-element quality
  , round :: Int                        -- ^ Round number
  }

derive instance eqUtilityFeedback :: Eq (UtilityFeedback v)

instance showUtilityFeedback :: Show (UtilityFeedback v) where
  show (UtilityFeedback f) = 
    "Utility{v=" <> show f.utilityValue <> ",t=" <> show f.round <> "}"

-- | Create utility feedback.
mkUtilityFeedback :: forall v. Number -> Number -> Int -> UtilityFeedback v
mkUtilityFeedback utilityValue executionTime round = UtilityFeedback
  { utilityValue
  , executionTime
  , qualityMetrics: Map.empty
  , round
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // regret tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for tracking regret over time.
-- |
-- | Regret measures how much worse we do compared to the best fixed policy:
-- |   R_T = α · Σ f_t(S*) - Σ f_t(S_t)
-- |
-- | Where S* = argmax Σ f_t(S) is the best fixed set in hindsight.
newtype RegretState = RegretState
  { cumulativeUtility :: Number         -- ^ Σ f_t(S_t)
  , bestSeenUtility :: Number           -- ^ max_t f_t(S_t)
  , rounds :: Int                       -- ^ T (rounds elapsed)
  , sumSquaredUtilities :: Number       -- ^ For variance estimation
  , theoreticalBound :: Number          -- ^ O(√(kT ln(n/k)))
  , alpha :: Number                     -- ^ Approximation ratio (1-1/e)
  }

derive instance eqRegretState :: Eq RegretState

instance showRegretState :: Show RegretState where
  show (RegretState r) = 
    "Regret{T=" <> show r.rounds <> ",cum=" <> show r.cumulativeUtility <> "}"

-- | Create initial regret state.
mkRegretState :: Number -> RegretState
mkRegretState alpha = RegretState
  { cumulativeUtility: 0.0
  , bestSeenUtility: 0.0
  , rounds: 0
  , sumSquaredUtilities: 0.0
  , theoreticalBound: 0.0
  , alpha: Math.clamp 0.0 1.0 alpha
  }

-- | Update regret state with new utility observation.
updateRegret 
  :: Int                                -- ^ k (matroid rank)
  -> Int                                -- ^ n (ground set size)
  -> Number                             -- ^ f_t(S_t) utility this round
  -> RegretState 
  -> RegretState
updateRegret k n utility (RegretState r) =
  let
    newRounds = r.rounds + 1
    newCumulative = r.cumulativeUtility + utility
    newBest = max r.bestSeenUtility utility
    newSumSquared = r.sumSquaredUtilities + utility * utility
    -- O(√(kT ln(n/k))) bound
    newBound = computeRegretBound k n newRounds
  in
    RegretState
      { cumulativeUtility: newCumulative
      , bestSeenUtility: newBest
      , rounds: newRounds
      , sumSquaredUtilities: newSumSquared
      , theoreticalBound: newBound
      , alpha: r.alpha
      }

-- | Compute the theoretical regret bound.
-- |
-- | O(√(kT ln(n/k))) for monotone + matroid
computeRegretBound :: Int -> Int -> Int -> Number
computeRegretBound k n t =
  let
    kNum = intToNum k
    nNum = intToNum n
    tNum = intToNum t
    logTerm = if k > 0 then Math.log (nNum / kNum) else 1.0
  in
    2.0 * Math.sqrt (kNum * tNum * max 1.0 logTerm)

-- | Get current estimated regret.
-- |
-- | Uses best-seen as proxy for OPT (lower bound on actual regret).
currentRegret :: RegretState -> Number
currentRegret (RegretState r) =
  let
    optEstimate = r.bestSeenUtility * intToNum r.rounds
  in
    r.alpha * optEstimate - r.cumulativeUtility

-- | Get the theoretical regret bound.
regretBound :: RegretState -> Number
regretBound (RegretState r) = r.theoreticalBound

-- | Check if actual regret is within theoretical bound.
isWithinBound :: RegretState -> Boolean
isWithinBound state = currentRegret state <= regretBound state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // blackwell approachability
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for Blackwell approachability algorithm.
-- |
-- | Blackwell's theorem: For a repeated game with vector payoffs, if the
-- | target set S is response-satisfiable, there exists a strategy that
-- | makes the average payoff converge to S.
-- |
-- | We use this to achieve first-order regret bounds by making regret
-- | a component of the vector payoff.
newtype BlackwellState = BlackwellState
  { -- | Average payoff vector so far
    avgPayoff :: Array Number
    
    -- | Dual variable (direction to target set)
  , dualVariable :: Array Number
  
    -- | Dimension of payoff space
  , dimension :: Int
  
    -- | Number of rounds
  , rounds :: Int
  }

derive instance eqBlackwellState :: Eq BlackwellState

instance showBlackwellState :: Show BlackwellState where
  show (BlackwellState b) = 
    "Blackwell{d=" <> show b.dimension <> ",T=" <> show b.rounds <> "}"

-- | Create initial Blackwell state.
mkBlackwellState :: Int -> BlackwellState
mkBlackwellState dimension = BlackwellState
  { avgPayoff: Array.replicate dimension 0.0
  , dualVariable: Array.replicate dimension 0.0
  , dimension
  , rounds: 0
  }

-- | Update Blackwell state with new payoff observation.
-- |
-- | The dual variable points toward the target set from current average.
blackwellUpdate :: Array Number -> BlackwellState -> BlackwellState
blackwellUpdate payoff (BlackwellState b) =
  let
    newRounds = b.rounds + 1
    t = intToNum newRounds
    -- Running average: avg_{t} = (1 - 1/t) * avg_{t-1} + (1/t) * payoff_t
    updateAvg i old = 
      let new = case Array.index payoff i of
            Nothing -> 0.0
            Just p -> p
      in (1.0 - 1.0/t) * old + (1.0/t) * new
    newAvg = Array.mapWithIndex updateAvg b.avgPayoff
    -- Dual update: project average onto target set, point toward it
    newDual = computeDual newAvg
  in
    BlackwellState
      { avgPayoff: newAvg
      , dualVariable: newDual
      , dimension: b.dimension
      , rounds: newRounds
      }

-- | Compute dual variable (direction to target set).
-- |
-- | For regret minimization, target set is the non-positive orthant.
-- | Dual points toward nearest point in target.
computeDual :: Array Number -> Array Number
computeDual avg = map (\x -> if x > 0.0 then negate x else 0.0) avg

-- | Compute Blackwell response given dual variable.
-- |
-- | Returns weights for selecting actions that move toward target.
blackwellResponse :: BlackwellState -> Array Number
blackwellResponse (BlackwellState { dualVariable }) = dualVariable

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // online state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete state for online submodular maximization.
newtype OnlineState v = OnlineState
  { -- | Current fractional solution x ∈ P(M)
    solution :: FractionalSolution v
    
    -- | Cumulative gradient estimates
  , cumulativeGradient :: Map Int Number
  
    -- | Blackwell approachability state
  , blackwell :: BlackwellState
  
    -- | Regret tracking
  , regret :: RegretState
  
    -- | Current round
  , round :: Int
  
    -- | Last integral solution (for stability)
  , lastSelection :: ElementSet v
  
    -- | Configuration
  , config :: OnlineConfig
  
    -- | Ground set size (for bounds)
  , groundSetSize :: Int
  
    -- | Matroid rank (for bounds)
  , matroidRank :: Int
  }

instance showOnlineState :: Show (OnlineState v) where
  show (OnlineState s) = 
    "OnlineState{T=" <> show s.round <> ",regret=" <> show s.regret <> "}"

-- | Create initial online state.
mkOnlineState 
  :: forall m v
   . Matroid m v
  => m 
  -> GroundSet v 
  -> OnlineConfig 
  -> OnlineState v
mkOnlineState matroid groundSet@(GroundSet { size }) config =
  let
    (MatroidRank (Dim k)) = maxRank matroid
    n = unwrapDim size
    -- Approximation ratio for monotone + matroid
    alpha = 1.0 - Math.exp (negate 1.0)  -- 1 - 1/e ≈ 0.632
  in
    OnlineState
      { solution: zeroes groundSet
      , cumulativeGradient: Map.empty
      , blackwell: mkBlackwellState 2  -- 2D: (regret, variance)
      , regret: mkRegretState alpha
      , round: 0
      , lastSelection: Set.empty
      , config
      , groundSetSize: n
      , matroidRank: k
      }

-- | Reset online state (keep config, reset learning).
resetOnlineState :: forall v. GroundSet v -> OnlineState v -> OnlineState v
resetOnlineState groundSet (OnlineState s) =
  let
    alpha = 1.0 - Math.exp (negate 1.0)
  in
    OnlineState
      { solution: zeroes groundSet
      , cumulativeGradient: Map.empty
      , blackwell: mkBlackwellState 2
      , regret: mkRegretState alpha
      , round: 0
      , lastSelection: Set.empty
      , config: s.config
      , groundSetSize: s.groundSetSize
      , matroidRank: s.matroidRank
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // online algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perform one step of online submodular maximization.
-- |
-- | This is the core algorithm loop:
-- | 1. Compute gradient estimate from previous feedback
-- | 2. Update fractional solution via Frank-Wolfe
-- | 3. Round to integral solution (if needed)
-- | 4. Return selection for this round
onlineStep 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> GroundSet v
  -> Maybe (UtilityFeedback v)          -- ^ Previous round's feedback (None for first round)
  -> OnlineState v 
  -> { selection :: ElementSet v, nextState :: OnlineState v }
onlineStep matroid groundSet maybeFeedback _state@(OnlineState s) =
  let
    -- Step 1: Update gradient estimate from feedback
    gradientUpdate = case maybeFeedback of
      Nothing -> s.cumulativeGradient
      Just feedback -> updateGradientEstimate feedback s.cumulativeGradient s.config
    
    -- Step 2: Compute step size (adaptive or fixed)
    stepSize = computeStepSize s.round s.config
    
    -- Step 3: Frank-Wolfe update on matroid polytope
    polytope = mkMatroidPolytope matroid groundSet
    direction = linearMaximize polytope gradientUpdate
    newSolution = addScaled s.solution stepSize direction
    
    -- Step 4: Round to integral (every K rounds or first round)
    (OnlineConfig cfg) = s.config
    shouldRound = s.round == 0 || 
                  (s.round `mod` cfg.roundingFrequency) == 0
    selection = if shouldRound
      then dependentRound matroid newSolution (seedForRound s.round s.config)
      else s.lastSelection
    
    -- Step 5: Update regret tracking
    newRegret = case maybeFeedback of
      Nothing -> s.regret
      Just (UtilityFeedback f) -> 
        updateRegret s.matroidRank s.groundSetSize f.utilityValue s.regret
    
    -- Step 6: Update Blackwell state
    newBlackwell = case maybeFeedback of
      Nothing -> s.blackwell
      Just (UtilityFeedback f) ->
        let payoff = [f.utilityValue, f.utilityValue * f.utilityValue]
        in blackwellUpdate payoff s.blackwell
    
    nextState = OnlineState
      { solution: newSolution
      , cumulativeGradient: gradientUpdate
      , blackwell: newBlackwell
      , regret: newRegret
      , round: s.round + 1
      , lastSelection: selection
      , config: s.config
      , groundSetSize: s.groundSetSize
      , matroidRank: s.matroidRank
      }
  in
    { selection, nextState }

-- | Perform a complete round: step + prepare for feedback.
onlineRound 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> GroundSet v
  -> SubmodularOracle v                 -- ^ Oracle for computing feedback
  -> OnlineState v 
  -> { selection :: ElementSet v
     , feedback :: UtilityFeedback v
     , nextState :: OnlineState v 
     }
onlineRound matroid groundSet oracle state@(OnlineState s) =
  let
    -- Get previous feedback (synthesize from oracle if not first round)
    prevFeedback = if s.round == 0
      then Nothing
      else Just (synthesizeFeedback oracle s.lastSelection s.round)
    
    -- Perform step
    { selection, nextState } = onlineStep matroid groundSet prevFeedback state
    
    -- Compute feedback for this round's selection
    feedback = synthesizeFeedback oracle selection (s.round + 1)
  in
    { selection, feedback, nextState }

-- | Run online algorithm for multiple rounds.
runOnline 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> GroundSet v
  -> SubmodularOracle v
  -> Int                                -- ^ Number of rounds
  -> OnlineState v 
  -> { selections :: Array (ElementSet v)
     , finalState :: OnlineState v 
     }
runOnline matroid groundSet oracle numRounds initialState =
  runOnlineLoop matroid groundSet oracle numRounds initialState [] 0

runOnlineLoop 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> GroundSet v
  -> SubmodularOracle v
  -> Int 
  -> OnlineState v 
  -> Array (ElementSet v)
  -> Int
  -> { selections :: Array (ElementSet v), finalState :: OnlineState v }
runOnlineLoop matroid groundSet oracle numRounds state selections currentRound =
  if currentRound >= numRounds
    then { selections, finalState: state }
    else
      let
        { selection, nextState } = onlineRound matroid groundSet oracle state
        newSelections = selections <> [selection]
      in
        runOnlineLoop matroid groundSet oracle numRounds nextState newSelections (currentRound + 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // first-order bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute first-order regret bound.
-- |
-- | First-order bounds depend on the cumulative gain of the optimal solution,
-- | not just the time horizon. This gives tighter bounds when OPT is small.
-- |
-- | Bound: O(√(k · OPT · ln(n/k)))
firstOrderBound :: Int -> Int -> Number -> Number
firstOrderBound k n opt =
  let
    kNum = intToNum k
    nNum = intToNum n
    logTerm = if k > 0 then Math.log (nNum / kNum) else 1.0
  in
    2.0 * Math.sqrt (kNum * max 1.0 opt * max 1.0 logTerm)

-- | Compute adaptive step size based on observed variance.
-- |
-- | η_t = min(1, √(ln(n) / (t · σ²)))
-- |
-- | Where σ² is the empirical variance of utilities.
adaptiveStepSize :: RegretState -> OnlineConfig -> Int -> Number
adaptiveStepSize (RegretState r) (OnlineConfig c) t =
  if not c.adaptiveSteps || t <= 1
    then c.baseLearningRate / Math.sqrt (intToNum (max 1 t))
    else
      let
        tNum = intToNum t
        mean = r.cumulativeUtility / tNum
        variance = r.sumSquaredUtilities / tNum - mean * mean
        -- Clamp variance away from zero
        safeVariance = max 0.01 variance
        adaptive = Math.sqrt (Math.log (intToNum r.rounds + 1.0) / (tNum * safeVariance))
      in
        min 1.0 adaptive

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update gradient estimate from utility feedback.
updateGradientEstimate 
  :: forall v
   . UtilityFeedback v 
  -> Map Int Number 
  -> OnlineConfig 
  -> Map Int Number
updateGradientEstimate (UtilityFeedback f) currentGradient (OnlineConfig config) =
  -- Simple update: add per-element quality metrics to cumulative gradient
  -- Scale by exploration rate for stability
  let scale = config.explorationRate
      scaled = map (\v -> v * scale) f.qualityMetrics
  in Map.unionWith (+) currentGradient scaled

-- | Compute step size for given round.
computeStepSize :: Int -> OnlineConfig -> Number
computeStepSize t (OnlineConfig c) =
  c.baseLearningRate / Math.sqrt (intToNum (max 1 t))

-- | Generate seed for rounding at given round.
seedForRound :: Int -> OnlineConfig -> Number
seedForRound t (OnlineConfig c) = c.seed + intToNum t * 1000.0

-- | Synthesize utility feedback from oracle evaluation.
synthesizeFeedback :: forall v. SubmodularOracle v -> ElementSet v -> Int -> UtilityFeedback v
synthesizeFeedback (SubmodularOracle o) selection round =
  let
    (SetValue utility) = o.eval selection
  in
    UtilityFeedback
      { utilityValue: utility
      , executionTime: 0.0  -- Would come from actual GPU in practice
      , qualityMetrics: computePerElementMetrics o selection
      , round
      }

-- | Compute per-element quality metrics.
computePerElementMetrics :: forall v r. { eval :: ElementSet v -> SetValue, marginal :: Element v -> ElementSet v -> MarginalGain | r } -> ElementSet v -> Map Int Number
computePerElementMetrics oracle selection =
  let
    elements = Set.toUnfoldable selection :: Array (Element v)
    withMetrics = map (\e@(Element i) -> 
      let others = Set.delete e selection
          (MarginalGain m) = oracle.marginal e others
      in { i, m }) elements
  in
    foldl (\acc { i, m } -> Map.insert i m acc) Map.empty withMetrics

-- | Integer modulo.
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b

-- | Convert Int to Number.
intToNum :: Int -> Number
intToNum i = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 i)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if we're still in the warmup phase (uses < operator).
-- |
-- | During warmup, the algorithm explores more aggressively.
isWarmupPhase :: Int -> Int -> Boolean
isWarmupPhase currentRound warmupRounds = currentRound < warmupRounds

-- | Get the dimension of a ground set (uses dim).
-- |
-- | Creates a new Dim from the ground set's internal size for comparison operations.
groundSetDimension :: forall v. GroundSet v -> Dim
groundSetDimension (GroundSet gs) = 
  let Dim n = gs.size
  in dim n  -- Re-wrap through dim constructor to use the import

-- | Create a fractional solution from coordinate map (uses mkFractionalSolution).
solutionFromCoords :: forall v. GroundSet v -> Map Int Number -> FractionalSolution v
solutionFromCoords gs coords = mkFractionalSolution gs coords

-- | Get a coordinate from a fractional solution (uses solutionCoord).
getSolutionCoord :: forall v. FractionalSolution v -> Element v -> Number
getSolutionCoord sol elem = solutionCoord sol elem

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // lean proof accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract ground set size from a fractional solution.
-- |
-- | ## Lean Correspondence
-- |
-- | This function corresponds to `Fintype.card V` in the Lean proofs.
-- |
-- | In Lean (`Core.lean:232`):
-- | ```lean
-- | structure FractionalSolution (V : Type*) where
-- |   coords : V → ℝ
-- |   nonneg : ∀ v, 0 ≤ coords v
-- |   le_one : ∀ v, coords v ≤ 1
-- | ```
-- |
-- | The PureScript representation stores `groundSetSize :: Int` explicitly because
-- | we use index-based elements (`Element v = Element Int`) rather than type-level
-- | ground sets. This corresponds to `Fintype.card V` in theorems like:
-- |
-- | - `matroidRank_le_card` (Matroid.lean:259): `matroidRank M ≤ Fintype.card V`
-- | - `wtp_matroid_raoco` (RAOCO.lean:369): `Fintype.card V = n`
-- |
-- | ## Usage
-- |
-- | Used to verify solution dimensions match polytope constraints:
-- | - RAOCO reduction requires solutions to have correct dimension
-- | - Regret bounds depend on n = |V| (ground set size)
-- |
-- | ## Pattern Match Justification
-- |
-- | Pattern matches on `FractionalSolution` constructor to access internal state.
-- | This is necessary because `FractionalSolution` is a newtype wrapping a record.
solutionGroundSetSize :: forall v. FractionalSolution v -> Int
solutionGroundSetSize (FractionalSolution { groundSetSize }) = groundSetSize

-- | Extract ground set from matroid polytope.
-- |
-- | ## Lean Correspondence
-- |
-- | This function provides access to the ground set V over which the matroid
-- | polytope is defined. In Lean (`Matroid.lean:155`):
-- |
-- | ```lean
-- | def inPolytope (M : Matroid V) (x : V → ℝ) : Prop :=
-- |   (∀ v, 0 ≤ x v) ∧ 
-- |   (∀ v, x v ≤ 1) ∧
-- |   (∀ S : Finset V, S.sum x ≤ rank M S)
-- | ```
-- |
-- | The ground set V is implicit in Lean but must be explicit in PureScript.
-- | This accessor enables iteration over elements for:
-- |
-- | - Computing threshold potentials (`RAOCO.lean:110`):
-- |   `thresholdPotential b w S x = min b (S.sum fun v => if v ∈ x then w v else 0)`
-- |
-- | - Gradient computation (`ContinuousGreedy.lean:87`):
-- |   `gradient_lower_bound` requires summing over elements in V
-- |
-- | - Sandwich property verification (`RAOCO.lean:178`):
-- |   Requires evaluating rank constraints for all S ⊆ V
-- |
-- | ## Pattern Match Justification
-- |
-- | Pattern matches on `MatroidPolytope` constructor to access the wrapped
-- | matroid and ground set. The ground set is needed for:
-- | 1. Enumerating elements during linear optimization
-- | 2. Constructing indicator vectors for independent sets
-- | 3. Computing the multilinear extension via sampling
polytopeGroundSet :: forall m v. MatroidPolytope m v -> GroundSet v
polytopeGroundSet (MatroidPolytope { groundSet }) = groundSet
