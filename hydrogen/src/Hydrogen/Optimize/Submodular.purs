-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // optimize // submodular
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Submodular Optimization for Viewport Resource Allocation.
-- |
-- | ## Overview
-- |
-- | This module provides a complete toolkit for submodular optimization,
-- | designed for real-time GPU resource allocation across viewport regions.
-- |
-- | At its core: given a budget (matroid constraint) and a quality function
-- | (submodular), find the allocation that maximizes total quality.
-- |
-- | ## Theoretical Foundation
-- |
-- | A set function f: 2^V → ℝ is **submodular** if it exhibits diminishing returns:
-- |
-- |   f(A ∪ {e}) - f(A) ≥ f(B ∪ {e}) - f(B)  for A ⊆ B
-- |
-- | This models realistic resource allocation where:
-- | - Adding compute to an already-detailed region helps less
-- | - Covering new regions provides higher marginal value
-- | - Quality saturates with increasing investment
-- |
-- | ## Matroid Constraints
-- |
-- | A matroid M = (V, I) captures feasibility constraints:
-- | - **Cardinality**: select at most k elements (budget constraint)
-- | - **Partition**: select at most one from each group (exclusivity)
-- | - **Uniform**: select exactly k elements (fixed allocation)
-- |
-- | For monotone submodular maximization subject to matroid constraints,
-- | the greedy algorithm achieves (1 - 1/e) ≈ 0.632 approximation.
-- |
-- | ## Online Setting
-- |
-- | In real-time rendering, we face an **online** problem:
-- | - Frame t: select allocation S_t
-- | - Reality reveals utility f_t(S_t) (actual render quality/time)
-- | - Update strategy for frame t+1
-- |
-- | The Harvey/Liaw/Soma (NeurIPS 2020) algorithm achieves:
-- |   O(√(kT ln(n/k))) first-order regret
-- |
-- | "First-order" means the bound scales with OPT, not worst-case.
-- |
-- | ## Module Structure
-- |
-- | - **Types**: Core type definitions (Element, GroundSet, Matroid, etc.)
-- | - **Oracle**: Submodular function constructors (coverage, facility location)
-- | - **Continuous**: Multilinear extension and continuous greedy
-- | - **Rounding**: Pipage and swap rounding for integral solutions
-- | - **Online**: Online algorithm with Blackwell approachability
-- |
-- | ## Billion-Agent Scale
-- |
-- | This module is designed for autonomous AI systems operating at scale:
-- | - Deterministic behavior: same inputs → same outputs
-- | - Bounded types: no invalid states
-- | - Pure functions: no hidden effects
-- | - Complete implementation: no stubs or TODOs
-- |
-- | ## References
-- |
-- | - Nemhauser, Wolsey, Fisher. "An Analysis of Approximations for
-- |   Maximizing Submodular Set Functions" Math. Prog. 1978
-- | - Calinescu et al. "Maximizing a Monotone Submodular Function Subject
-- |   to a Matroid Constraint" SICOMP 2011
-- | - Harvey, Liaw, Soma. "Improved Algorithms for Online Submodular
-- |   Maximization via First-order Regret Bounds" NeurIPS 2020

module Hydrogen.Optimize.Submodular
  ( -- * Re-exports from Types
    module Hydrogen.Optimize.Submodular.Types
    
    -- * Re-exports from Oracle
  , module Hydrogen.Optimize.Submodular.Oracle
  
    -- * Re-exports from Continuous
  , module Hydrogen.Optimize.Submodular.Continuous
  
    -- * Re-exports from Rounding
  , module Hydrogen.Optimize.Submodular.Rounding
  
    -- * Re-exports from Online
  , module Hydrogen.Optimize.Submodular.Online
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- | Core types: Element, GroundSet, Matroid, SubmodularOracle, etc.
import Hydrogen.Optimize.Submodular.Types
  ( -- Element types
    Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  
  -- Submodular values
  , SetValue(SetValue)
  , MarginalGain(MarginalGain)
  
  -- Monotonicity classification
  , Monotonicity(Monotone, NonMonotone)
  , Curvature(CurvatureUnknown, CurvatureBounded)
  , CurvatureWitness(CurvatureWitness)
  
  -- Submodular function
  , SubmodularFn
  , SubmodularOracle(SubmodularOracle)
  
  -- Matroid types
  , class Matroid
  , rank
  , maxRank
  , isIndependent
  , canExtend
  , extensionElements
  , MatroidRank(MatroidRank)
  , IndependentSet
  
  -- Matroid instances
  , CardinalityMatroid(CardinalityMatroid)
  , PartitionMatroid(PartitionMatroid)
  , PartitionBlock(PartitionBlock)
  , UniformMatroid(UniformMatroid)
  , GraphicMatroid(GraphicMatroid)
  
  -- Approximation types
  , ApproxRatio
  , AlphaRegret
  , MonotoneOPT
  , NonMonotoneOPT
  
  -- Online learning state
  , TimeHorizon(TimeHorizon)
  , Round(Round)
  , CumulativeGradient(CumulativeGradient)
  , DualVariable(DualVariable)
  , RegretBound(RegretBound)
  
  -- Graded monad
  , OnlineGrade(OnlineGrade)
  , OnlineLearn
  
  -- Blackwell approachability
  , TargetSet(TargetSet)
  , ResponseSet(ResponseSet)
  , PayoffVector(PayoffVector)
  
  -- Configuration
  , SamplingRate(SamplingRate)
  , StepSize(StepSize)
  , PiPage(DeterministicPipage, RandomizedPipage, ContiguousPipage, SwapPipage)
  )

-- | Oracle constructors for various submodular functions.
import Hydrogen.Optimize.Submodular.Oracle
  ( -- Coverage oracles
    mkCoverageOracle
  , mkWeightedCoverageOracle
  , CoverageSpec(CoverageSpec)
  , mkCoverageSpec
  , coverageNeighborhood
  
  -- Facility location
  , mkFacilityLocationOracle
  , FacilitySpec(FacilitySpec)
  , mkFacilitySpec
  , facilitySimilarity
  
  -- Quality functions
  , mkSaturatingQualityOracle
  , QualityParams(QualityParams)
  , mkQualityParams
  , qualityValue
  , qualityMarginal
  
  -- Oracle operations
  , evalOracle
  , marginalGainOracle
  
  -- Greedy algorithms
  , greedyMaximize
  , lazyGreedyMaximize
  
  -- Oracle combinators
  , sumOracles
  , scaleOracle
  , restrictOracle
  )

-- | Continuous relaxation and gradient-based optimization.
import Hydrogen.Optimize.Submodular.Continuous
  ( -- Fractional solutions
    FractionalSolution(FractionalSolution)
  , mkFractionalSolution
  , solutionValue
  , solutionCoord
  , solutionCoords
  , solutionSupport
  , zeroes
  , ones
  , uniform
  , addScaled
  
  -- Multilinear extension
  , MultilinearExt(MultilinearExt)
  , mkMultilinearExt
  , evalMultilinear
  , evalMultilinearSampled
  , partialDerivative
  , gradientSampled
  
  -- Matroid polytope
  , MatroidPolytope(MatroidPolytope)
  , mkMatroidPolytope
  , isInPolytope
  , linearMaximize
  
  -- Continuous greedy
  , ContinuousGreedyConfig(ContinuousGreedyConfig)
  , mkContinuousGreedyConfig
  , continuousGreedy
  , continuousGreedyStep
  
  -- Gradient estimation
  , GradientEstimate(GradientEstimate)
  , twoPointEstimate
  , coordinateGradient
  , stochasticGradient
  
  -- Basic rounding
  , sampleSolution
  , thresholdRound
  , dependentRound
  )

-- | Pipage and swap rounding for matroid-respecting integral solutions.
import Hydrogen.Optimize.Submodular.Rounding
  ( -- Pipage rounding
    PipageState(PipageState)
  , mkPipageState
  , pipageStep
  , pipageRound
  , fullPipageRound
  
  -- Swap rounding
  , SwapState(SwapState)
  , mkSwapState
  , swapStep
  , swapRound
  
  -- Contention resolution
  , ContentionScheme(ContentionScheme)
  , mkContentionScheme
  , resolveContention
  , correlatedContentionResolution
  
  -- Metrics
  , RoundingMetrics(RoundingMetrics)
  , mkRoundingMetrics
  , updateMetrics
  , roundingQuality
  
  -- Pairing utilities
  , PipagePair(PipagePair)
  , findPipagePair
  , pairTransferBounds
  
  -- Element classification
  , isFractional
  , fractionalElements
  , integralElements
  )

-- | Online submodular maximization with first-order regret bounds.
import Hydrogen.Optimize.Submodular.Online
  ( -- Online state
    OnlineState(OnlineState)
  , mkOnlineState
  , resetOnlineState
  
  -- Configuration
  , OnlineConfig(OnlineConfig)
  , mkOnlineConfig
  , defaultOnlineConfig
  
  -- Online algorithm
  , onlineStep
  , onlineRound
  , runOnline
  
  -- Blackwell approachability
  , BlackwellState(BlackwellState)
  , mkBlackwellState
  , blackwellUpdate
  , blackwellResponse
  
  -- Regret tracking
  , RegretState(RegretState)
  , mkRegretState
  , updateRegret
  , currentRegret
  , regretBound
  , isWithinBound
  
  -- Utility feedback
  , UtilityFeedback(UtilityFeedback)
  , mkUtilityFeedback
  
  -- First-order bounds
  , firstOrderBound
  , adaptiveStepSize
  )
