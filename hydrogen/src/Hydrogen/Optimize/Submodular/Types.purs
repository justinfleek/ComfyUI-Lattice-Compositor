-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // optimize // submodular // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Type System for Online Submodular Maximization.
-- |
-- | ## Theoretical Foundation
-- |
-- | This module implements the type-theoretic foundation for Harvey/Liaw/Soma's
-- | online submodular maximization algorithm (NeurIPS 2020). The key result:
-- |
-- | **O(√(kT ln(n/k))) first-order regret for monotone + matroid constraint**
-- |
-- | Where:
-- | - k = rank of matroid (max independent set size)
-- | - T = time horizon (number of rounds)
-- | - n = ground set size
-- |
-- | ## Design Philosophy
-- |
-- | Submodularity is the discrete analog of concavity. A function f : 2^V → ℝ
-- | is submodular iff for all A ⊆ B and e ∉ B:
-- |
-- |   f(A ∪ {e}) - f(A) ≥ f(B ∪ {e}) - f(B)
-- |
-- | This is the **diminishing returns** property: adding an element to a smaller
-- | set gives at least as much gain as adding it to a larger set.
-- |
-- | We encode this property directly in the type system using phantom types
-- | that track monotonicity, curvature bounds, and approximation ratios.
-- |
-- | ## Billion-Agent Context
-- |
-- | At billion-agent swarm scale, submodular optimization enables:
-- | - **Widget allocation**: Select k UI components maximizing engagement
-- | - **Attention routing**: Choose which elements get rendered first
-- | - **Resource scheduling**: Allocate compute across rendering tasks
-- | - **Feature selection**: Pick which brand atoms to include in design
-- |
-- | Each agent must reach the same decision given the same state. The type
-- | system guarantees this by making approximation ratios explicit.
-- |
-- | ## Module Structure
-- |
-- | This module exports TYPES ONLY. Implementation in separate modules.
-- |
-- | ## References
-- |
-- | - Harvey, Liaw, Soma. "Improved Online Submodular Maximization"
-- |   NeurIPS 2020, arXiv:2007.09231
-- | - Blackwell, D. "An analog of the minimax theorem for vector payoffs"
-- |   Pacific J. Math. 6(1), 1-8 (1956)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Bounded (bounded types)
-- | - Hydrogen.Schema.Tensor.Dimension (dimension atoms)

module Hydrogen.Optimize.Submodular.Types
  ( -- * Ground Set Elements
    Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  
  -- * Submodular Function Classification
  , Monotonicity(..)
  , Curvature(..)
  , CurvatureWitness(CurvatureWitness)
  
  -- * Core Submodular Function Type
  , SubmodularFn
  , SubmodularOracle(SubmodularOracle)
  , MarginalGain(MarginalGain)
  , SetValue(SetValue)
  
  -- * Matroid Constraints
  , class Matroid
  , rank
  , maxRank
  , isIndependent
  , canExtend
  , extensionElements
  , MatroidRank(MatroidRank)
  , IndependentSet
  , CardinalityMatroid(CardinalityMatroid)
  , PartitionMatroid(PartitionMatroid)
  , PartitionBlock(PartitionBlock)
  , UniformMatroid(UniformMatroid)
  , GraphicMatroid(GraphicMatroid)
  
  -- * Approximation Ratios (Phantom Types)
  , ApproxRatio
  , AlphaRegret
  , MonotoneOPT
  , NonMonotoneOPT
  
  -- * Online Learning State
  , TimeHorizon(TimeHorizon)
  , Round(Round)
  , CumulativeGradient(CumulativeGradient)
  , DualVariable(DualVariable)
  , RegretBound(RegretBound)
  
  -- * Graded Monad for Online Learning
  , OnlineGrade(..)
  , OnlineLearn
  
  -- * Blackwell Approachability
  , TargetSet(TargetSet)
  , ResponseSet(ResponseSet)
  , PayoffVector(PayoffVector)
  
  -- * Algorithm Configuration
  , SamplingRate(SamplingRate)
  , StepSize(StepSize)
  , PiPage(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , class Semiring
  , map
  , min
  , not
  , show
  , (<>)
  , (==)
  , (<=)
  , (<)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (&&)
  )

import Data.Array as Array
import Data.Foldable (foldl, any, all)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set (Set)
import Data.Set as Set
import Data.Map (Map)

import Hydrogen.Schema.Tensor.Dimension (Dim(Dim), unwrapDim)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // ground set elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | An element in the ground set V.
-- |
-- | Elements are uniquely identified by an index in [0, n-1] where n = |V|.
-- | The phantom type 'v' ties the element to its ground set.
-- |
-- | The kind of `v` is `Type` - it represents a specific ground set identity.
newtype Element :: Type -> Type
newtype Element v = Element Int

derive instance eqElement :: Eq (Element v)
derive instance ordElement :: Ord (Element v)

instance showElement :: Show (Element v) where
  show (Element i) = "e" <> show i

-- | A set of elements from ground set V.
-- |
-- | Represented as a sorted array for efficient iteration.
-- | Invariant: elements are unique and sorted by index.
type ElementSet :: Type -> Type
type ElementSet v = Set (Element v)

-- | The ground set V of n elements.
-- |
-- | The cardinality n is encoded in the Dim type to enable
-- | compile-time verification of regret bounds.
newtype GroundSet :: Type -> Type
newtype GroundSet v = GroundSet
  { size :: Dim                    -- | n = |V|
  , elements :: Array (Element v)  -- | All elements, indexed [0..n-1]
  }

derive instance eqGroundSet :: Eq (GroundSet v)

instance showGroundSet :: Show (GroundSet v) where
  show (GroundSet g) = "V[" <> show g.size <> "]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                         // submodular function classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Monotonicity classification of a submodular function.
-- |
-- | **Monotone**: f(A) ≤ f(B) whenever A ⊆ B
-- |   - Adding elements never decreases value
-- |   - Achievable approximation ratio: (1 - 1/e) ≈ 0.632
-- |
-- | **NonMonotone**: f(A) can be > f(B) even when A ⊆ B
-- |   - Adding elements may decrease value
-- |   - Achievable approximation ratio: 1/2
data Monotonicity
  = Monotone
  | NonMonotone

derive instance eqMonotonicity :: Eq Monotonicity
derive instance ordMonotonicity :: Ord Monotonicity

instance showMonotonicity :: Show Monotonicity where
  show Monotone = "Monotone"
  show NonMonotone = "NonMonotone"

-- | Curvature of a submodular function.
-- |
-- | Curvature κ ∈ [0, 1] measures how far from modular (additive) f is:
-- |
-- | κ = 1 - min_{e ∈ V, S ⊆ V\{e}} [f(S ∪ {e}) - f(S)] / [f({e}) - f(∅)]
-- |
-- | - κ = 0: f is modular (linear)
-- | - κ = 1: f has maximum submodularity
-- |
-- | Tighter curvature bounds enable better approximation ratios:
-- | - General submodular: (1 - 1/e) ≈ 0.632
-- | - Curvature κ: (1 - e^{-κ})/κ (approaches 1 as κ → 0)
data Curvature
  = CurvatureUnknown              -- ^ κ = 1 assumed (worst case)
  | CurvatureBounded Number       -- ^ κ ≤ bound, where bound ∈ [0, 1]
  | CurvatureExact Number         -- ^ κ = exact, where exact ∈ [0, 1]

derive instance eqCurvature :: Eq Curvature

instance showCurvature :: Show Curvature where
  show CurvatureUnknown = "κ≤1"
  show (CurvatureBounded k) = "κ≤" <> show k
  show (CurvatureExact k) = "κ=" <> show k

-- | A witness that a function has specific curvature.
-- |
-- | The witness encodes a proof (or certificate) that the function
-- | satisfies the curvature bound. This enables the type system to
-- | track curvature through compositions.
newtype CurvatureWitness (κ :: Curvature) = CurvatureWitness
  { bound :: Number                -- ^ The curvature bound value
  , certified :: Boolean           -- ^ Whether bound has been verified
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // core submodular function type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A value returned by evaluating f(S).
-- |
-- | Values are non-negative reals. We use Number but enforce non-negativity.
newtype SetValue = SetValue Number

derive instance eqSetValue :: Eq SetValue
derive instance ordSetValue :: Ord SetValue

instance showSetValue :: Show SetValue where
  show (SetValue v) = show v

instance semigroupSetValue :: Semigroup SetValue where
  append (SetValue a) (SetValue b) = SetValue (a + b)

instance monoidSetValue :: Monoid SetValue where
  mempty = SetValue 0.0

-- | Marginal gain from adding element e to set S.
-- |
-- | Δf(e | S) = f(S ∪ {e}) - f(S)
-- |
-- | For submodular functions, marginal gains are non-increasing as S grows.
newtype MarginalGain = MarginalGain Number

derive instance eqMarginalGain :: Eq MarginalGain
derive instance ordMarginalGain :: Ord MarginalGain

instance showMarginalGain :: Show MarginalGain where
  show (MarginalGain g) = "Δ" <> show g

instance semigroupMarginalGain :: Semigroup MarginalGain where
  append (MarginalGain a) (MarginalGain b) = MarginalGain (a + b)

instance monoidMarginalGain :: Monoid MarginalGain where
  mempty = MarginalGain 0.0

-- | A submodular function f : 2^V → ℝ₊.
-- |
-- | Phantom types encode static guarantees:
-- | - `v`: Ground set type
-- | - `m`: Monotonicity (Monotone or NonMonotone)
-- | - `κ`: Curvature bound
-- |
-- | The oracle provides access to f(S) and marginal gains.
type SubmodularFn :: Type -> Monotonicity -> Curvature -> Type
type SubmodularFn v (m :: Monotonicity) (κ :: Curvature) = SubmodularOracle v

-- | Oracle interface for evaluating a submodular function.
-- |
-- | Separates the "what" (SubmodularFn type) from the "how" (oracle impl).
-- |
-- | ## Oracle Model
-- |
-- | We assume value oracle access: given S ⊆ V, return f(S).
-- | Marginal gain oracle: given e and S, return f(S ∪ {e}) - f(S).
-- |
-- | In practice, marginal gains may be computed more efficiently than
-- | full set evaluation (e.g., for graph cuts, coverage functions).
newtype SubmodularOracle :: Type -> Type
newtype SubmodularOracle v = SubmodularOracle
  { -- | Evaluate f(S)
    eval :: ElementSet v -> SetValue
    
    -- | Evaluate marginal gain Δf(e | S) = f(S ∪ {e}) - f(S)
  , marginal :: Element v -> ElementSet v -> MarginalGain
  
    -- | Ground set
  , groundSet :: GroundSet v
  
    -- | Upper bound on f(OPT) if known (for normalized functions)
  , fMax :: Maybe SetValue
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // matroid constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matroid rank (maximum independent set size).
-- |
-- | For a cardinality matroid with constraint |S| ≤ k, the rank is k.
-- | Bounded to [1, 2^30] since rank must be positive.
newtype MatroidRank = MatroidRank Dim

derive instance eqMatroidRank :: Eq MatroidRank
derive instance ordMatroidRank :: Ord MatroidRank

instance showMatroidRank :: Show MatroidRank where
  show (MatroidRank (Dim k)) = "rank=" <> show k

-- | A set that is independent in the matroid.
-- |
-- | Invariant: the set satisfies the matroid independence axioms.
type IndependentSet :: Type -> Type
type IndependentSet v = ElementSet v

-- | A matroid (V, I) where:
-- | - V is the ground set
-- | - I ⊆ 2^V is the family of independent sets
-- |
-- | Matroid axioms:
-- | 1. ∅ ∈ I (empty set is independent)
-- | 2. If A ∈ I and B ⊆ A, then B ∈ I (hereditary)
-- | 3. If A, B ∈ I and |A| < |B|, then ∃e ∈ B\A : A ∪ {e} ∈ I (exchange)
-- |
-- | Encoded as a typeclass to enable different matroid implementations.
class Matroid :: Type -> Type -> Constraint
class Matroid m v | m -> v where
  -- | Matroid rank function: r(S) = max{|I| : I ⊆ S, I ∈ I}
  rank :: m -> ElementSet v -> MatroidRank
  
  -- | Maximum rank (rank of entire ground set)
  maxRank :: m -> MatroidRank
  
  -- | Check if a set is independent
  isIndependent :: m -> ElementSet v -> Boolean
  
  -- | Check if adding an element maintains independence
  canExtend :: m -> Element v -> IndependentSet v -> Boolean
  
  -- | Get all elements that can extend the current independent set
  extensionElements :: m -> IndependentSet v -> Array (Element v)

-- | Cardinality matroid: I = {S ⊆ V : |S| ≤ k}
-- |
-- | The simplest matroid constraint: select at most k elements.
-- | Rank function: r(S) = min(|S|, k)
newtype CardinalityMatroid :: Type -> Type
newtype CardinalityMatroid v = CardinalityMatroid
  { k :: Dim                       -- ^ Cardinality constraint
  , groundSet :: GroundSet v       -- ^ Ground set V
  }

derive instance eqCardinalityMatroid :: Eq (CardinalityMatroid v)

instance showCardinalityMatroid :: Show (CardinalityMatroid v) where
  show (CardinalityMatroid c) = "Card≤" <> show c.k

-- | A block in a partition matroid.
-- |
-- | Each block has elements and a cardinality limit.
newtype PartitionBlock :: Type -> Type
newtype PartitionBlock v = PartitionBlock
  { elements :: ElementSet v       -- ^ Elements in this block
  , limit :: Dim                   -- ^ Max elements selectable from this block
  }

derive instance eqPartitionBlock :: Eq (PartitionBlock v)

instance showPartitionBlock :: Show (PartitionBlock v) where
  show (PartitionBlock b) = "Block[" <> show b.limit <> "]"

-- | Partition matroid: V partitioned into blocks, select ≤ k_i from each.
-- |
-- | I = {S : |S ∩ V_i| ≤ k_i for all blocks i}
-- |
-- | Generalizes cardinality matroids. Common in resource allocation.
newtype PartitionMatroid :: Type -> Type
newtype PartitionMatroid v = PartitionMatroid
  { blocks :: Array (PartitionBlock v)  -- ^ Partition blocks
  , groundSet :: GroundSet v            -- ^ Ground set V
  }

derive instance eqPartitionMatroid :: Eq (PartitionMatroid v)

instance showPartitionMatroid :: Show (PartitionMatroid v) where
  show (PartitionMatroid p) = "Partition[" <> show (Array.length p.blocks) <> " blocks]"

-- | Uniform matroid: all k-subsets are bases.
-- |
-- | I = {S ⊆ V : |S| ≤ k}
-- | Same as cardinality matroid, but emphasizes that any k elements form a basis.
newtype UniformMatroid :: Type -> Type
newtype UniformMatroid v = UniformMatroid
  { n :: Dim                       -- ^ Ground set size
  , k :: Dim                       -- ^ Rank
  }

derive instance eqUniformMatroid :: Eq (UniformMatroid v)

instance showUniformMatroid :: Show (UniformMatroid v) where
  show (UniformMatroid u) = "U(" <> show u.n <> "," <> show u.k <> ")"

-- | Graphic matroid: independent sets are forests in a graph.
-- |
-- | V = edges of graph G
-- | I = {S ⊆ E : S forms a forest (no cycles)}
-- |
-- | Rank = |V(G)| - 1 for connected G (spanning tree).
newtype GraphicMatroid :: Type -> Type
newtype GraphicMatroid v = GraphicMatroid
  { vertices :: Dim                -- ^ Number of vertices in graph
  , edges :: GroundSet v           -- ^ Edges as ground set
  , adjacency :: Map Int (Set Int) -- ^ Adjacency list: vertex -> neighbors
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                       // approximation ratios (phantom types)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximation ratio α for submodular maximization.
-- |
-- | An α-approximation algorithm guarantees:
-- |   ALG ≥ α · OPT
-- |
-- | Encoded as a phantom type to track approximation guarantees statically.
-- |
-- | Standard ratios:
-- | - Monotone + cardinality: (1 - 1/e) ≈ 0.632
-- | - Non-monotone + cardinality: 1/2
-- | - Monotone + matroid: (1 - 1/e) ≈ 0.632
-- | - Non-monotone + matroid: (e-1)/(2e-1) ≈ 0.401
data ApproxRatio
  = ExactRatio              -- ^ α = 1 (optimal)
  | MonotoneMatroidRatio    -- ^ α = 1 - 1/e ≈ 0.632
  | NonMonotoneMatroidRatio -- ^ α = (e-1)/(2e-1) ≈ 0.401
  | HalfRatio               -- ^ α = 1/2
  | CustomRatio Number      -- ^ α = custom value in (0, 1]

-- | Type-level encoding of (1 - 1/e) optimal for monotone.
data MonotoneOPT

-- | Type-level encoding of 1/2 optimal for non-monotone.
data NonMonotoneOPT

-- | α-regret in online learning context.
-- |
-- | For online submodular maximization, we measure α-regret:
-- |   R_α(T) = α · Σ f_t(S_t*) - Σ f_t(S_t)
-- |
-- | Where S_t* = argmax_{S ∈ I} f_t(S) is the offline optimum for round t.
-- |
-- | Harvey/Liaw/Soma achieve O(√(kT ln(n/k))) first-order α-regret.
newtype AlphaRegret :: ApproxRatio -> Type
newtype AlphaRegret (α :: ApproxRatio) = AlphaRegret
  { cumulative :: Number           -- ^ Cumulative regret so far
  , bound :: Number                -- ^ Theoretical upper bound
  , alpha :: Number                -- ^ The approximation ratio value
  }

instance eqAlphaRegret :: Eq (AlphaRegret α) where
  eq (AlphaRegret a) (AlphaRegret b) = 
    a.cumulative == b.cumulative && a.bound == b.bound && a.alpha == b.alpha

instance showAlphaRegret :: Show (AlphaRegret α) where
  show (AlphaRegret r) = "R_" <> show r.alpha <> "=" <> show r.cumulative

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // online learning state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time horizon T (number of rounds).
-- |
-- | May be known in advance (finite horizon) or unknown (anytime).
newtype TimeHorizon = TimeHorizon (Maybe Dim)

derive instance eqTimeHorizon :: Eq TimeHorizon

instance showTimeHorizon :: Show TimeHorizon where
  show (TimeHorizon Nothing) = "T=∞"
  show (TimeHorizon (Just (Dim t))) = "T=" <> show t

-- | Current round t ∈ [1, T].
newtype Round = Round Int

derive instance eqRound :: Eq Round
derive instance ordRound :: Ord Round

instance showRound :: Show Round where
  show (Round t) = "t=" <> show t

instance semiringRound :: Semiring Round where
  add (Round a) (Round b) = Round (a + b)
  mul (Round a) (Round b) = Round (a * b)
  zero = Round 0
  one = Round 1

-- | Cumulative gradient for an element across rounds.
-- |
-- | In the continuous relaxation, we track:
-- |   ∇_e = Σ_{t=1}^T ∂f_t/∂x_e
-- |
-- | This drives the Frank-Wolfe style update.
newtype CumulativeGradient :: Type -> Type
newtype CumulativeGradient v = CumulativeGradient
  { gradients :: Map (Element v) Number  -- ^ Per-element cumulative gradient
  , round :: Round                       -- ^ Current round
  }

-- | Dual variable for Blackwell approachability.
-- |
-- | The dual λ ∈ ℝ^d tracks the direction to the target set.
newtype DualVariable :: Type -> Type
newtype DualVariable d = DualVariable
  { components :: Array Number           -- ^ λ components
  , dimension :: Dim                     -- ^ d (dimension of dual space)
  }

-- | Regret bound guarantee.
-- |
-- | Encodes the theoretical bound: R(T) ≤ bound(k, T, n)
-- |
-- | For Harvey/Liaw/Soma: O(√(kT ln(n/k)))
newtype RegretBound = RegretBound
  { value :: Number                      -- ^ Numerical bound value
  , asymptotics :: String                -- ^ Asymptotic form (e.g., "√(kT ln(n/k))")
  , tight :: Boolean                     -- ^ Whether bound is known to be tight
  }

derive instance eqRegretBound :: Eq RegretBound

instance showRegretBound :: Show RegretBound where
  show (RegretBound r) = "O(" <> r.asymptotics <> ")≤" <> show r.value

-- ═════════════════════════════════════════════════════════════════════════════
--                                           // graded monad for online learning
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grade for the online learning monad.
-- |
-- | Tracks what resources/state the computation has accumulated:
-- | - Rounds elapsed
-- | - Cumulative regret
-- | - Dual variable state
-- |
-- | Grades form a monoid under composition:
-- |   pure : G_0
-- |   bind : G_a → (a → G_b) → G_(a ⊕ b)
data OnlineGrade = OnlineGrade
  { rounds :: Int                        -- ^ Rounds elapsed
  , regret :: Number                     -- ^ Cumulative regret
  , queries :: Int                       -- ^ Oracle queries made
  }

derive instance eqOnlineGrade :: Eq OnlineGrade

instance showOnlineGrade :: Show OnlineGrade where
  show (OnlineGrade g) = 
    "⟨t=" <> show g.rounds 
    <> ",R=" <> show g.regret 
    <> ",q=" <> show g.queries <> "⟩"

instance semigroupOnlineGrade :: Semigroup OnlineGrade where
  append (OnlineGrade a) (OnlineGrade b) = OnlineGrade
    { rounds: a.rounds + b.rounds
    , regret: a.regret + b.regret
    , queries: a.queries + b.queries
    }

instance monoidOnlineGrade :: Monoid OnlineGrade where
  mempty = OnlineGrade { rounds: 0, regret: 0.0, queries: 0 }

-- | Graded monad for online learning computations.
-- |
-- | OnlineLearn g a represents a computation that:
-- | - Consumes grade g (rounds, regret, queries)
-- | - Produces a value of type a
-- |
-- | The graded monad laws ensure composition tracks cumulative resources.
-- |
-- | ## Co-Effect Interpretation
-- |
-- | The grade is a CO-EFFECT: it describes what the computation NEEDS
-- | (rounds to observe, oracle access, regret budget) rather than what
-- | it produces.
-- |
-- | This enables:
-- | - Static verification of regret bounds
-- | - Compile-time oracle query counting
-- | - Resource-aware scheduling
type OnlineLearn (g :: OnlineGrade) a = 
  { run :: a                             -- ^ The computed value
  , grade :: OnlineGrade                 -- ^ The grade (resources consumed)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // blackwell approachability
-- ═════════════════════════════════════════════════════════════════════════════

-- | Target set for Blackwell approachability.
-- |
-- | The algorithm maintains dual variables to approach this convex set.
-- | For submodular maximization, the target encodes the α-regret guarantee.
newtype TargetSet :: Type -> Type
newtype TargetSet d = TargetSet
  { halfspaces :: Array { normal :: Array Number, offset :: Number }
  }

-- | Response set for Blackwell approachability.
-- |
-- | Given adversary's action, the learner's response set contains
-- | all achievable payoffs.
newtype ResponseSet :: Type -> Type
newtype ResponseSet d = ResponseSet
  { vertices :: Array (Array Number)     -- ^ Extreme points of response polytope
  }

-- | Payoff vector in the Blackwell game.
-- |
-- | u_t ∈ ℝ^d is the vector payoff at round t.
newtype PayoffVector :: Type -> Type
newtype PayoffVector d = PayoffVector (Array Number)

instance eqPayoffVector :: Eq (PayoffVector d) where
  eq (PayoffVector a) (PayoffVector b) = a == b

instance showPayoffVector :: Show (PayoffVector d) where
  show (PayoffVector v) = "u=" <> show v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // algorithm configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sampling rate for continuous-to-discrete rounding.
-- |
-- | In continuous relaxation algorithms, we maintain x ∈ [0,1]^n
-- | and round to discrete solutions with rate ρ.
-- |
-- | Bounded to [0, 1] (probability).
newtype SamplingRate = SamplingRate Number

derive instance eqSamplingRate :: Eq SamplingRate
derive instance ordSamplingRate :: Ord SamplingRate

instance showSamplingRate :: Show SamplingRate where
  show (SamplingRate r) = "ρ=" <> show r

-- | Step size for gradient-based updates.
-- |
-- | η controls the learning rate. For regret bounds to hold,
-- | typically η = O(1/√T) or η = O(1/√t) (adaptive).
-- |
-- | Bounded to (0, 1] for stability.
newtype StepSize = StepSize Number

derive instance eqStepSize :: Eq StepSize
derive instance ordStepSize :: Ord StepSize

instance showStepSize :: Show StepSize where
  show (StepSize η) = "η=" <> show η

-- | Pipage rounding parameter.
-- |
-- | Controls how continuous solutions are rounded to discrete
-- | while preserving the value (in expectation for randomized rounding,
-- | or exactly for pipage rounding).
-- |
-- | The PiPage type encapsulates the rounding strategy and its parameters.
data PiPage
  = DeterministicPipage      -- ^ Deterministic pipage rounding
  | RandomizedPipage Number  -- ^ Randomized with given rate
  | ContiguousPipage         -- ^ Contiguous rounding (for matroids)
  | SwapPipage               -- ^ Swap-based rounding

derive instance eqPiPage :: Eq PiPage

instance showPiPage :: Show PiPage where
  show DeterministicPipage = "Pipage[det]"
  show (RandomizedPipage r) = "Pipage[rand=" <> show r <> "]"
  show ContiguousPipage = "Pipage[contig]"
  show SwapPipage = "Pipage[swap]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // matroid instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cardinality matroid instance: I = {S ⊆ V : |S| ≤ k}
-- |
-- | Rank function: r(S) = min(|S|, k)
instance matroidCardinality :: Matroid (CardinalityMatroid v) v where
  rank (CardinalityMatroid { k }) s =
    let setSize = Set.size s
        kVal = unwrapDim k
    in MatroidRank (Dim (min setSize kVal))
  
  maxRank (CardinalityMatroid { k }) = MatroidRank k
  
  isIndependent (CardinalityMatroid { k }) s =
    Set.size s <= unwrapDim k
  
  canExtend (CardinalityMatroid { k }) _ s =
    Set.size s < unwrapDim k
  
  extensionElements (CardinalityMatroid { k, groundSet }) s =
    if Set.size s >= unwrapDim k
      then []
      else
        let (GroundSet { elements }) = groundSet
        in Array.filter (\e -> not (Set.member e s)) elements

-- | Partition matroid instance: select ≤ k_i from each partition block.
-- |
-- | I = {S : ∀i. |S ∩ V_i| ≤ k_i}
-- | Rank function: r(S) = Σ_i min(|S ∩ V_i|, k_i)
instance matroidPartition :: Matroid (PartitionMatroid v) v where
  rank (PartitionMatroid { blocks }) s =
    let blockRank :: PartitionBlock v -> Int
        blockRank (PartitionBlock { elements, limit }) =
          let intersection = Set.intersection s elements
          in min (Set.size intersection) (unwrapDim limit)
        totalRank = foldl (\acc b -> acc + blockRank b) 0 blocks
    in MatroidRank (Dim totalRank)
  
  maxRank (PartitionMatroid { blocks }) =
    let sumLimits = foldl (\acc (PartitionBlock { limit }) -> acc + unwrapDim limit) 0 blocks
    in MatroidRank (Dim sumLimits)
  
  isIndependent (PartitionMatroid { blocks }) s =
    all (blockSatisfied s) blocks
    where
      blockSatisfied :: ElementSet v -> PartitionBlock v -> Boolean
      blockSatisfied set (PartitionBlock { elements, limit }) =
        Set.size (Set.intersection set elements) <= unwrapDim limit
  
  canExtend (PartitionMatroid { blocks }) e s =
    any (canAddToBlock e s) blocks
    where
      canAddToBlock :: Element v -> ElementSet v -> PartitionBlock v -> Boolean
      canAddToBlock elem set (PartitionBlock { elements, limit }) =
        Set.member elem elements &&
        Set.size (Set.intersection set elements) < unwrapDim limit
  
  extensionElements (PartitionMatroid { blocks, groundSet }) s =
    let (GroundSet { elements }) = groundSet
        canAdd e = not (Set.member e s) && any (canAddToBlock e s) blocks
        canAddToBlock elem set (PartitionBlock { elements: blockElems, limit }) =
          Set.member elem blockElems &&
          Set.size (Set.intersection set blockElems) < unwrapDim limit
    in Array.filter canAdd elements

-- | Uniform matroid instance: U_{n,k} where all k-subsets are bases.
-- |
-- | Equivalent to cardinality matroid, emphasizes basis structure.
instance matroidUniform :: Matroid (UniformMatroid v) v where
  rank (UniformMatroid { k }) s =
    let setSize = Set.size s
        kVal = unwrapDim k
    in MatroidRank (Dim (min setSize kVal))
  
  maxRank (UniformMatroid { k }) = MatroidRank k
  
  isIndependent (UniformMatroid { k }) s =
    Set.size s <= unwrapDim k
  
  canExtend (UniformMatroid { k }) _ s =
    Set.size s < unwrapDim k
  
  extensionElements (UniformMatroid { n, k }) s =
    if Set.size s >= unwrapDim k
      then []
      else
        let nVal = unwrapDim n
            allElements = Array.range 0 (nVal - 1)
        in map Element (Array.filter (\i -> not (Set.member (Element i) s)) allElements)
