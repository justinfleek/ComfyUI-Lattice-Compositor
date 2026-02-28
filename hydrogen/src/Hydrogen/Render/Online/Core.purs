-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // render // online
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Online Submodular Optimization — Core Types
-- |
-- | This module defines the foundational types for online submodular maximization
-- | used in adaptive rendering quality allocation. The design synthesizes:
-- |
-- | - **Type Theory**: Phantom types for monotonicity, witness types for guarantees
-- | - **ML/Diffusion**: Weighted coverage function with diminishing returns
-- | - **Systems**: Partitioned coordination, bounded memory, deterministic identity
-- |
-- | ## Core Insight
-- |
-- | Types DESCRIBE guarantees (compile-time), runtime TRACKS actual values.
-- | A `SubmodularFn 'Monotone a` guarantees (1-1/e) approximation is achievable.
-- | The actual utility achieved is tracked in `OnlineState` at runtime.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Element selection as submodular maximization:
-- |   f(S) = Σ max_{r∈S} w_p · q(r, s_r) + λ · Coverage(S)
-- |
-- | Subject to matroid constraint:
-- |   Partition matroid over render tiers (foveal/peripheral/background)
-- |
-- | Greedy achieves (1 - 1/e) ≈ 0.632 approximation for monotone + matroid
-- | ```

module Hydrogen.Render.Online.Core
  ( -- * Bounded Numeric Types
    BoundedNumber
  , mkBoundedNumber
  , unwrapBounded
  , clampToBounds
  
  -- * Utility Type
  , Utility(..)
  , zeroUtility
  , addUtility
  , maxUtility
  
  -- * Quality Types
  , Quality(..)
  , DiffusionSteps(..)
  , mkDiffusionSteps
  
  -- * Grid Types
  , GridLevel(..)
  , GridCoord(..)
  , mkGridCoord
  , gridLevelSize
  
  -- * Render Tiers
  , RenderTier(..)
  , tierPriority
  , tierDefaultSteps
  
  -- * Region Types
  , RegionId(..)
  , Region(..)
  , RegionSelection(..)
  
  -- * Epoch Types
  , EpochId(..)
  , AgentId(..)
  , nextEpoch
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, EQ, GT)
  , compare
  , identity
  , max
  , min
  , show
  , ($)
  , (&&)
  , (+)
  , (<)
  , (<=)
  , (<>)
  , (==)
  , (>)
  , (>=)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // bounded // numeric // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A number bounded within [lo, hi]
-- |
-- | Invariant: lo <= value <= hi
-- | Construction: Only via `mkBoundedNumber` which validates bounds
-- | 
-- | This is the foundation for all bounded values in the optimization system.
-- | Unbounded values cannot exist — every numeric has explicit domain.
newtype BoundedNumber = BoundedNumber
  { value :: Number
  , lo :: Number
  , hi :: Number
  }

derive instance eqBoundedNumber :: Eq BoundedNumber

instance ordBoundedNumber :: Ord BoundedNumber where
  compare (BoundedNumber a) (BoundedNumber b) = compare a.value b.value

instance showBoundedNumber :: Show BoundedNumber where
  show (BoundedNumber r) = 
    "BoundedNumber(" <> show r.value <> " ∈ [" <> show r.lo <> ", " <> show r.hi <> "])"

-- | Construct a bounded number, returning Nothing if out of bounds
mkBoundedNumber :: Number -> Number -> Number -> Maybe BoundedNumber
mkBoundedNumber lo hi value
  | lo <= value && value <= hi = Just (BoundedNumber { value, lo, hi })
  | value < lo = Nothing
  | value > hi = Nothing
  | lo > hi = Nothing  -- Invalid bounds
  | true = Nothing     -- Catch NaN and other edge cases

-- | Extract the underlying value
unwrapBounded :: BoundedNumber -> Number
unwrapBounded (BoundedNumber r) = r.value

-- | Clamp a value to bounds (never fails)
clampToBounds :: Number -> Number -> Number -> BoundedNumber
clampToBounds lo hi value = BoundedNumber
  { value: max lo (min hi value)
  , lo
  , hi
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // utility // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Utility value — bounded non-negative with explicit maximum
-- |
-- | Range: [0, 1e12] — sufficient for any practical rendering budget
-- | The upper bound prevents overflow in summations.
newtype Utility = Utility BoundedNumber

derive instance eqUtility :: Eq Utility
derive instance ordUtility :: Ord Utility

instance showUtility :: Show Utility where
  show (Utility bn) = "Utility(" <> show (unwrapBounded bn) <> ")"

-- | Zero utility — the additive identity
zeroUtility :: Utility
zeroUtility = Utility (clampToBounds 0.0 1.0e12 0.0)

-- | Add two utilities, clamping to maximum
addUtility :: Utility -> Utility -> Utility
addUtility (Utility a) (Utility b) =
  Utility (clampToBounds 0.0 1.0e12 (unwrapBounded a + unwrapBounded b))

-- | Maximum of two utilities
maxUtility :: Utility -> Utility -> Utility
maxUtility (Utility a) (Utility b) =
  if unwrapBounded a >= unwrapBounded b
    then Utility a
    else Utility b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // quality // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render quality — normalized [0, 1]
-- |
-- | 0 = minimum acceptable quality
-- | 1 = maximum possible quality
newtype Quality = Quality BoundedNumber

derive instance eqQuality :: Eq Quality
derive instance ordQuality :: Ord Quality

instance showQuality :: Show Quality where
  show (Quality bn) = "Quality(" <> show (unwrapBounded bn) <> ")"

-- | Number of diffusion steps allocated to a region
-- |
-- | Range: [1, 50] — based on diminishing returns curve
-- | q(s) = q_max · (1 - e^{-α·s}) saturates around 50 steps
newtype DiffusionSteps = DiffusionSteps Int

derive instance eqDiffusionSteps :: Eq DiffusionSteps
derive instance ordDiffusionSteps :: Ord DiffusionSteps

instance showDiffusionSteps :: Show DiffusionSteps where
  show (DiffusionSteps s) = "DiffusionSteps(" <> show s <> ")"

-- | Construct diffusion steps within valid bounds
mkDiffusionSteps :: Int -> Maybe DiffusionSteps
mkDiffusionSteps s
  | s >= 1 && s <= 50 = Just (DiffusionSteps s)
  | s < 1 = Nothing
  | s > 50 = Nothing
  | true = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // grid // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid resolution levels — hybrid grid from ML expert
-- |
-- | - Coarse: 8×8 = 64 regions (overview)
-- | - Medium: 16×16 = 256 regions (standard)
-- | - Fine: 32×32 = 1024 regions (detail)
data GridLevel
  = Coarse   -- 8×8
  | Medium   -- 16×16
  | Fine     -- 32×32

derive instance eqGridLevel :: Eq GridLevel

instance ordGridLevel :: Ord GridLevel where
  compare Coarse Coarse = EQ
  compare Coarse _ = LT
  compare Medium Coarse = GT
  compare Medium Medium = EQ
  compare Medium Fine = LT
  compare Fine Fine = EQ
  compare Fine _ = GT

instance showGridLevel :: Show GridLevel where
  show Coarse = "Coarse(8×8)"
  show Medium = "Medium(16×16)"
  show Fine = "Fine(32×32)"

-- | Get the dimension size for a grid level
gridLevelSize :: GridLevel -> Int
gridLevelSize Coarse = 8
gridLevelSize Medium = 16
gridLevelSize Fine = 32

-- | Grid coordinate at a specific level
-- |
-- | Coordinates are bounded by grid level:
-- | - Coarse: x,y ∈ [0,7]
-- | - Medium: x,y ∈ [0,15]
-- | - Fine: x,y ∈ [0,31]
newtype GridCoord = GridCoord
  { level :: GridLevel
  , x :: Int
  , y :: Int
  }

derive instance eqGridCoord :: Eq GridCoord
derive instance ordGridCoord :: Ord GridCoord

instance showGridCoord :: Show GridCoord where
  show (GridCoord r) = 
    "GridCoord(" <> show r.level <> ", " <> show r.x <> ", " <> show r.y <> ")"

-- | Construct a grid coordinate, validating bounds
mkGridCoord :: GridLevel -> Int -> Int -> Maybe GridCoord
mkGridCoord level x y =
  let maxCoord = gridLevelSize level
  in if x >= 0 && x < maxCoord && y >= 0 && y < maxCoord
       then Just (GridCoord { level, x, y })
       else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // render // tiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render priority tiers — partition matroid categories
-- |
-- | From ML expert's analysis:
-- | - Foveal: High priority (gaze-centered), k₁ = 8 max selections
-- | - Peripheral: Medium priority (context), k₂ = 16 max selections  
-- | - Background: Low priority (ambient), k₃ = 32 max selections
-- |
-- | Total budget: 56 regions per frame
data RenderTier
  = Foveal       -- Highest priority, most quality
  | Peripheral   -- Medium priority, moderate quality
  | Background   -- Lowest priority, minimum quality

derive instance eqRenderTier :: Eq RenderTier

instance ordRenderTier :: Ord RenderTier where
  compare Foveal Foveal = EQ
  compare Foveal _ = GT          -- Foveal is highest priority
  compare Peripheral Foveal = LT
  compare Peripheral Peripheral = EQ
  compare Peripheral Background = GT
  compare Background Background = EQ
  compare Background _ = LT      -- Background is lowest priority

instance showRenderTier :: Show RenderTier where
  show Foveal = "Foveal"
  show Peripheral = "Peripheral"
  show Background = "Background"

-- | Get the priority weight for a tier (higher = more important)
tierPriority :: RenderTier -> Number
tierPriority Foveal = 1.0
tierPriority Peripheral = 0.5
tierPriority Background = 0.25

-- | Get the default diffusion steps for a tier
tierDefaultSteps :: RenderTier -> DiffusionSteps
tierDefaultSteps Foveal = DiffusionSteps 50
tierDefaultSteps Peripheral = DiffusionSteps 25
tierDefaultSteps Background = DiffusionSteps 10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // region // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a region — deterministic via UUID5
-- |
-- | Derived from grid coordinate: uuid5(namespace_region, serialize(coord))
-- | Same coordinate always produces same RegionId.
newtype RegionId = RegionId String

derive instance eqRegionId :: Eq RegionId
derive instance ordRegionId :: Ord RegionId

instance showRegionId :: Show RegionId where
  show (RegionId id) = "RegionId(" <> id <> ")"

-- | A renderable region with spatial and priority information
newtype Region = Region
  { id :: RegionId
  , coord :: GridCoord
  , tier :: RenderTier
  }

derive instance eqRegion :: Eq Region
derive instance ordRegion :: Ord Region

instance showRegion :: Show Region where
  show (Region r) = "Region(" <> show r.coord <> ", " <> show r.tier <> ")"

-- | A region selection pairs a region with quality allocation
-- |
-- | This is the element type for the submodular optimization:
-- | Select which regions to render and how many diffusion steps each gets.
newtype RegionSelection = RegionSelection
  { region :: Region
  , steps :: DiffusionSteps
  }

derive instance eqRegionSelection :: Eq RegionSelection
derive instance ordRegionSelection :: Ord RegionSelection

instance showRegionSelection :: Show RegionSelection where
  show (RegionSelection r) = 
    "Selection(" <> show r.region <> ", " <> show r.steps <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // epoch // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Epoch identifier — monotonically increasing frame counter
-- |
-- | Used for:
-- | - Coordination: All agents in same epoch see consistent state
-- | - Staleness: Gradients older than N epochs are discounted
-- | - Identity: Selection IDs include epoch for uniqueness
newtype EpochId = EpochId Int

derive instance eqEpochId :: Eq EpochId
derive instance ordEpochId :: Ord EpochId

instance showEpochId :: Show EpochId where
  show (EpochId e) = "Epoch(" <> show e <> ")"

-- | Advance to the next epoch
nextEpoch :: EpochId -> EpochId
nextEpoch (EpochId e) = EpochId (e + 1)

-- | Unique identifier for an agent in the swarm
-- |
-- | Deterministic: uuid5(namespace_agent, agent_index)
-- | Enables consistent partitioning across epochs.
newtype AgentId = AgentId String

derive instance eqAgentId :: Eq AgentId
derive instance ordAgentId :: Ord AgentId

instance showAgentId :: Show AgentId where
  show (AgentId id) = "AgentId(" <> id <> ")"
