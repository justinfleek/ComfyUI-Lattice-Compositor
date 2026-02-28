-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // selection // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Online Selection State
-- |
-- | This module defines the state maintained by each agent for online
-- | submodular optimization. The state tracks marginal gain estimates
-- | and enables efficient lazy greedy selection.
-- |
-- | ## Memory Budget
-- |
-- | From systems architect analysis, each agent maintains ~2.5KB:
-- | - Gradients for active regions (56 max × 20 bytes ≈ 1.1KB)
-- | - Partition assignment (~1KB)
-- | - Overhead (~400 bytes)
-- |
-- | This scales to billion-agent deployment without memory pressure.
-- |
-- | ## State Update Flow
-- |
-- | ```
-- | Epoch N:
-- |   1. Read previous frame results
-- |   2. Update gradient estimates (EMA smoothing)
-- |   3. Run greedy selection using cached gradients
-- |   4. Dispatch render commands
-- |   5. Wait for results
-- |   6. Observe actual utility → update for Epoch N+1
-- | ```

module Hydrogen.Render.Online.Selection.State
  ( -- * Online State
    OnlineState(..)
  , mkOnlineState
  , emptyOnlineState
  
  -- * Marginal Estimate
  , MarginalEstimate(..)
  , mkMarginalEstimate
  , zeroEstimate
  
  -- * EMA State
  , EMAState(..)
  , mkEMAState
  , defaultEMADecay
  , updateEMA
  
  -- * State Operations
  , getGradient
  , setGradient
  , updateGradient
  , getSortedCandidates
  , staleGradients
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(GT)
  , compare
  , map
  , negate
  , otherwise
  , show
  , ($)
  , (*)
  , (+)
  , (-)
  , (<)
  , (<>)
  , (>=)
  )

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Online.Core
  ( AgentId
  , BoundedNumber
  , EpochId(..)
  , RegionId
  , Utility(..)
  , clampToBounds
  , unwrapBounded
  , zeroUtility
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // marginal // estimate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Estimated marginal gain for a region
-- |
-- | Tracks the expected utility gain from selecting this region,
-- | along with confidence (based on observation recency) and
-- | the epoch when this estimate was last updated.
newtype MarginalEstimate = MarginalEstimate
  { gain :: Utility
  , confidence :: BoundedNumber   -- [0, 1] — higher = more confident
  , lastUpdated :: EpochId
  }

derive instance eqMarginalEstimate :: Eq MarginalEstimate

instance ordMarginalEstimate :: Ord MarginalEstimate where
  compare (MarginalEstimate a) (MarginalEstimate b) =
    -- Sort by gain descending (higher gain = higher priority)
    compare b.gain a.gain

instance showMarginalEstimate :: Show MarginalEstimate where
  show (MarginalEstimate r) =
    "MarginalEstimate(gain=" <> show r.gain <>
    ", confidence=" <> show (unwrapBounded r.confidence) <>
    ", epoch=" <> show r.lastUpdated <> ")"

-- | Construct a marginal estimate
mkMarginalEstimate :: Utility -> Number -> EpochId -> MarginalEstimate
mkMarginalEstimate gain confidenceVal epoch = MarginalEstimate
  { gain
  , confidence: clampToBounds 0.0 1.0 confidenceVal
  , lastUpdated: epoch
  }

-- | Zero estimate (unknown region)
zeroEstimate :: EpochId -> MarginalEstimate
zeroEstimate epoch = MarginalEstimate
  { gain: zeroUtility
  , confidence: clampToBounds 0.0 1.0 0.0
  , lastUpdated: epoch
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // ema // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Exponential moving average state for gradient smoothing
-- |
-- | EMA smooths noisy observations over time:
-- |   ema_new = decay * ema_old + (1 - decay) * observation
-- |
-- | With decay = 0.9, the effective window is ~10 observations.
newtype EMAState = EMAState
  { value :: Utility
  , decay :: BoundedNumber  -- [0, 1] — typically 0.9
  }

derive instance eqEMAState :: Eq EMAState

instance showEMAState :: Show EMAState where
  show (EMAState r) =
    "EMAState(value=" <> show r.value <>
    ", decay=" <> show (unwrapBounded r.decay) <> ")"

-- | Construct EMA state
mkEMAState :: Utility -> Number -> EMAState
mkEMAState value decayVal = EMAState
  { value
  , decay: clampToBounds 0.0 1.0 decayVal
  }

-- | Default EMA decay factor
-- |
-- | 0.9 provides good smoothing while remaining responsive to changes.
-- | Effective window ≈ 1 / (1 - 0.9) = 10 observations.
defaultEMADecay :: Number
defaultEMADecay = 0.9

-- | Update EMA with a new observation
updateEMA :: EMAState -> Utility -> EMAState
updateEMA (EMAState state) (Utility observation) =
  let decay = unwrapBounded state.decay
      Utility oldVal = state.value
      oldNum = unwrapBounded oldVal
      obsNum = unwrapBounded observation
      newNum = decay * oldNum + (1.0 - decay) * obsNum
      newVal = clampToBounds 0.0 1.0e12 newNum
  in EMAState state { value = Utility newVal }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // online // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Online state maintained by each agent
-- |
-- | Tracks gradient estimates for regions this agent is responsible for.
-- | State is bounded: at most 56 active regions (the matroid rank).
newtype OnlineState = OnlineState
  { gradients :: Map RegionId MarginalEstimate
  , ema :: Map RegionId EMAState
  , epoch :: EpochId
  , agentId :: AgentId
  }

derive instance eqOnlineState :: Eq OnlineState

instance showOnlineState :: Show OnlineState where
  show (OnlineState state) =
    "OnlineState(agent=" <> show state.agentId <>
    ", epoch=" <> show state.epoch <>
    ", regions=" <> show (Map.size state.gradients) <> ")"

-- | Construct online state for an agent
mkOnlineState :: AgentId -> EpochId -> OnlineState
mkOnlineState agentId epoch = OnlineState
  { gradients: Map.empty
  , ema: Map.empty
  , epoch
  , agentId
  }

-- | Empty online state (for initialization)
emptyOnlineState :: AgentId -> OnlineState
emptyOnlineState agentId = mkOnlineState agentId (EpochId 0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // state // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the gradient estimate for a region
getGradient :: RegionId -> OnlineState -> Maybe MarginalEstimate
getGradient regionId (OnlineState state) =
  Map.lookup regionId state.gradients

-- | Set the gradient estimate for a region
setGradient :: RegionId -> MarginalEstimate -> OnlineState -> OnlineState
setGradient regionId estimate (OnlineState state) =
  OnlineState state { gradients = Map.insert regionId estimate state.gradients }

-- | Update a gradient with a new observation
-- |
-- | Uses EMA smoothing to reduce noise in gradient estimates.
updateGradient :: RegionId -> Utility -> OnlineState -> OnlineState
updateGradient regionId observation (OnlineState state) =
  let -- Get or initialize EMA state
      emaState = fromMaybe (mkEMAState zeroUtility defaultEMADecay) 
                           (Map.lookup regionId state.ema)
      
      -- Update EMA with new observation
      newEma = updateEMA emaState observation
      
      -- Create new estimate from smoothed value
      EMAState { value: smoothedGain } = newEma
      newEstimate = mkMarginalEstimate smoothedGain 1.0 state.epoch
      
  in OnlineState state
       { gradients = Map.insert regionId newEstimate state.gradients
       , ema = Map.insert regionId newEma state.ema
       }

-- | Get candidates sorted by descending marginal gain
-- |
-- | Returns (RegionId, MarginalEstimate) pairs sorted by gain.
-- | This ordering is used by the greedy algorithm.
getSortedCandidates :: OnlineState -> Array (Tuple RegionId MarginalEstimate)
getSortedCandidates (OnlineState state) =
  Array.sortBy compareByGain (Map.toUnfoldable state.gradients)

-- | Compare by gain descending
compareByGain 
  :: Tuple RegionId MarginalEstimate 
  -> Tuple RegionId MarginalEstimate 
  -> Ordering
compareByGain (Tuple _ a) (Tuple _ b) = compare a b

-- | Find regions with stale gradients (older than threshold epochs)
-- |
-- | Stale gradients should be discounted or re-explored.
staleGradients :: Int -> OnlineState -> Array RegionId
staleGradients threshold (OnlineState state) =
  let EpochId currentEpoch = state.epoch
      isStale (Tuple regionId (MarginalEstimate est)) =
        let EpochId lastEpoch = est.lastUpdated
        in currentEpoch - lastEpoch >= threshold
  in map (\(Tuple rid _) -> rid) 
       (Array.filter isStale (Map.toUnfoldable state.gradients))
