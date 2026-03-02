-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // worldmodel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | World Model Integration for Lattice Compositor
-- |
-- | This module consolidates the world model infrastructure enabling AI agents
-- | to predict future world states through video simulation conditioned on
-- | actions.
-- |
-- | ## Components
-- |
-- | - **Types**: Core tensor, state, action, and observation types
-- | - **PAN**: Generative Latent Prediction (GLP) architecture (arXiv 2511.09057)
-- | - **AnchorWeave**: Local spatial memory for world-consistent generation
-- |   (arXiv 2602.14941)
-- | - **Memory**: Memory bank and coverage-driven retrieval
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents operate at 1000 tokens/second, the world model infrastructure
-- | must be provably correct:
-- |
-- | - All types are bounded with explicit min/max
-- | - UUIDs provide cryptographic verification
-- | - Coverage algorithms have deterministic output
-- | - No escape hatches - invalid states are unrepresentable
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.WorldModel
-- |   ( Tensor(..)
-- |   , WorldState(..)
-- |   , PANModel(..)
-- |   , MemoryBank
-- |   , retrieve
-- |   )
-- | ```

module Hydrogen.WorldModel
  ( -- * Re-exported from Types
    module Hydrogen.WorldModel.Types
    
  -- * Re-exported from PAN
  , module Hydrogen.WorldModel.PAN
  
  -- * Re-exported from AnchorWeave
  , module Hydrogen.WorldModel.AnchorWeave
  
  -- * Re-exported from Memory
  , module Hydrogen.WorldModel.Memory
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.WorldModel.Types
  ( TensorShape(..)
  , Tensor(..)
  , TensorId(..)
  , tensorId
  , tensorShape
  , tensorRank
  , emptyTensor
  , scalarTensor
  , WorldState(..)
  , WorldStateId(..)
  , emptyWorldState
  , stateLatent
  , stateHistory
  , stateTimestamp
  , Observation(..)
  , ObservationId(..)
  , VideoFrame(..)
  , FrameIndex(..)
  , frameIndex
  , observationFrame
  , WorldAction(..)
  , ActionId(..)
  , NaturalLanguageAction(..)
  , CameraAction(..)
  , AgentAction(..)
  , CameraPose(..)
  , CameraTrajectory(..)
  , trajectoryLength
  , trajectoryPose
  , LatentCode(..)
  , LatentDimension(..)
  , latentDimension
  , latentCodeId
  , Timestep(..)
  , timestep
  , nextTimestep
  , timestepValue
  )

import Hydrogen.WorldModel.PAN
  ( Encoder(..)
  , Predictor(..)
  , Decoder(..)
  , PANModel(..)
  , createPAN
  )

import Hydrogen.WorldModel.AnchorWeave
  ( LocalMemory(..)
  , MemoryId(..)
  , Anchor(..)
  , AnchorSet(..)
  , emptyAnchorSet
  , WeavingController(..)
  , createController
  )

import Hydrogen.WorldModel.Memory
  ( MemoryBank(..)
  , emptyBank
  , bankSize
  , addMemory
  , Coverage(..)
  , CoverageFunction
  , computeCoverage
  , compareCoverage
  , coverageValue
  , addCoverage
  , zeroCoverage
  , RetrievalConfig(..)
  , defaultRetrievalConfig
  , retrieve
  , retrieveWithFunction
  , sameMemory
  , differentMemories
  , notSameMemory
  )
