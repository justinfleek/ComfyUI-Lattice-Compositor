-- | Lattice.Services.Export.FlowGenerators.Types - Flow generator types
-- |
-- | Types for Wan-Move flow generation including trajectory data,
-- | configuration, and pattern-specific parameters.
-- |
-- | Source: ui/src/services/export/wanMoveExport.ts (types)

module Lattice.Services.Export.FlowGenerators.Types
  ( -- * Core Types
    WanMoveTrajectory
  , TrajectoryMetadata
    -- * Configuration Types
  , GenerativeFlowConfig
  , GenerativeFlowParams
  , DataDrivenFlowConfig
    -- * Pattern Types
  , FlowPattern(..)
  , DataMapping(..)
  , MorphShape(..)
  , MorphEasing(..)
    -- * Defaults
  , defaultGenerativeFlowParams
  , defaultTrajectoryMetadata
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)

-- ────────────────────────────────────────────────────────────────────────────
-- Core Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Trajectory metadata
type TrajectoryMetadata =
  { numPoints :: Int
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , fps :: Int
  }

-- | Wan-Move trajectory format
-- | tracks: [N][T][2] where N=points, T=frames, 2=x,y
-- | visibility: [N][T] where true = visible
type WanMoveTrajectory =
  { tracks :: Array (Array { x :: Number, y :: Number })
  , visibility :: Array (Array Boolean)
  , metadata :: TrajectoryMetadata
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Pattern Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Flow pattern type
data FlowPattern
  = PatternSpiral
  | PatternWave
  | PatternExplosion
  | PatternVortex
  | PatternDataRiver
  | PatternMorph
  | PatternSwarm

derive instance Generic FlowPattern _
instance Show FlowPattern where show = genericShow
instance Eq FlowPattern where eq = genericEq

-- | Data-to-motion mapping type
data DataMapping
  = MappingSpeed
  | MappingDirection
  | MappingAmplitude
  | MappingPhase
  | MappingSize

derive instance Generic DataMapping _
instance Show DataMapping where show = genericShow
instance Eq DataMapping where eq = genericEq

-- | Morph source/target shape
data MorphShape
  = ShapeCircle
  | ShapeGrid
  | ShapeRandom

derive instance Generic MorphShape _
instance Show MorphShape where show = genericShow
instance Eq MorphShape where eq = genericEq

-- | Morph easing function
data MorphEasing
  = EasingLinear
  | EasingIn
  | EasingOut
  | EasingInOut

derive instance Generic MorphEasing _
instance Show MorphEasing where show = genericShow
instance Eq MorphEasing where eq = genericEq

-- ────────────────────────────────────────────────────────────────────────────
-- Configuration Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Pattern-specific parameters
type GenerativeFlowParams =
  { -- Spiral
    spiralTurns :: Maybe Number
  , spiralExpansion :: Maybe Number
  , spiralSpeed :: Maybe Number
    -- Wave
  , waveAmplitude :: Maybe Number
  , waveFrequency :: Maybe Number
  , waveSpeed :: Maybe Number
  , waveLayers :: Maybe Int
    -- Explosion
  , explosionSpeed :: Maybe Number
  , explosionDecay :: Maybe Number
  , explosionCenter :: Maybe { x :: Number, y :: Number }
    -- Vortex
  , vortexStrength :: Maybe Number
  , vortexRadius :: Maybe Number
  , vortexCenter :: Maybe { x :: Number, y :: Number }
    -- Data River
  , riverWidth :: Maybe Number
  , riverCurve :: Maybe Number
  , riverTurbulence :: Maybe Number
    -- Morph
  , morphSource :: Maybe MorphShape
  , morphTarget :: Maybe MorphShape
  , morphEasing :: Maybe MorphEasing
    -- Swarm
  , swarmCohesion :: Maybe Number
  , swarmSeparation :: Maybe Number
  , swarmAlignment :: Maybe Number
  , swarmSpeed :: Maybe Number
    -- Common
  , noiseStrength :: Maybe Number
  , noiseScale :: Maybe Number
  , seed :: Maybe Int
  }

-- | Generative flow configuration
type GenerativeFlowConfig =
  { pattern :: FlowPattern
  , numPoints :: Int
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , params :: GenerativeFlowParams
  }

-- | Data-driven flow configuration
type DataDrivenFlowConfig =
  { dataValues :: Array Number
  , mapping :: DataMapping
  , basePattern :: FlowPattern
  , numFrames :: Int
  , width :: Int
  , height :: Int
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Defaults
-- ────────────────────────────────────────────────────────────────────────────

-- | Default generative flow parameters
defaultGenerativeFlowParams :: GenerativeFlowParams
defaultGenerativeFlowParams =
  { spiralTurns: Nothing
  , spiralExpansion: Nothing
  , spiralSpeed: Nothing
  , waveAmplitude: Nothing
  , waveFrequency: Nothing
  , waveSpeed: Nothing
  , waveLayers: Nothing
  , explosionSpeed: Nothing
  , explosionDecay: Nothing
  , explosionCenter: Nothing
  , vortexStrength: Nothing
  , vortexRadius: Nothing
  , vortexCenter: Nothing
  , riverWidth: Nothing
  , riverCurve: Nothing
  , riverTurbulence: Nothing
  , morphSource: Nothing
  , morphTarget: Nothing
  , morphEasing: Nothing
  , swarmCohesion: Nothing
  , swarmSeparation: Nothing
  , swarmAlignment: Nothing
  , swarmSpeed: Nothing
  , noiseStrength: Nothing
  , noiseScale: Nothing
  , seed: Nothing
  }

-- | Default trajectory metadata
defaultTrajectoryMetadata :: TrajectoryMetadata
defaultTrajectoryMetadata =
  { numPoints: 0
  , numFrames: 0
  , width: 512
  , height: 512
  , fps: 16
  }
