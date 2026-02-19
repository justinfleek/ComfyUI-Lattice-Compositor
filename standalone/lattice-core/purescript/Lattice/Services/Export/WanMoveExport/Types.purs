-- | Lattice.Services.Export.WanMoveExport.Types - Wan-Move export types
-- |
-- | Types for trajectory and visibility data in Wan-Move compatible format.
-- |
-- | Source: ui/src/services/export/wanMoveExport.ts

module Lattice.Services.Export.WanMoveExport.Types
  ( -- * Core Types
    WanMoveTrajectory
  , TrajectoryMetadata
  , TrackPoint
    -- * Generative Flow Types
  , GenerativeFlowConfig
  , GenerativeFlowParams
  , FlowPattern(..)
    -- * Data-Driven Types
  , DataDrivenFlowConfig
  , DataMapping(..)
    -- * Colored Trajectory
  , ColoredTrajectory
  , ColorGradient
  , GradientStop
    -- * Attractor Types
  , AttractorConfig
  , AttractorType(..)
    -- * Shape Types
  , ShapeTargetConfig
  , ShapeDefinition(..)
  , ShapeEasing(..)
    -- * Force Field Types
  , ForceFieldConfig
  , ForcePoint
  , ForceFalloff(..)
  , InitialDistribution(..)
    -- * Layer Types
  , FlowLayer
    -- * Render Types
  , RenderOptions
    -- * Defaults
  , defaultTrajectoryMetadata
  , defaultGenerativeFlowParams
  , defaultRenderOptions
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

-- | Track point (x, y coordinates)
type TrackPoint = { x :: Number, y :: Number }

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

--------------------------------------------------------------------------------
-- Flow Pattern Types
--------------------------------------------------------------------------------

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

-- | Generative flow parameters
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
  , explosionCenter :: Maybe TrackPoint
    -- Vortex
  , vortexStrength :: Maybe Number
  , vortexRadius :: Maybe Number
  , vortexCenter :: Maybe TrackPoint
    -- Data River
  , riverWidth :: Maybe Number
  , riverCurve :: Maybe Number
  , riverTurbulence :: Maybe Number
    -- Morph
  , morphSource :: Maybe String
  , morphTarget :: Maybe String
  , morphEasing :: Maybe String
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

-- | Generative flow configuration
type GenerativeFlowConfig =
  { pattern :: FlowPattern
  , numPoints :: Int
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , params :: GenerativeFlowParams
  }

--------------------------------------------------------------------------------
-- Data-Driven Types
--------------------------------------------------------------------------------

-- | Data mapping type
data DataMapping
  = MappingSpeed
  | MappingDirection
  | MappingAmplitude
  | MappingPhase
  | MappingSize

derive instance Generic DataMapping _
instance Show DataMapping where show = genericShow
instance Eq DataMapping where eq = genericEq

-- | Data-driven flow configuration
type DataDrivenFlowConfig =
  { dataValues :: Array Number
  , mapping :: DataMapping
  , basePattern :: FlowPattern
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , splinePath :: Maybe (Array TrackPoint)
  }

--------------------------------------------------------------------------------
-- Colored Trajectory Types
--------------------------------------------------------------------------------

-- | Gradient stop
type GradientStop =
  { position :: Number
  , color :: { r :: Int, g :: Int, b :: Int }
  }

-- | Color gradient
type ColorGradient =
  { stops :: Array GradientStop
  }

-- | Trajectory with color data
type ColoredTrajectory =
  { tracks :: Array (Array { x :: Number, y :: Number })
  , visibility :: Array (Array Boolean)
  , metadata :: TrajectoryMetadata
  , colors :: Maybe (Array (Array { r :: Int, g :: Int, b :: Int }))
  , dataValues :: Maybe (Array Number)
  , trailLength :: Maybe Int
  }

--------------------------------------------------------------------------------
-- Attractor Types
--------------------------------------------------------------------------------

-- | Attractor type
data AttractorType
  = AttractorLorenz
  | AttractorRossler
  | AttractorAizawa
  | AttractorThomas
  | AttractorHalvorsen

derive instance Generic AttractorType _
instance Show AttractorType where show = genericShow
instance Eq AttractorType where eq = genericEq

-- | Attractor configuration
type AttractorConfig =
  { attractorType :: AttractorType
  , numPoints :: Int
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , dt :: Maybe Number
  , scale :: Maybe Number
  , center :: Maybe TrackPoint
  , seed :: Maybe Int
  }

--------------------------------------------------------------------------------
-- Shape Morph Types
--------------------------------------------------------------------------------

-- | Shape easing function
data ShapeEasing
  = EasingLinear
  | EasingEaseIn
  | EasingEaseOut
  | EasingEaseInOut
  | EasingElastic
  | EasingBounce

derive instance Generic ShapeEasing _
instance Show ShapeEasing where show = genericShow
instance Eq ShapeEasing where eq = genericEq

-- | Shape definition
data ShapeDefinition
  = ShapeCircle { radius :: Maybe Number, center :: Maybe TrackPoint }
  | ShapeGrid { columns :: Maybe Int, rows :: Maybe Int, padding :: Maybe Number }
  | ShapeText { text :: String, fontSize :: Maybe Number }
  | ShapeHeart
  | ShapeStar { points :: Maybe Int, innerRadius :: Maybe Number, outerRadius :: Maybe Number }
  | ShapeSpiral { turns :: Maybe Number }
  | ShapeRandom
  | ShapeCustom { points :: Array TrackPoint }

derive instance Generic ShapeDefinition _
instance Show ShapeDefinition where show = genericShow

-- | Shape target configuration
type ShapeTargetConfig =
  { numPoints :: Int
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , source :: ShapeDefinition
  , target :: ShapeDefinition
  , easing :: Maybe ShapeEasing
  , morphNoise :: Maybe Number
  , seed :: Maybe Int
  }

--------------------------------------------------------------------------------
-- Force Field Types
--------------------------------------------------------------------------------

-- | Force falloff type
data ForceFalloff
  = FalloffLinear
  | FalloffQuadratic
  | FalloffNone

derive instance Generic ForceFalloff _
instance Show ForceFalloff where show = genericShow
instance Eq ForceFalloff where eq = genericEq

-- | Force point (attractor or repulsor)
type ForcePoint =
  { x :: Number
  , y :: Number
  , strength :: Number  -- Positive = attractor, Negative = repulsor
  , radius :: Number    -- Influence radius
  , falloff :: Maybe ForceFalloff
  }

-- | Initial distribution type
data InitialDistribution
  = DistributionRandom
  | DistributionGrid
  | DistributionEdge
  | DistributionCenter

derive instance Generic InitialDistribution _
instance Show InitialDistribution where show = genericShow
instance Eq InitialDistribution where eq = genericEq

-- | Force field configuration
type ForceFieldConfig =
  { numPoints :: Int
  , numFrames :: Int
  , width :: Int
  , height :: Int
  , forces :: Array ForcePoint
  , initialDistribution :: Maybe InitialDistribution
  , damping :: Maybe Number
  , maxSpeed :: Maybe Number
  , seed :: Maybe Int
  }

--------------------------------------------------------------------------------
-- Layer Types
--------------------------------------------------------------------------------

-- | Flow layer for composition
type FlowLayer =
  { trajectory :: WanMoveTrajectory
  , name :: Maybe String
  , weight :: Maybe Number
  , color :: Maybe { r :: Int, g :: Int, b :: Int }
  }

--------------------------------------------------------------------------------
-- Render Types
--------------------------------------------------------------------------------

-- | Render options for trajectory visualization
type RenderOptions =
  { background :: Maybe String
  , showTrails :: Maybe Boolean
  , trailLength :: Maybe Int
  , trailFade :: Maybe Boolean
  , pointSize :: Maybe Number
  , useTrajectoryColors :: Maybe Boolean
  , defaultColor :: Maybe String
  , showVelocity :: Maybe Boolean
  }

-- | Default render options
defaultRenderOptions :: RenderOptions
defaultRenderOptions =
  { background: Just "#0a0a0a"
  , showTrails: Just true
  , trailLength: Just 10
  , trailFade: Just true
  , pointSize: Just 2.0
  , useTrajectoryColors: Just true
  , defaultColor: Just "#8b5cf6"
  , showVelocity: Just false
  }

--------------------------------------------------------------------------------
-- Defaults
--------------------------------------------------------------------------------

-- | Default trajectory metadata
defaultTrajectoryMetadata :: TrajectoryMetadata
defaultTrajectoryMetadata =
  { numPoints: 100
  , numFrames: 81
  , width: 512
  , height: 512
  , fps: 16
  }

