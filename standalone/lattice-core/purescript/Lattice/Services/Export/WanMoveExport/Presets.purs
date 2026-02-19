-- | Lattice.Services.Export.WanMoveExport.Presets - Flow presets
-- |
-- | Ready-to-use configurations for generative flow patterns.
-- |
-- | Source: ui/src/services/export/wanMoveExport.ts

module Lattice.Services.Export.WanMoveExport.Presets
  ( -- * Flow Presets
    FlowPreset
  , neuralFlowPreset
  , singularityPreset
  , dataGenesisPreset
  , informationTidePreset
  , cosmicSpiralPreset
  , metamorphosisPreset
  , hivemindPreset
  , getFlowPreset
    -- * Attractor Presets
  , AttractorPreset
  , lorenzButterflyPreset
  , rosslerSpiralPreset
  , aizawaTorusPreset
  , getAttractorPreset
    -- * Shape Presets
  , ShapeMorphPreset
  , gridToCirclePreset
  , randomToHeartPreset
  , circleToStarPreset
  , spiralToGridPreset
  , getShapeMorphPreset
  ) where

import Prelude
import Data.Maybe (Maybe(..))

import Lattice.Services.Export.WanMoveExport.Types
  ( FlowPattern(..)
  , GenerativeFlowParams
  , AttractorType(..)
  , ShapeDefinition(..)
  , ShapeEasing(..)
  , defaultGenerativeFlowParams
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Flow Presets
-- ────────────────────────────────────────────────────────────────────────────

-- | Flow preset configuration
type FlowPreset =
  { name :: String
  , pattern :: FlowPattern
  , params :: GenerativeFlowParams
  }

-- | Data flowing through neural pathways
neuralFlowPreset :: FlowPreset
neuralFlowPreset =
  { name: "neural-flow"
  , pattern: PatternDataRiver
  , params: defaultGenerativeFlowParams
      { riverWidth = Just 0.4
      , riverCurve = Just 2.0
      , riverTurbulence = Just 0.15
      , noiseStrength = Just 0.08
      }
  }

-- | Particles spiraling into a black hole
singularityPreset :: FlowPreset
singularityPreset =
  { name: "singularity"
  , pattern: PatternVortex
  , params: defaultGenerativeFlowParams
      { vortexStrength = Just 0.8
      , vortexRadius = Just 0.4
      , noiseStrength = Just 0.05
      }
  }

-- | Big bang style data explosion
dataGenesisPreset :: FlowPreset
dataGenesisPreset =
  { name: "data-genesis"
  , pattern: PatternExplosion
  , params: defaultGenerativeFlowParams
      { explosionSpeed = Just 1.2
      , explosionDecay = Just 0.92
      , noiseStrength = Just 0.15
      }
  }

-- | Gentle wave of information
informationTidePreset :: FlowPreset
informationTidePreset =
  { name: "information-tide"
  , pattern: PatternWave
  , params: defaultGenerativeFlowParams
      { waveAmplitude = Just 0.12
      , waveFrequency = Just 2.0
      , waveLayers = Just 8
      , noiseStrength = Just 0.05
      }
  }

-- | Spiral galaxy formation
cosmicSpiralPreset :: FlowPreset
cosmicSpiralPreset =
  { name: "cosmic-spiral"
  , pattern: PatternSpiral
  , params: defaultGenerativeFlowParams
      { spiralTurns = Just 4.0
      , spiralExpansion = Just 1.2
      , noiseStrength = Just 0.1
      }
  }

-- | Data morphing between shapes
metamorphosisPreset :: FlowPreset
metamorphosisPreset =
  { name: "metamorphosis"
  , pattern: PatternMorph
  , params: defaultGenerativeFlowParams
      { morphSource = Just "grid"
      , morphTarget = Just "circle"
      , morphEasing = Just "ease-in-out"
      , noiseStrength = Just 0.08
      }
  }

-- | Collective intelligence swarm
hivemindPreset :: FlowPreset
hivemindPreset =
  { name: "hivemind"
  , pattern: PatternSwarm
  , params: defaultGenerativeFlowParams
      { swarmCohesion = Just 0.015
      , swarmSeparation = Just 25.0
      , swarmAlignment = Just 0.08
      , swarmSpeed = Just 4.0
      }
  }

-- | Get flow preset by name
getFlowPreset :: String -> Maybe FlowPreset
getFlowPreset name = case name of
  "neural-flow" -> Just neuralFlowPreset
  "singularity" -> Just singularityPreset
  "data-genesis" -> Just dataGenesisPreset
  "information-tide" -> Just informationTidePreset
  "cosmic-spiral" -> Just cosmicSpiralPreset
  "metamorphosis" -> Just metamorphosisPreset
  "hivemind" -> Just hivemindPreset
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Attractor Presets
-- ────────────────────────────────────────────────────────────────────────────

-- | Attractor preset configuration
type AttractorPreset =
  { name :: String
  , attractorType :: AttractorType
  , scale :: Number
  , dt :: Number
  }

-- | Lorenz butterfly attractor
lorenzButterflyPreset :: AttractorPreset
lorenzButterflyPreset =
  { name: "lorenz-butterfly"
  , attractorType: AttractorLorenz
  , scale: 8.0
  , dt: 0.005
  }

-- | Rossler spiral attractor
rosslerSpiralPreset :: AttractorPreset
rosslerSpiralPreset =
  { name: "rossler-spiral"
  , attractorType: AttractorRossler
  , scale: 15.0
  , dt: 0.02
  }

-- | Aizawa torus attractor
aizawaTorusPreset :: AttractorPreset
aizawaTorusPreset =
  { name: "aizawa-torus"
  , attractorType: AttractorAizawa
  , scale: 80.0
  , dt: 0.01
  }

-- | Get attractor preset by name
getAttractorPreset :: String -> Maybe AttractorPreset
getAttractorPreset name = case name of
  "lorenz-butterfly" -> Just lorenzButterflyPreset
  "rossler-spiral" -> Just rosslerSpiralPreset
  "aizawa-torus" -> Just aizawaTorusPreset
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Shape Morph Presets
-- ────────────────────────────────────────────────────────────────────────────

-- | Shape morph preset configuration
type ShapeMorphPreset =
  { name :: String
  , source :: ShapeDefinition
  , target :: ShapeDefinition
  , easing :: ShapeEasing
  }

-- | Grid to circle morph
gridToCirclePreset :: ShapeMorphPreset
gridToCirclePreset =
  { name: "grid-to-circle"
  , source: ShapeGrid { columns: Nothing, rows: Nothing, padding: Nothing }
  , target: ShapeCircle { radius: Nothing, center: Nothing }
  , easing: EasingEaseInOut
  }

-- | Random to heart morph
randomToHeartPreset :: ShapeMorphPreset
randomToHeartPreset =
  { name: "random-to-heart"
  , source: ShapeRandom
  , target: ShapeHeart
  , easing: EasingElastic
  }

-- | Circle to star morph
circleToStarPreset :: ShapeMorphPreset
circleToStarPreset =
  { name: "circle-to-star"
  , source: ShapeCircle { radius: Nothing, center: Nothing }
  , target: ShapeStar { points: Just 5, innerRadius: Nothing, outerRadius: Nothing }
  , easing: EasingBounce
  }

-- | Spiral to grid morph
spiralToGridPreset :: ShapeMorphPreset
spiralToGridPreset =
  { name: "spiral-to-grid"
  , source: ShapeSpiral { turns: Just 3.0 }
  , target: ShapeGrid { columns: Nothing, rows: Nothing, padding: Nothing }
  , easing: EasingEaseOut
  }

-- | Get shape morph preset by name
getShapeMorphPreset :: String -> Maybe ShapeMorphPreset
getShapeMorphPreset name = case name of
  "grid-to-circle" -> Just gridToCirclePreset
  "random-to-heart" -> Just randomToHeartPreset
  "circle-to-star" -> Just circleToStarPreset
  "spiral-to-grid" -> Just spiralToGridPreset
  _ -> Nothing

