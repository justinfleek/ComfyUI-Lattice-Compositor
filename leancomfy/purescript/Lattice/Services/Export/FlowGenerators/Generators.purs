-- | Lattice.Services.Export.FlowGenerators.Generators - Flow pattern generators
-- |
-- | Anadol-style generative flow patterns for Wan-Move trajectories.
-- | All generators are pure functions with deterministic output given a seed.
-- |
-- | Patterns:
-- | - Spiral: Galaxy spiral pattern with configurable turns
-- | - Wave: Ocean wave pattern with layers
-- | - Explosion: Big bang outward burst
-- | - Vortex: Whirlpool inward spiral
-- | - DataRiver: Particles flowing along S-curve
-- | - Morph: Shape-to-shape transition
-- | - Swarm: Boid flocking behavior
-- |
-- | Source: ui/src/services/export/wanMoveFlowGenerators.ts

module Lattice.Services.Export.FlowGenerators.Generators
  ( -- * Flow Generators
    generateSpiralFlow
  , generateWaveFlow
  , generateExplosionFlow
  , generateVortexFlow
  , generateDataRiverFlow
  , generateMorphFlow
  , generateSwarmFlow
    -- * Dispatch
  , generateFlow
  ) where

import Prelude
import Data.Array ((..), length, range, replicate, snoc, zipWith, mapWithIndex, (!!))
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (sqrt, cos, sin, pi, log)
import Data.Foldable (foldl, sum)
import Data.Traversable (for)

import Lattice.Services.Export.FlowGenerators.Types
  ( WanMoveTrajectory
  , TrajectoryMetadata
  , GenerativeFlowConfig
  , GenerativeFlowParams
  , FlowPattern(..)
  , MorphShape(..)
  , MorphEasing(..)
  )
import Lattice.Services.Export.FlowGenerators.SeededRandom
  ( SeededRandomState
  , initialState
  , nextWithState
  , rangeWithState
  , gaussianWithState
  )
import Lattice.Services.Export.FlowGenerators.Noise (simplexNoise2D)

--------------------------------------------------------------------------------
-- Dispatch
--------------------------------------------------------------------------------

-- | Generate flow based on pattern type
generateFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateFlow config = case config.pattern of
  PatternSpiral -> generateSpiralFlow config
  PatternWave -> generateWaveFlow config
  PatternExplosion -> generateExplosionFlow config
  PatternVortex -> generateVortexFlow config
  PatternDataRiver -> generateDataRiverFlow config
  PatternMorph -> generateMorphFlow config
  PatternSwarm -> generateSwarmFlow config

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Clamp value to bounds
clamp :: Number -> Number -> Number -> Number
clamp lo hi x = max lo (min hi x)

-- | Minimum of two values
min :: forall a. Ord a => a -> a -> a
min a b = if a < b then a else b

-- | Maximum of two values
max :: forall a. Ord a => a -> a -> a
max a b = if a > b then a else b

-- | Extract seed with default
getSeed :: GenerativeFlowParams -> Int
getSeed params = fromMaybe 42 params.seed

-- | Create metadata from config
makeMetadata :: GenerativeFlowConfig -> TrajectoryMetadata
makeMetadata cfg =
  { numPoints: cfg.numPoints
  , numFrames: cfg.numFrames
  , width: cfg.width
  , height: cfg.height
  , fps: 16
  }

--------------------------------------------------------------------------------
-- Spiral Flow Generator
--------------------------------------------------------------------------------

-- | Generate spiral galaxy flow pattern
generateSpiralFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateSpiralFlow cfg =
  let
    seed = getSeed cfg.params
    turns = fromMaybe 3.0 cfg.params.spiralTurns
    expansion = fromMaybe 1.5 cfg.params.spiralExpansion
    noise = fromMaybe 0.1 cfg.params.noiseStrength

    width = toNumber cfg.width
    height = toNumber cfg.height
    centerX = width / 2.0
    centerY = height / 2.0
    maxRadius = min width height * 0.45

    -- Generate track for one point
    generatePoint :: Int -> SeededRandomState
                  -> { track :: Array { x :: Number, y :: Number }
                     , vis :: Array Boolean
                     , state :: SeededRandomState }
    generatePoint i rng =
      let
        r1 = nextWithState rng
        r2 = nextWithState r1.state
        r3 = nextWithState r2.state
        armOffset = r1.value * pi * 2.0
        radiusOffset = r2.value
        phaseOffset = r3.value * 0.5

        -- Generate frames
        frames = range 0 (cfg.numFrames - 1)
        generateFrame f =
          let
            t = toNumber f / toNumber cfg.numFrames + phaseOffset
            angle = armOffset + t * pi * 2.0 * turns
            radius = (radiusOffset + t * expansion) * maxRadius
            noiseVal = simplexNoise2D (toNumber i * 0.1) (toNumber f * 0.05) seed
            noisedRadius = radius * (1.0 + (noiseVal - 0.5) * noise * 2.0)
            x = centerX + cos angle * noisedRadius
            y = centerY + sin angle * noisedRadius
            clampedX = clamp 0.0 width x
            clampedY = clamp 0.0 height y
            distFromCenter = sqrt ((x - centerX) * (x - centerX) + (y - centerY) * (y - centerY))
          in
            { pos: { x: clampedX, y: clampedY }
            , visible: distFromCenter < maxRadius * 1.1
            }

        frameResults = map generateFrame frames
      in
        { track: map _.pos frameResults
        , vis: map _.visible frameResults
        , state: r3.state
        }

    -- Generate all points
    go :: Int -> SeededRandomState
       -> Array (Array { x :: Number, y :: Number })
       -> Array (Array Boolean)
       -> { tracks :: Array (Array { x :: Number, y :: Number })
          , visibility :: Array (Array Boolean) }
    go i rng accTracks accVis
      | i >= cfg.numPoints =
          { tracks: accTracks, visibility: accVis }
      | otherwise =
          let
            result = generatePoint i rng
          in
            go (i + 1) result.state (snoc accTracks result.track) (snoc accVis result.vis)

    result = go 0 (initialState seed) [] []
  in
    { tracks: result.tracks
    , visibility: result.visibility
    , metadata: makeMetadata cfg
    }

--------------------------------------------------------------------------------
-- Wave Flow Generator
--------------------------------------------------------------------------------

-- | Generate wave/ocean flow pattern
generateWaveFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateWaveFlow cfg =
  let
    seed = getSeed cfg.params
    width = toNumber cfg.width
    height = toNumber cfg.height
    amplitude = fromMaybe (height * 0.15) cfg.params.waveAmplitude
    frequency = fromMaybe 3.0 cfg.params.waveFrequency
    speed = fromMaybe 0.1 cfg.params.waveSpeed
    layers = fromMaybe 5 cfg.params.waveLayers
    noise = fromMaybe 0.05 cfg.params.noiseStrength

    generatePoint :: Int -> SeededRandomState
                  -> { track :: Array { x :: Number, y :: Number }
                     , vis :: Array Boolean
                     , state :: SeededRandomState }
    generatePoint i rng =
      let
        r1 = nextWithState rng
        r2 = nextWithState r1.state
        r3 = nextWithState r2.state
        r4 = nextWithState r3.state

        layer = floor (r1.value * toNumber layers)
        layerY = (toNumber layer + 0.5) / toNumber layers * height
        startX = r2.value * width
        phaseOffset = r3.value * pi * 2.0
        amplitudeVariation = 0.5 + r4.value * 0.5

        frames = range 0 (cfg.numFrames - 1)
        generateFrame f =
          let
            t = toNumber f / toNumber cfg.numFrames
            rawX = startX + t * width * speed * 10.0
            x = ((rawX `mod'` (width * 1.2)) - width * 0.1)
            wave = sin ((x / width) * pi * 2.0 * frequency + phaseOffset + t * pi * 4.0)
            baseY = layerY + wave * amplitude * amplitudeVariation
            noiseVal = simplexNoise2D (x * 0.01) (toNumber f * 0.05 + toNumber layer) seed
            y = baseY + (noiseVal - 0.5) * amplitude * noise * 4.0
          in
            { pos: { x: clamp 0.0 width x, y: clamp 0.0 height y }
            , visible: x >= 0.0 && x <= width
            }

        frameResults = map generateFrame frames
      in
        { track: map _.pos frameResults
        , vis: map _.visible frameResults
        , state: r4.state
        }

    result = foldPoints cfg.numPoints (initialState seed) generatePoint
  in
    { tracks: result.tracks
    , visibility: result.visibility
    , metadata: makeMetadata cfg
    }

-- | Modulo for Number (fmod equivalent)
mod' :: Number -> Number -> Number
mod' x y = x - (toNumber (floor (x / y))) * y

-- | Helper to fold over points
foldPoints :: Int -> SeededRandomState
           -> (Int -> SeededRandomState -> { track :: Array { x :: Number, y :: Number }
                                           , vis :: Array Boolean
                                           , state :: SeededRandomState })
           -> { tracks :: Array (Array { x :: Number, y :: Number })
              , visibility :: Array (Array Boolean) }
foldPoints numPoints initialRng genFn =
  let
    go i rng accTracks accVis
      | i >= numPoints = { tracks: accTracks, visibility: accVis }
      | otherwise =
          let result = genFn i rng
          in go (i + 1) result.state (snoc accTracks result.track) (snoc accVis result.vis)
  in
    go 0 initialRng [] []

--------------------------------------------------------------------------------
-- Explosion Flow Generator
--------------------------------------------------------------------------------

-- | Generate explosion/big bang pattern
generateExplosionFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateExplosionFlow cfg =
  let
    seed = getSeed cfg.params
    width = toNumber cfg.width
    height = toNumber cfg.height
    explosionSpeed = fromMaybe 1.0 cfg.params.explosionSpeed
    decay = fromMaybe 0.95 cfg.params.explosionDecay
    center = fromMaybe { x: width / 2.0, y: height / 2.0 } cfg.params.explosionCenter
    noise = fromMaybe 0.1 cfg.params.noiseStrength

    generatePoint :: Int -> SeededRandomState
                  -> { track :: Array { x :: Number, y :: Number }
                     , vis :: Array Boolean
                     , state :: SeededRandomState }
    generatePoint i rng =
      let
        r1 = nextWithState rng
        r2 = rangeWithState 0.5 1.5 r1.state
        r3 = nextWithState r2.state

        angle = r1.value * pi * 2.0
        pointSpeed = r2.value * explosionSpeed
        startDelay = r3.value * 0.3

        -- Simulate explosion physics
        frames = range 0 (cfg.numFrames - 1)

        simulateExplosion :: { x :: Number, y :: Number, vx :: Number, vy :: Number, frame :: Int }
                         -> { pos :: { x :: Number, y :: Number }, visible :: Boolean }
        simulateExplosion st =
          let
            t = toNumber st.frame / toNumber cfg.numFrames
          in
            if t < startDelay then
              { pos: { x: center.x, y: center.y }, visible: true }
            else
              let
                noiseX = (simplexNoise2D (toNumber i * 0.1) (toNumber st.frame * 0.1) seed - 0.5) * noise * 50.0
                noiseY = (simplexNoise2D (toNumber i * 0.1 + 100.0) (toNumber st.frame * 0.1) seed - 0.5) * noise * 50.0
                newX = st.x + st.vx + noiseX
                newY = st.y + st.vy + noiseY
              in
                { pos: { x: clamp 0.0 width newX, y: clamp 0.0 height newY }
                , visible: newX >= 0.0 && newX <= width && newY >= 0.0 && newY <= height
                }

        -- Generate all frames with velocity decay
        generateFrames :: Int -> Number -> Number -> Number -> Number
                       -> Array { x :: Number, y :: Number } -> Array Boolean
                       -> { track :: Array { x :: Number, y :: Number }, vis :: Array Boolean }
        generateFrames f x y vx vy accTrack accVis
          | f >= cfg.numFrames = { track: accTrack, vis: accVis }
          | otherwise =
              let
                t = toNumber f / toNumber cfg.numFrames
                result =
                  if t < startDelay then
                    { newX: center.x, newY: center.y, newVx: vx, newVy: vy, visible: true }
                  else
                    let
                      noiseX = (simplexNoise2D (toNumber i * 0.1) (toNumber f * 0.1) seed - 0.5) * noise * 50.0
                      noiseY = (simplexNoise2D (toNumber i * 0.1 + 100.0) (toNumber f * 0.1) seed - 0.5) * noise * 50.0
                    in
                      { newX: x + vx + noiseX
                      , newY: y + vy + noiseY
                      , newVx: vx * decay
                      , newVy: vy * decay
                      , visible: (x + vx + noiseX) >= 0.0 && (x + vx + noiseX) <= width &&
                                 (y + vy + noiseY) >= 0.0 && (y + vy + noiseY) <= height
                      }
              in
                generateFrames (f + 1) result.newX result.newY result.newVx result.newVy
                  (snoc accTrack { x: clamp 0.0 width result.newX, y: clamp 0.0 height result.newY })
                  (snoc accVis result.visible)

        initialVx = cos angle * pointSpeed * 20.0
        initialVy = sin angle * pointSpeed * 20.0
        frameResult = generateFrames 0 center.x center.y initialVx initialVy [] []
      in
        { track: frameResult.track
        , vis: frameResult.vis
        , state: r3.state
        }

    result = foldPoints cfg.numPoints (initialState seed) generatePoint
  in
    { tracks: result.tracks
    , visibility: result.visibility
    , metadata: makeMetadata cfg
    }

--------------------------------------------------------------------------------
-- Vortex Flow Generator
--------------------------------------------------------------------------------

-- | Generate vortex/whirlpool pattern
generateVortexFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateVortexFlow cfg =
  let
    seed = getSeed cfg.params
    width = toNumber cfg.width
    height = toNumber cfg.height
    strength = fromMaybe 0.5 cfg.params.vortexStrength
    maxRadius = fromMaybe (min width height * 0.4) cfg.params.vortexRadius
    center = fromMaybe { x: width / 2.0, y: height / 2.0 } cfg.params.vortexCenter
    noise = fromMaybe 0.05 cfg.params.noiseStrength

    generatePoint :: Int -> SeededRandomState
                  -> { track :: Array { x :: Number, y :: Number }
                     , vis :: Array Boolean
                     , state :: SeededRandomState }
    generatePoint i rng =
      let
        r1 = nextWithState rng
        r2 = rangeWithState (maxRadius * 0.2) maxRadius r1.state

        startAngle = r1.value * pi * 2.0
        startRadius = r2.value

        -- Generate vortex spiral frames
        generateFrames :: Int -> Number -> Number
                       -> Array { x :: Number, y :: Number } -> Array Boolean
                       -> { track :: Array { x :: Number, y :: Number }, vis :: Array Boolean }
        generateFrames f angle radius accTrack accVis
          | f >= cfg.numFrames = { track: accTrack, vis: accVis }
          | otherwise =
              let
                -- Spiral inward while rotating
                newAngle = angle + strength * (1.0 + (maxRadius - radius) / maxRadius * 2.0)
                newRadius = max 10.0 (radius - radius * 0.01 * strength)
                noiseVal = simplexNoise2D newAngle (newRadius * 0.01) seed
                noisedRadius = newRadius * (1.0 + (noiseVal - 0.5) * noise)
                x = center.x + cos newAngle * noisedRadius
                y = center.y + sin newAngle * noisedRadius
              in
                generateFrames (f + 1) newAngle newRadius
                  (snoc accTrack { x: clamp 0.0 width x, y: clamp 0.0 height y })
                  (snoc accVis true)

        frameResult = generateFrames 0 startAngle startRadius [] []
      in
        { track: frameResult.track
        , vis: frameResult.vis
        , state: r2.state
        }

    result = foldPoints cfg.numPoints (initialState seed) generatePoint
  in
    { tracks: result.tracks
    , visibility: result.visibility
    , metadata: makeMetadata cfg
    }

--------------------------------------------------------------------------------
-- Remaining generators (DataRiver, Morph, Swarm) from Generators2
--------------------------------------------------------------------------------

import Lattice.Services.Export.FlowGenerators.Generators2 as G2

generateDataRiverFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateDataRiverFlow = G2.generateDataRiverFlow

generateMorphFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateMorphFlow = G2.generateMorphFlow

generateSwarmFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateSwarmFlow = G2.generateSwarmFlow
