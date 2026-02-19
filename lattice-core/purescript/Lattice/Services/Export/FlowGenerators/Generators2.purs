-- | Lattice.Services.Export.FlowGenerators.Generators2 - Additional patterns
-- |
-- | DataRiver, Morph, and Swarm flow generators.
-- |
-- | Source: ui/src/services/export/wanMoveFlowGenerators.ts

module Lattice.Services.Export.FlowGenerators.Generators2
  ( generateDataRiverFlow
  , generateMorphFlow
  , generateSwarmFlow
  ) where

import Prelude
import Data.Array (range, snoc, length, mapWithIndex, (!!), updateAt, replicate)
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (sqrt, cos, sin, pi, ceil)
import Data.Foldable (foldl, sum)

import Lattice.Services.Export.FlowGenerators.Types
  ( WanMoveTrajectory
  , TrajectoryMetadata
  , GenerativeFlowConfig
  , GenerativeFlowParams
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
-- Helpers
--------------------------------------------------------------------------------

clamp :: Number -> Number -> Number -> Number
clamp lo hi x = max lo (min hi x)

min :: forall a. Ord a => a -> a -> a
min a b = if a < b then a else b

max :: forall a. Ord a => a -> a -> a
max a b = if a > b then a else b

getSeed :: GenerativeFlowParams -> Int
getSeed params = fromMaybe 42 params.seed

makeMetadata :: GenerativeFlowConfig -> TrajectoryMetadata
makeMetadata cfg =
  { numPoints: cfg.numPoints
  , numFrames: cfg.numFrames
  , width: cfg.width
  , height: cfg.height
  , fps: 16
  }

--------------------------------------------------------------------------------
-- Data River Flow Generator
--------------------------------------------------------------------------------

-- | Generate data river flow (particles flowing along a curved path)
generateDataRiverFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateDataRiverFlow cfg =
  let
    seed = getSeed cfg.params
    width = toNumber cfg.width
    height = toNumber cfg.height
    riverWidth = fromMaybe (height * 0.3) cfg.params.riverWidth
    curve = fromMaybe 0.5 cfg.params.riverCurve
    turbulence = fromMaybe 0.1 cfg.params.riverTurbulence

    -- River path (S-curve from left to right)
    riverPath :: Number -> Number
    riverPath x =
      let t = x / width
      in height / 2.0 + sin (t * pi * 2.0 * curve) * height * 0.25

    generatePoint :: Int -> SeededRandomState
                  -> { track :: Array { x :: Number, y :: Number }
                     , vis :: Array Boolean
                     , state :: SeededRandomState }
    generatePoint i rng =
      let
        r1 = rangeWithState (-width * 0.1) (width * 0.3) rng
        r2 = gaussianWithState 0.0 (riverWidth * 0.15) r1.state
        r3 = rangeWithState 0.8 1.2 r2.state

        startX = r1.value
        laneOffset = r2.value
        speed = r3.value

        frames = range 0 (cfg.numFrames - 1)
        generateFrame f =
          let
            t = toNumber f / toNumber cfg.numFrames
            x = startX + t * width * speed * 1.3
            baseY = riverPath x
            turbNoise = simplexNoise2D (x * 0.01) (toNumber f * 0.05 + toNumber i * 0.1) seed
            y = baseY + laneOffset + (turbNoise - 0.5) * riverWidth * turbulence * 2.0
          in
            { pos: { x: clamp 0.0 width x, y: clamp 0.0 height y }
            , visible: x >= 0.0 && x <= width
            }

        frameResults = map generateFrame frames
      in
        { track: map _.pos frameResults
        , vis: map _.visible frameResults
        , state: r3.state
        }

    result = foldPoints cfg.numPoints (initialState seed) generatePoint
  in
    { tracks: result.tracks
    , visibility: result.visibility
    , metadata: makeMetadata cfg
    }

--------------------------------------------------------------------------------
-- Morph Flow Generator
--------------------------------------------------------------------------------

-- | Generate morph flow (points transitioning between two shapes)
generateMorphFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateMorphFlow cfg =
  let
    seed = getSeed cfg.params
    width = toNumber cfg.width
    height = toNumber cfg.height
    sourceShape = fromMaybe ShapeGrid cfg.params.morphSource
    targetShape = fromMaybe ShapeCircle cfg.params.morphTarget
    easing = fromMaybe EasingInOut cfg.params.morphEasing

    -- Generate positions for a shape
    generateShapePositions :: MorphShape -> SeededRandomState -> Int
                           -> { positions :: Array { x :: Number, y :: Number }
                              , state :: SeededRandomState }
    generateShapePositions shape rng count = case shape of
      ShapeGrid ->
        let
          cols = floor (ceil (sqrt (toNumber count)))
          positions = mapWithIndex (\i _ ->
            let
              row = floor (toNumber i / toNumber cols)
              col = i `mod` cols
            in
              { x: (toNumber col + 0.5) / toNumber cols * width * 0.8 + width * 0.1
              , y: (toNumber row + 0.5) / toNumber cols * height * 0.8 + height * 0.1
              }
          ) (range 0 (count - 1))
        in
          { positions, state: rng }

      ShapeCircle ->
        let
          radius = min width height * 0.35
          positions = mapWithIndex (\i _ ->
            let angle = toNumber i / toNumber count * pi * 2.0
            in { x: width / 2.0 + cos angle * radius
               , y: height / 2.0 + sin angle * radius
               }
          ) (range 0 (count - 1))
        in
          { positions, state: rng }

      ShapeRandom ->
        let
          go :: Int -> SeededRandomState -> Array { x :: Number, y :: Number }
             -> { positions :: Array { x :: Number, y :: Number }, state :: SeededRandomState }
          go n st acc
            | n <= 0 = { positions: acc, state: st }
            | otherwise =
                let
                  r1 = nextWithState st
                  r2 = nextWithState r1.state
                in
                  go (n - 1) r2.state (snoc acc { x: r1.value * width, y: r2.value * height })
        in
          go count rng []

    -- Easing function
    applyEasing :: Number -> Number
    applyEasing t = case easing of
      EasingLinear -> t
      EasingIn -> t * t
      EasingOut -> 1.0 - (1.0 - t) * (1.0 - t)
      EasingInOut ->
        if t < 0.5
        then 2.0 * t * t
        else 1.0 - ((-2.0 * t + 2.0) * (-2.0 * t + 2.0)) / 2.0

    -- Generate source and target positions
    rng0 = initialState seed
    srcResult = generateShapePositions sourceShape rng0 cfg.numPoints
    tgtResult = generateShapePositions targetShape srcResult.state cfg.numPoints

    -- Generate tracks by interpolating between source and target
    generateTracks :: Array { x :: Number, y :: Number }
                   -> Array { x :: Number, y :: Number }
                   -> { tracks :: Array (Array { x :: Number, y :: Number })
                      , visibility :: Array (Array Boolean) }
    generateTracks sources targets =
      let
        tracks = mapWithIndex (\i src ->
          let
            tgt = fromMaybe src (targets !! i)
            frames = range 0 (cfg.numFrames - 1)
          in
            map (\f ->
              let
                t = toNumber f / toNumber (cfg.numFrames - 1)
                easedT = applyEasing t
                noise = simplexNoise2D (toNumber i * 0.1) (toNumber f * 0.02) seed
                noiseOffset = (noise - 0.5) * 20.0 * (1.0 - (t - 0.5) * (t - 0.5) * 4.0)
                x = src.x + (tgt.x - src.x) * easedT + noiseOffset
                y = src.y + (tgt.y - src.y) * easedT + noiseOffset
              in
                { x: clamp 0.0 width x, y: clamp 0.0 height y }
            ) frames
        ) sources
        visibility = map (\track -> map (\_ -> true) track) tracks
      in
        { tracks, visibility }

    result = generateTracks srcResult.positions tgtResult.positions
  in
    { tracks: result.tracks
    , visibility: result.visibility
    , metadata: makeMetadata cfg
    }

--------------------------------------------------------------------------------
-- Swarm Flow Generator
--------------------------------------------------------------------------------

-- | Particle state for swarm simulation
type Particle =
  { x :: Number
  , y :: Number
  , vx :: Number
  , vy :: Number
  }

-- | Generate swarm/flocking behavior pattern
generateSwarmFlow :: GenerativeFlowConfig -> WanMoveTrajectory
generateSwarmFlow cfg =
  let
    seed = getSeed cfg.params
    width = toNumber cfg.width
    height = toNumber cfg.height
    cohesion = fromMaybe 0.01 cfg.params.swarmCohesion
    separation = fromMaybe 30.0 cfg.params.swarmSeparation
    alignment = fromMaybe 0.05 cfg.params.swarmAlignment
    maxSpeed = fromMaybe 5.0 cfg.params.swarmSpeed

    -- Initialize particles
    initParticles :: SeededRandomState -> Array Particle
    initParticles rng =
      let
        go n st acc
          | n <= 0 = acc
          | otherwise =
              let
                r1 = nextWithState st
                r2 = nextWithState r1.state
                r3 = rangeWithState (-maxSpeed) maxSpeed r2.state
                r4 = rangeWithState (-maxSpeed) maxSpeed r3.state
                particle = { x: r1.value * width
                           , y: r2.value * height
                           , vx: r3.value
                           , vy: r4.value
                           }
              in
                go (n - 1) r4.state (snoc acc particle)
      in
        go cfg.numPoints rng []

    -- Calculate center of mass
    centerOfMass :: Array Particle -> { cx :: Number, cy :: Number }
    centerOfMass particles =
      let
        n = toNumber (length particles)
        sumX = foldl (\acc p -> acc + p.x) 0.0 particles
        sumY = foldl (\acc p -> acc + p.y) 0.0 particles
      in
        { cx: sumX / n, cy: sumY / n }

    -- Update one particle with swarm forces
    updateParticle :: { cx :: Number, cy :: Number }
                   -> Array Particle -> Int -> Particle -> Particle
    updateParticle com particles i p =
      let
        -- Cohesion force (toward center)
        cohesionFx = (com.cx - p.x) * cohesion
        cohesionFy = (com.cy - p.y) * cohesion

        -- Separation force (avoid crowding)
        separationForce = foldl (\acc j ->
          if i == j then acc
          else
            case particles !! j of
              Nothing -> acc
              Just other ->
                let
                  dx = p.x - other.x
                  dy = p.y - other.y
                  dist = sqrt (dx * dx + dy * dy)
                in
                  if dist < separation && dist > 0.0 then
                    { fx: acc.fx + (dx / dist) * (separation - dist) * 0.1
                    , fy: acc.fy + (dy / dist) * (separation - dist) * 0.1
                    }
                  else acc
        ) { fx: 0.0, fy: 0.0 } (range 0 (length particles - 1))

        -- Alignment force (match nearby velocity)
        nearbyStart = max 0 (i - 10)
        nearbyEnd = min (length particles) (i + 10)
        avgVel = foldl (\acc j ->
          case particles !! j of
            Nothing -> acc
            Just other ->
              { vx: acc.vx + other.vx
              , vy: acc.vy + other.vy
              , count: acc.count + 1
              }
        ) { vx: 0.0, vy: 0.0, count: 0 } (range nearbyStart (nearbyEnd - 1))

        alignmentFx = if avgVel.count > 0 then (avgVel.vx / toNumber avgVel.count - p.vx) * alignment else 0.0
        alignmentFy = if avgVel.count > 0 then (avgVel.vy / toNumber avgVel.count - p.vy) * alignment else 0.0

        -- Boundary avoidance
        margin = 50.0
        boundFx = (if p.x < margin then (margin - p.x) * 0.1 else 0.0) +
                  (if p.x > width - margin then -(p.x - (width - margin)) * 0.1 else 0.0)
        boundFy = (if p.y < margin then (margin - p.y) * 0.1 else 0.0) +
                  (if p.y > height - margin then -(p.y - (height - margin)) * 0.1 else 0.0)

        -- Apply forces
        newVx = p.vx + cohesionFx + separationForce.fx + alignmentFx + boundFx
        newVy = p.vy + cohesionFy + separationForce.fy + alignmentFy + boundFy

        -- Limit speed
        speed = sqrt (newVx * newVx + newVy * newVy)
        limitedVx = if speed > maxSpeed then newVx / speed * maxSpeed else newVx
        limitedVy = if speed > maxSpeed then newVy / speed * maxSpeed else newVy
      in
        { x: p.x + limitedVx
        , y: p.y + limitedVy
        , vx: limitedVx
        , vy: limitedVy
        }

    -- Simulate all frames
    particles0 = initParticles (initialState seed)

    simulateFrames :: Int -> Array Particle
                   -> Array (Array { x :: Number, y :: Number })
                   -> { tracks :: Array (Array { x :: Number, y :: Number }) }
    simulateFrames f particles accTracks
      | f >= cfg.numFrames = { tracks: accTracks }
      | otherwise =
          let
            com = centerOfMass particles
            newParticles = mapWithIndex (updateParticle com particles) particles
            framePositions = map (\p -> { x: clamp 0.0 width p.x, y: clamp 0.0 height p.y }) newParticles
            -- Append this frame's positions to each track
            newTracks = mapWithIndex (\i track ->
              case framePositions !! i of
                Just pos -> snoc track pos
                Nothing -> track
            ) accTracks
          in
            simulateFrames (f + 1) newParticles newTracks

    emptyTracks = replicate cfg.numPoints []
    result = simulateFrames 0 particles0 emptyTracks
    visibility = map (\track -> map (\_ -> true) track) result.tracks
  in
    { tracks: result.tracks
    , visibility
    , metadata: makeMetadata cfg
    }

--------------------------------------------------------------------------------
-- Helper
--------------------------------------------------------------------------------

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
