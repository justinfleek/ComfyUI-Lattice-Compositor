-- | Lattice.Services.Export.WanMoveExport.Attractors - Strange attractors
-- |
-- | Strange attractor trajectory generators (Lorenz, Rossler, Aizawa).
-- | Creates chaotic, organic motion patterns.
-- |
-- | Source: ui/src/services/export/wanMoveExport.ts

module Lattice.Services.Export.WanMoveExport.Attractors
  ( -- * Attractor Generators
    generateLorenzAttractor
  , generateRosslerAttractor
  , generateAizawaAttractor
    -- * Generic Attractor
  , generateAttractor
  ) where

import Prelude
import Data.Array (range, foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Math (sqrt)

import Lattice.Services.Export.WanMoveExport.Types
  ( WanMoveTrajectory
  , AttractorConfig
  , AttractorType(..)
  , TrackPoint
  )
import Lattice.Services.Export.FlowGenerators.SeededRandom (SeededRandomState, initialState, next, rangeWithState) as SRng
import Lattice.Services.Export.FlowGenerators.SeededRandom (SeededRandomState, initialState, next)

-- ────────────────────────────────────────────────────────────────────────────
-- Generic Attractor
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate attractor based on type
generateAttractor :: AttractorConfig -> WanMoveTrajectory
generateAttractor config =
  case config.attractorType of
    AttractorLorenz -> generateLorenzAttractor config
    AttractorRossler -> generateRosslerAttractor config
    AttractorAizawa -> generateAizawaAttractor config
    AttractorThomas -> generateLorenzAttractor config  -- Fallback
    AttractorHalvorsen -> generateLorenzAttractor config  -- Fallback

-- ────────────────────────────────────────────────────────────────────────────
-- Lorenz Attractor
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate Lorenz attractor trajectories
-- | Creates the famous "butterfly" chaotic pattern
generateLorenzAttractor :: AttractorConfig -> WanMoveTrajectory
generateLorenzAttractor config =
  let
    numPoints = config.numPoints
    numFrames = config.numFrames
    width = config.width
    height = config.height
    seed = fromMaybe 42 config.seed
    dt = fromMaybe 0.005 config.dt
    scale = fromMaybe 8.0 config.scale
    center = fromMaybe { x: toNumber width / 2.0, y: toNumber height / 2.0 } config.center

    -- Lorenz parameters
    sigma = 10.0
    rho = 28.0
    beta = 8.0 / 3.0

    -- Generate tracks
    result = foldl (\acc i ->
      let
        rng = initialState (seed + i)
        initial = initLorenzPoint rng
        settled = settleLorenz initial dt sigma rho beta 500
        track = generateLorenzTrack settled dt sigma rho beta scale center width height numFrames
      in
        { tracks: acc.tracks <> [track.points]
        , visibility: acc.visibility <> [track.vis]
        }
    ) { tracks: [], visibility: [] } (range 0 (numPoints - 1))
  in
    { tracks: result.tracks
    , visibility: result.visibility
    , metadata: { numPoints, numFrames, width, height, fps: 16 }
    }

-- | Initialize Lorenz starting point
initLorenzPoint :: SeededRandomState -> { x :: Number, y :: Number, z :: Number }
initLorenzPoint rng =
  let
    rx = SRng.rangeWithState (-0.1) 0.1 rng
    ry = SRng.rangeWithState (-0.1) 0.1 rx.state
    rz = SRng.rangeWithState 20.0 30.0 ry.state
  in
    { x: rx.value, y: ry.value, z: rz.value }

-- | Settle Lorenz system into attractor
settleLorenz
  :: { x :: Number, y :: Number, z :: Number }
  -> Number  -- dt
  -> Number  -- sigma
  -> Number  -- rho
  -> Number  -- beta
  -> Int     -- steps
  -> { x :: Number, y :: Number, z :: Number }
settleLorenz initial dt sigma rho beta steps =
  foldl (\p _ ->
    let
      dx = sigma * (p.y - p.x)
      dy = p.x * (rho - p.z) - p.y
      dz = p.x * p.y - beta * p.z
    in
      { x: p.x + dx * dt
      , y: p.y + dy * dt
      , z: p.z + dz * dt
      }
  ) initial (range 0 (steps - 1))

-- | Generate Lorenz track points
generateLorenzTrack
  :: { x :: Number, y :: Number, z :: Number }
  -> Number  -- dt
  -> Number  -- sigma
  -> Number  -- rho
  -> Number  -- beta
  -> Number  -- scale
  -> TrackPoint  -- center
  -> Int  -- width
  -> Int  -- height
  -> Int  -- numFrames
  -> { points :: Array TrackPoint, vis :: Array Boolean }
generateLorenzTrack initial dt sigma rho beta scale center w h numFrames =
  let
    width = toNumber w
    height = toNumber h
    result = foldl (\acc f ->
      let
        -- Multiple integration steps per frame
        newState = foldl (\p _ ->
          let
            dx = sigma * (p.y - p.x)
            dy = p.x * (rho - p.z) - p.y
            dz = p.x * p.y - beta * p.z
          in
            { x: p.x + dx * dt
            , y: p.y + dy * dt
            , z: p.z + dz * dt
            }
        ) acc.state (range 0 9)

        -- Project to 2D (XZ plane)
        px = center.x + newState.x * scale
        py = center.y + (newState.z - 25.0) * scale

        clampedX = max 0.0 (min width px)
        clampedY = max 0.0 (min height py)
      in
        { state: newState
        , points: acc.points <> [{ x: clampedX, y: clampedY }]
        , vis: acc.vis <> [true]
        }
    ) { state: initial, points: [], vis: [] } (range 0 (numFrames - 1))
  in { points: result.points, vis: result.vis }

-- ────────────────────────────────────────────────────────────────────────────
-- Rossler Attractor
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate Rossler attractor trajectories
-- | Creates a simpler spiral-like chaotic pattern
generateRosslerAttractor :: AttractorConfig -> WanMoveTrajectory
generateRosslerAttractor config =
  let
    numPoints = config.numPoints
    numFrames = config.numFrames
    width = config.width
    height = config.height
    seed = fromMaybe 42 config.seed
    dt = fromMaybe 0.02 config.dt
    scale = fromMaybe 15.0 config.scale
    center = fromMaybe { x: toNumber width / 2.0, y: toNumber height / 2.0 } config.center

    -- Rossler parameters
    a = 0.2
    b = 0.2
    c = 5.7

    result = foldl (\acc i ->
      let
        rng = initialState (seed + i)
        initial = initRosslerPoint rng
        settled = settleRossler initial dt a b c 300
        track = generateRosslerTrack settled dt a b c scale center width height numFrames
      in
        { tracks: acc.tracks <> [track.points]
        , visibility: acc.visibility <> [track.vis]
        }
    ) { tracks: [], visibility: [] } (range 0 (numPoints - 1))
  in
    { tracks: result.tracks
    , visibility: result.visibility
    , metadata: { numPoints, numFrames, width, height, fps: 16 }
    }

-- | Initialize Rossler starting point
initRosslerPoint :: SeededRandomState -> { x :: Number, y :: Number, z :: Number }
initRosslerPoint rng =
  let
    rx = SRng.rangeWithState (-1.0) 1.0 rng
    ry = SRng.rangeWithState (-1.0) 1.0 rx.state
    rz = SRng.rangeWithState 0.0 1.0 ry.state
  in
    { x: rx.value, y: ry.value, z: rz.value }

-- | Settle Rossler system
settleRossler
  :: { x :: Number, y :: Number, z :: Number }
  -> Number  -- dt
  -> Number  -- a
  -> Number  -- b
  -> Number  -- c
  -> Int     -- steps
  -> { x :: Number, y :: Number, z :: Number }
settleRossler initial dt a b c steps =
  foldl (\p _ ->
    let
      dx = negate p.y - p.z
      dy = p.x + a * p.y
      dz = b + p.z * (p.x - c)
    in
      { x: p.x + dx * dt
      , y: p.y + dy * dt
      , z: p.z + dz * dt
      }
  ) initial (range 0 (steps - 1))

-- | Generate Rossler track
generateRosslerTrack
  :: { x :: Number, y :: Number, z :: Number }
  -> Number -> Number -> Number -> Number
  -> Number -> TrackPoint
  -> Int -> Int -> Int
  -> { points :: Array TrackPoint, vis :: Array Boolean }
generateRosslerTrack initial dt a b c scale center w h numFrames =
  let
    width = toNumber w
    height = toNumber h
  in
    let result = foldl (\acc _ ->
          let
            newState = foldl (\p _ ->
              let
                dx = negate p.y - p.z
                dy = p.x + a * p.y
                dz = b + p.z * (p.x - c)
              in
                { x: p.x + dx * dt
                , y: p.y + dy * dt
                , z: p.z + dz * dt
                }
            ) acc.state (range 0 4)

            px = center.x + newState.x * scale
            py = center.y + newState.y * scale

            clampedX = max 0.0 (min width px)
            clampedY = max 0.0 (min height py)
          in
            { state: newState
            , points: acc.points <> [{ x: clampedX, y: clampedY }]
            , vis: acc.vis <> [true]
            }
        ) { state: initial, points: [], vis: [] } (range 0 (numFrames - 1))
    in { points: result.points, vis: result.vis }

-- ────────────────────────────────────────────────────────────────────────────
-- Aizawa Attractor
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate Aizawa attractor (beautiful 3D torus-like chaos)
generateAizawaAttractor :: AttractorConfig -> WanMoveTrajectory
generateAizawaAttractor config =
  let
    numPoints = config.numPoints
    numFrames = config.numFrames
    width = config.width
    height = config.height
    seed = fromMaybe 42 config.seed
    dt = fromMaybe 0.01 config.dt
    scale = fromMaybe 80.0 config.scale
    center = fromMaybe { x: toNumber width / 2.0, y: toNumber height / 2.0 } config.center

    -- Aizawa parameters
    params = { a: 0.95, b: 0.7, c: 0.6, d: 3.5, e: 0.25, f: 0.1 }

    result = foldl (\acc i ->
      let
        rng = initialState (seed + i)
        initial = initAizawaPoint rng
        settled = settleAizawa initial dt params 500
        track = generateAizawaTrack settled dt params scale center width height numFrames
      in
        { tracks: acc.tracks <> [track.points]
        , visibility: acc.visibility <> [track.vis]
        }
    ) { tracks: [], visibility: [] } (range 0 (numPoints - 1))
  in
    { tracks: result.tracks
    , visibility: result.visibility
    , metadata: { numPoints, numFrames, width, height, fps: 16 }
    }

-- | Initialize Aizawa starting point
initAizawaPoint :: SeededRandomState -> { x :: Number, y :: Number, z :: Number }
initAizawaPoint rng =
  let
    rx = SRng.rangeWithState 0.1 0.2 rng
    ry = SRng.rangeWithState 0.0 0.1 rx.state
    rz = SRng.rangeWithState 0.0 0.1 ry.state
  in
    { x: rx.value, y: ry.value, z: rz.value }

-- | Aizawa parameters type
type AizawaParams =
  { a :: Number, b :: Number, c :: Number
  , d :: Number, e :: Number, f :: Number
  }

-- | Settle Aizawa system
settleAizawa
  :: { x :: Number, y :: Number, z :: Number }
  -> Number  -- dt
  -> AizawaParams
  -> Int     -- steps
  -> { x :: Number, y :: Number, z :: Number }
settleAizawa initial dt params steps =
  foldl (\p _ -> aizawaStep p dt params) initial (range 0 (steps - 1))

-- | Single Aizawa integration step
aizawaStep
  :: { x :: Number, y :: Number, z :: Number }
  -> Number
  -> AizawaParams
  -> { x :: Number, y :: Number, z :: Number }
aizawaStep p dt params =
  let
    dx = (p.z - params.b) * p.x - params.d * p.y
    dy = params.d * p.x + (p.z - params.b) * p.y
    dz = params.c + params.a * p.z
       - (p.z * p.z * p.z) / 3.0
       - (p.x * p.x + p.y * p.y) * (1.0 + params.e * p.z)
       + params.f * p.z * p.x * p.x * p.x
  in
    { x: p.x + dx * dt
    , y: p.y + dy * dt
    , z: p.z + dz * dt
    }

-- | Generate Aizawa track
generateAizawaTrack
  :: { x :: Number, y :: Number, z :: Number }
  -> Number -> AizawaParams
  -> Number -> TrackPoint
  -> Int -> Int -> Int
  -> { points :: Array TrackPoint, vis :: Array Boolean }
generateAizawaTrack initial dt params scale center w h numFrames =
  let
    width = toNumber w
    height = toNumber h
    result = foldl (\acc _ ->
      let
        newState = foldl (\p _ -> aizawaStep p dt params) acc.state (range 0 7)

        px = center.x + newState.x * scale
        py = center.y + newState.y * scale

        clampedX = max 0.0 (min width px)
        clampedY = max 0.0 (min height py)
      in
        { state: newState
        , points: acc.points <> [{ x: clampedX, y: clampedY }]
        , vis: acc.vis <> [true]
        }
    ) { state: initial, points: [], vis: [] } (range 0 (numFrames - 1))
  in { points: result.points, vis: result.vis }

