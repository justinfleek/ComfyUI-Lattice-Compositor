-- | Lattice.Services.Export.WanMoveExport.Colors - Color gradient handling
-- |
-- | Color gradients and trajectory coloring for data visualization.
-- |
-- | Source: ui/src/services/export/wanMoveExport.ts

module Lattice.Services.Export.WanMoveExport.Colors
  ( -- * Color Gradients
    viridisGradient
  , plasmaGradient
  , infernoGradient
  , coolWarmGradient
  , rainbowGradient
  , depthGradient
  , getGradient
    -- * Color Sampling
  , sampleGradient
  , normalizeData
    -- * Trajectory Coloring
  , addColorToTrajectory
  , addTimeColorToTrajectory
  ) where

import Prelude
import Data.Array (length, (!!), foldl, range)
import Data.Int (round, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)

import Lattice.Services.Export.WanMoveExport.Types
  ( WanMoveTrajectory
  , ColoredTrajectory
  , ColorGradient
  , GradientStop
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Built-in Gradients
-- ────────────────────────────────────────────────────────────────────────────

-- | Viridis gradient (perceptually uniform, colorblind-friendly)
viridisGradient :: ColorGradient
viridisGradient =
  { stops:
      [ { position: 0.0, color: { r: 68, g: 1, b: 84 } }
      , { position: 0.25, color: { r: 59, g: 82, b: 139 } }
      , { position: 0.5, color: { r: 33, g: 145, b: 140 } }
      , { position: 0.75, color: { r: 94, g: 201, b: 98 } }
      , { position: 1.0, color: { r: 253, g: 231, b: 37 } }
      ]
  }

-- | Plasma gradient
plasmaGradient :: ColorGradient
plasmaGradient =
  { stops:
      [ { position: 0.0, color: { r: 13, g: 8, b: 135 } }
      , { position: 0.25, color: { r: 126, g: 3, b: 168 } }
      , { position: 0.5, color: { r: 204, g: 71, b: 120 } }
      , { position: 0.75, color: { r: 248, g: 149, b: 64 } }
      , { position: 1.0, color: { r: 240, g: 249, b: 33 } }
      ]
  }

-- | Inferno gradient
infernoGradient :: ColorGradient
infernoGradient =
  { stops:
      [ { position: 0.0, color: { r: 0, g: 0, b: 4 } }
      , { position: 0.25, color: { r: 87, g: 16, b: 110 } }
      , { position: 0.5, color: { r: 188, g: 55, b: 84 } }
      , { position: 0.75, color: { r: 249, g: 142, b: 9 } }
      , { position: 1.0, color: { r: 252, g: 255, b: 164 } }
      ]
  }

-- | Cool-warm diverging gradient
coolWarmGradient :: ColorGradient
coolWarmGradient =
  { stops:
      [ { position: 0.0, color: { r: 59, g: 76, b: 192 } }
      , { position: 0.5, color: { r: 221, g: 221, b: 221 } }
      , { position: 1.0, color: { r: 180, g: 4, b: 38 } }
      ]
  }

-- | Rainbow gradient
rainbowGradient :: ColorGradient
rainbowGradient =
  { stops:
      [ { position: 0.0, color: { r: 255, g: 0, b: 0 } }
      , { position: 0.2, color: { r: 255, g: 165, b: 0 } }
      , { position: 0.4, color: { r: 255, g: 255, b: 0 } }
      , { position: 0.6, color: { r: 0, g: 255, b: 0 } }
      , { position: 0.8, color: { r: 0, g: 0, b: 255 } }
      , { position: 1.0, color: { r: 128, g: 0, b: 128 } }
      ]
  }

-- | Depth gradient (black to white)
depthGradient :: ColorGradient
depthGradient =
  { stops:
      [ { position: 0.0, color: { r: 0, g: 0, b: 0 } }
      , { position: 1.0, color: { r: 255, g: 255, b: 255 } }
      ]
  }

-- | Get gradient by name
getGradient :: String -> ColorGradient
getGradient name = case name of
  "viridis" -> viridisGradient
  "plasma" -> plasmaGradient
  "inferno" -> infernoGradient
  "cool-warm" -> coolWarmGradient
  "rainbow" -> rainbowGradient
  "depth" -> depthGradient
  _ -> viridisGradient  -- Default

-- ────────────────────────────────────────────────────────────────────────────
-- Color Sampling
-- ────────────────────────────────────────────────────────────────────────────

-- | Sample color from gradient at position t ∈ [0, 1]
sampleGradient :: ColorGradient -> Number -> { r :: Int, g :: Int, b :: Int }
sampleGradient gradient t =
  let
    clampedT = max 0.0 (min 1.0 t)
    stops = gradient.stops
    n = length stops
  in
    if n == 0 then
      { r: 128, g: 128, b: 128 }
    else if n == 1 then
      let firstStop = fromMaybe { position: 0.0, color: { r: 128, g: 128, b: 128 } } (stops !! 0)
      in firstStop.color
    else
      interpolateGradient stops clampedT

-- | Interpolate between gradient stops
interpolateGradient :: Array GradientStop -> Number -> { r :: Int, g :: Int, b :: Int }
interpolateGradient stops t =
  let
    -- Find surrounding stops
    findStops :: GradientStop -> GradientStop -> Int -> { lower :: GradientStop, upper :: GradientStop }
    findStops lower upper idx =
      if idx >= length stops - 1 then
        { lower, upper }
      else
        let
          current = fromMaybe lower (stops !! idx)
          next = fromMaybe current (stops !! (idx + 1))
        in
          if t >= current.position && t <= next.position then
            { lower: current, upper: next }
          else
            findStops lower upper (idx + 1)

    first = fromMaybe { position: 0.0, color: { r: 0, g: 0, b: 0 } } (stops !! 0)
    last = fromMaybe first (stops !! (length stops - 1))

    { lower, upper } = findStops first last 0

    -- Interpolate
    range = upper.position - lower.position
    localT = if range > 0.0 then (t - lower.position) / range else 0.0
  in
    { r: round (toNumber lower.color.r + (toNumber upper.color.r - toNumber lower.color.r) * localT)
    , g: round (toNumber lower.color.g + (toNumber upper.color.g - toNumber lower.color.g) * localT)
    , b: round (toNumber lower.color.b + (toNumber upper.color.b - toNumber lower.color.b) * localT)
    }

-- | Normalize data values to 0-1 range
normalizeData :: Array Number -> Array Number
normalizeData values =
  let
    minVal = foldl min 0.0 values
    maxVal = foldl max 0.0 values
    range = maxVal - minVal
    safeRange = if range > 0.0 then range else 1.0
  in
    map (\v -> (v - minVal) / safeRange) values

-- ────────────────────────────────────────────────────────────────────────────
-- Trajectory Coloring
-- ────────────────────────────────────────────────────────────────────────────

-- | Add color data to trajectory based on data values
addColorToTrajectory
  :: WanMoveTrajectory
  -> Array Number
  -> String  -- gradient name
  -> ColoredTrajectory
addColorToTrajectory trajectory dataValues gradientName =
  let
    gradient = getGradient gradientName
    normalized = normalizeData dataValues
    numTracks = length trajectory.tracks
    numData = length normalized

    colors = map (\i ->
      let
        dataIdx = i `mod` numData
        normalizedValue = fromMaybe 0.5 (normalized !! dataIdx)
        color = sampleGradient gradient normalizedValue
        trackLen = case trajectory.tracks !! i of
          Just track -> length track
          Nothing -> 0
      in
        -- Same color for all frames of this trajectory
        map (\_ -> color) (range 0 (trackLen - 1))
    ) (range 0 (numTracks - 1))
  in
    { tracks: trajectory.tracks
    , visibility: trajectory.visibility
    , metadata: trajectory.metadata
    , colors: Just colors
    , dataValues: Just dataValues
    , trailLength: Nothing
    }

-- | Add time-based color (earlier = one color, later = another)
addTimeColorToTrajectory
  :: WanMoveTrajectory
  -> String  -- gradient name
  -> ColoredTrajectory
addTimeColorToTrajectory trajectory gradientName =
  let
    gradient = getGradient gradientName
    numFrames = trajectory.metadata.numFrames
    numTracks = length trajectory.tracks

    colors = map (\i ->
      let
        trackLen = case trajectory.tracks !! i of
          Just track -> length track
          Nothing -> 0
      in
        map (\f ->
          let
            t = if numFrames > 1 then toNumber f / toNumber (numFrames - 1) else 0.0
          in
            sampleGradient gradient t
        ) (range 0 (trackLen - 1))
    ) (range 0 (numTracks - 1))
  in
    { tracks: trajectory.tracks
    , visibility: trajectory.visibility
    , metadata: trajectory.metadata
    , colors: Just colors
    , dataValues: Nothing
    , trailLength: Nothing
    }

