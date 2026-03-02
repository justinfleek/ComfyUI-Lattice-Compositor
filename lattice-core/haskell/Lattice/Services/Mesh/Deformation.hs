{-|
Module      : Lattice.Services.Mesh.Deformation
Description : Mesh Warp Deformation
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for mesh deformation using control pins.
Uses inverse-distance weighting for smooth deformations.

Features:
- Inverse-distance weight calculation
- Point rotation around origin
- Point scaling around origin
- Weighted vertex blending

Source: ui/src/services/meshWarpDeformation.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Mesh.Deformation
  ( -- * Types
    Point2D(..)
  , WeightOptions(..)
  , PinState(..)
  , PinRestState(..)
    -- * Defaults
  , defaultWeightOptions
    -- * Point Operations
  , distance
  , rotatePoint
  , scalePoint
  , translatePoint
    -- * Weight Calculation
  , calculatePinWeight
  , calculateWeights
    -- * Deformation
  , applyPinTransform
  , deformVertex
  , deformMesh
    -- * Utilities
  , createPinState
  , lerpPoint
  , lerp
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D point
data Point2D = Point2D
  { p2dX :: Double
  , p2dY :: Double
  } deriving (Show, Eq)

-- | Weight calculation options
data WeightOptions = WeightOptions
  { woFalloffPower :: Double  -- ^ Power for inverse distance falloff
  , woMinWeight    :: Double  -- ^ Minimum weight threshold
  , woNormalize    :: Bool    -- ^ Whether to normalize weights
  } deriving (Show, Eq)

-- | Default weight options
defaultWeightOptions :: WeightOptions
defaultWeightOptions = WeightOptions
  { woFalloffPower = 2.0
  , woMinWeight = 0.001
  , woNormalize = True
  }

-- | Pin state at a specific frame
data PinState = PinState
  { psPosition :: Point2D
  , psRotation :: Double  -- ^ degrees
  , psScale    :: Double
  , psDelta    :: Point2D -- ^ position - restPosition
  } deriving (Show, Eq)

-- | Pin rest state (initial pose)
data PinRestState = PinRestState
  { prsPosition  :: Point2D
  , prsRotation  :: Double
  , prsScale     :: Double
  , prsRadius    :: Double
  , prsStiffness :: Double
  } deriving (Show, Eq)

-- | Default pin rest state
defaultPinRestState :: Point2D -> PinRestState
defaultPinRestState pos = PinRestState
  { prsPosition = pos
  , prsRotation = 0
  , prsScale = 1
  , prsRadius = 100.0
  , prsStiffness = 0.0
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Point Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Distance between two points
distance :: Point2D -> Point2D -> Double
distance a b =
  let dx = p2dX b - p2dX a
      dy = p2dY b - p2dY a
  in sqrt (dx * dx + dy * dy)

-- | Rotate a point around an origin
rotatePoint :: Point2D -> Point2D -> Double -> Point2D
rotatePoint point origin angleDegrees =
  let angleRadians = angleDegrees * pi / 180.0
      cosA = cos angleRadians
      sinA = sin angleRadians
      dx = p2dX point - p2dX origin
      dy = p2dY point - p2dY origin
  in Point2D
       (p2dX origin + dx * cosA - dy * sinA)
       (p2dY origin + dx * sinA + dy * cosA)

-- | Scale a point relative to an origin
scalePoint :: Point2D -> Point2D -> Double -> Point2D
scalePoint point origin scale = Point2D
  (p2dX origin + (p2dX point - p2dX origin) * scale)
  (p2dY origin + (p2dY point - p2dY origin) * scale)

-- | Translate a point by a delta
translatePoint :: Point2D -> Point2D -> Point2D
translatePoint point delta = Point2D
  (p2dX point + p2dX delta)
  (p2dY point + p2dY delta)

-- ────────────────────────────────────────────────────────────────────────────
-- Weight Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate weight for a single vertex-pin pair.
--
-- Uses inverse distance weighting with smooth falloff.
--
-- Formula: weight = (1 / (1 + normalizedDist))^falloffPower
-- where normalizedDist = distance / radius
calculatePinWeight :: Point2D -> Point2D -> Double -> Double -> WeightOptions -> Double
calculatePinWeight vertex pinPos radius stiffness options =
  let dist = distance vertex pinPos
      weight
        | dist < 0.001 = 1000.0  -- Very close - high weight
        | dist > radius * 3.0 = 0.0  -- Too far - no influence
        | otherwise =
            let normalizedDist = dist / radius
                baseWeight = (1.0 / (1.0 + normalizedDist)) ** woFalloffPower options
            in if stiffness > 0.0
               then baseWeight * (1.0 - stiffness * 0.5)
               else baseWeight
  in if weight < woMinWeight options then 0.0 else weight

-- | Calculate weights for all vertex-pin pairs.
--
-- Returns flattened vector: weights[v * pinCount + p] = weight of pin p on vertex v
calculateWeights :: Vector Point2D -> Vector PinRestState -> WeightOptions -> Vector Double
calculateWeights vertices pinRestStates options
  | V.null pinRestStates = V.empty
  | otherwise =
      let pinCount = V.length pinRestStates
          processVertex vertex =
            let vertexWeights = V.map (\pin ->
                  calculatePinWeight vertex (prsPosition pin) (prsRadius pin)
                    (prsStiffness pin) options
                  ) pinRestStates
                totalWeight = V.sum vertexWeights
                normalizedWeights =
                  if woNormalize options && totalWeight > 0.0
                  then V.map (/ totalWeight) vertexWeights
                  else vertexWeights
            in normalizedWeights
      in V.concatMap processVertex vertices

-- ────────────────────────────────────────────────────────────────────────────
-- Deformation Application
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply a single pin's transformation to a vertex.
--
-- Handles translation, rotation, and scale based on pin delta.
applyPinTransform :: Point2D -> PinState -> PinRestState
                  -> Bool -> Bool -> Bool -> Point2D
applyPinTransform vertex pinState restState
                  applyTranslation applyRotation applyScale =
  let
      -- Apply translation
      v1 = if applyTranslation
           then translatePoint vertex (psDelta pinState)
           else vertex

      -- Apply rotation around pin position
      v2 = if applyRotation
           then let rotationDelta = psRotation pinState - prsRotation restState
                in if abs rotationDelta > 0.001
                   then rotatePoint v1 (psPosition pinState) rotationDelta
                   else v1
           else v1

      -- Apply scale around pin position
      v3 = if applyScale
           then if abs (psScale pinState - prsScale restState) > 0.001
                then let scaleDelta = psScale pinState / prsScale restState
                     in scalePoint v2 (psPosition pinState) scaleDelta
                else v2
           else v2
  in v3

-- | Deform a single vertex using weighted pin influences.
--
-- Computes weighted average of per-pin deformed positions.
deformVertex :: Point2D -> Int -> Vector PinState -> Vector PinRestState
             -> Vector Double -> Point2D
deformVertex vertex vertexIndex pinStates pinRestStates weights
  | V.null pinStates = vertex
  | otherwise =
      let pinCount = V.length pinStates
          -- Accumulate weighted positions
          (totalX, totalY, totalWeight) = V.ifoldl'
            (\(accX, accY, accW) p _ ->
              let weight = weights V.! (vertexIndex * pinCount + p)
              in if weight <= 0.0
                 then (accX, accY, accW)
                 else
                   let pinState = pinStates V.! p
                       restState = pinRestStates V.! p
                       deformed = applyPinTransform vertex pinState restState
                                    True True True
                   in (accX + p2dX deformed * weight,
                       accY + p2dY deformed * weight,
                       accW + weight)
            ) (0.0, 0.0, 0.0) pinStates
      in if totalWeight > 0.0
         then Point2D (totalX / totalWeight) (totalY / totalWeight)
         else vertex

-- | Deform all vertices in a mesh.
--
-- Returns vector of deformed vertex positions.
deformMesh :: Vector Point2D -> Vector PinState -> Vector PinRestState
           -> Vector Double -> Vector Point2D
deformMesh vertices pinStates pinRestStates weights =
  V.imap (\i vertex -> deformVertex vertex i pinStates pinRestStates weights) vertices

-- ────────────────────────────────────────────────────────────────────────────
-- Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Create pin state from current and rest positions
createPinState :: Point2D -> Double -> Double -> Point2D -> PinState
createPinState position rotation scale restPosition = PinState
  { psPosition = position
  , psRotation = rotation
  , psScale = scale
  , psDelta = Point2D (p2dX position - p2dX restPosition)
                      (p2dY position - p2dY restPosition)
  }

-- | Linear interpolation between two points
lerpPoint :: Point2D -> Point2D -> Double -> Point2D
lerpPoint a b t =
  let tc = max 0.0 (min 1.0 t)
  in Point2D
       (p2dX a + (p2dX b - p2dX a) * tc)
       (p2dY a + (p2dY b - p2dY a) * tc)

-- | Linear interpolation between two values
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * max 0.0 (min 1.0 t)
