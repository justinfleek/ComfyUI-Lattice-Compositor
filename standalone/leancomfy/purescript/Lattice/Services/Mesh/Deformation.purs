-- | Lattice.Services.Mesh.Deformation - Mesh Warp Deformation
-- |
-- | Pure mathematical functions for mesh deformation using control pins.
-- | Uses inverse-distance weighting for smooth deformations.
-- |
-- | Features:
-- | - Inverse-distance weight calculation
-- | - Point rotation around origin
-- | - Point scaling around origin
-- | - Weighted vertex blending
-- |
-- | Source: ui/src/services/meshWarpDeformation.ts

module Lattice.Services.Mesh.Deformation
  ( Point2D
  , mkPoint2D
  , p2dX
  , p2dY
  , WeightOptions
  , mkWeightOptions
  , defaultWeightOptions
  , PinState
  , mkPinState
  , PinRestState
  , mkPinRestState
  , distance
  , rotatePoint
  , scalePoint
  , translatePoint
  , calculatePinWeight
  , calculateWeights
  , applyPinTransform
  , deformVertex
  , deformMesh
  , createPinState
  , lerpPoint
  , lerp
  ) where

import Prelude

import Data.Array (foldl, length, mapWithIndex, (!!))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Math (abs, cos, pi, pow, sin, sqrt)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D point
newtype Point2D = Point2D { x :: Number, y :: Number }

derive instance eqPoint2D :: Eq Point2D

mkPoint2D :: Number -> Number -> Point2D
mkPoint2D x y = Point2D { x, y }

p2dX :: Point2D -> Number
p2dX (Point2D p) = p.x

p2dY :: Point2D -> Number
p2dY (Point2D p) = p.y

-- | Weight calculation options
type WeightOptions =
  { falloffPower :: Number
  , minWeight :: Number
  , normalize :: Boolean
  }

mkWeightOptions :: Number -> Number -> Boolean -> WeightOptions
mkWeightOptions falloffPower minWeight normalize =
  { falloffPower, minWeight, normalize }

defaultWeightOptions :: WeightOptions
defaultWeightOptions =
  { falloffPower: 2.0
  , minWeight: 0.001
  , normalize: true
  }

-- | Pin state at a specific frame
type PinState =
  { position :: Point2D
  , rotation :: Number  -- degrees
  , scale :: Number
  , delta :: Point2D    -- position - restPosition
  }

mkPinState :: Point2D -> Number -> Number -> Point2D -> PinState
mkPinState position rotation scale delta =
  { position, rotation, scale, delta }

-- | Pin rest state (initial pose)
type PinRestState =
  { position :: Point2D
  , rotation :: Number
  , scale :: Number
  , radius :: Number
  , stiffness :: Number
  }

mkPinRestState :: Point2D -> Number -> Number -> Number -> Number -> PinRestState
mkPinRestState position rotation scale radius stiffness =
  { position, rotation, scale, radius, stiffness }

defaultPinRestState :: Point2D -> PinRestState
defaultPinRestState pos =
  { position: pos
  , rotation: 0.0
  , scale: 1.0
  , radius: 100.0
  , stiffness: 0.0
  }

--------------------------------------------------------------------------------
-- Point Operations
--------------------------------------------------------------------------------

-- | Distance between two points
distance :: Point2D -> Point2D -> Number
distance a b =
  let dx = p2dX b - p2dX a
      dy = p2dY b - p2dY a
  in sqrt (dx * dx + dy * dy)

-- | Rotate a point around an origin
rotatePoint :: Point2D -> Point2D -> Number -> Point2D
rotatePoint point origin angleDegrees =
  let angleRadians = angleDegrees * pi / 180.0
      cosA = cos angleRadians
      sinA = sin angleRadians
      dx = p2dX point - p2dX origin
      dy = p2dY point - p2dY origin
  in mkPoint2D
       (p2dX origin + dx * cosA - dy * sinA)
       (p2dY origin + dx * sinA + dy * cosA)

-- | Scale a point relative to an origin
scalePoint :: Point2D -> Point2D -> Number -> Point2D
scalePoint point origin scale = mkPoint2D
  (p2dX origin + (p2dX point - p2dX origin) * scale)
  (p2dY origin + (p2dY point - p2dY origin) * scale)

-- | Translate a point by a delta
translatePoint :: Point2D -> Point2D -> Point2D
translatePoint point delta = mkPoint2D
  (p2dX point + p2dX delta)
  (p2dY point + p2dY delta)

--------------------------------------------------------------------------------
-- Weight Calculation
--------------------------------------------------------------------------------

-- | Calculate weight for a single vertex-pin pair.
-- |
-- | Uses inverse distance weighting with smooth falloff.
-- |
-- | Formula: weight = (1 / (1 + normalizedDist))^falloffPower
-- | where normalizedDist = distance / radius
calculatePinWeight :: Point2D -> Point2D -> Number -> Number -> WeightOptions -> Number
calculatePinWeight vertex pinPos radius stiffness options =
  let dist = distance vertex pinPos
      weight
        | dist < 0.001 = 1000.0  -- Very close - high weight
        | dist > radius * 3.0 = 0.0  -- Too far - no influence
        | otherwise =
            let normalizedDist = dist / radius
                baseWeight = pow (1.0 / (1.0 + normalizedDist)) options.falloffPower
            in if stiffness > 0.0
               then baseWeight * (1.0 - stiffness * 0.5)
               else baseWeight
  in if weight < options.minWeight then 0.0 else weight

-- | Calculate weights for all vertex-pin pairs.
-- |
-- | Returns flattened array: weights[v * pinCount + p] = weight of pin p on vertex v
calculateWeights :: Array Point2D -> Array PinRestState -> WeightOptions -> Array Number
calculateWeights vertices pinRestStates options
  | length pinRestStates == 0 = []
  | otherwise =
      let pinCount = length pinRestStates
          processVertex vertex =
            let vertexWeights = map (\pin ->
                  calculatePinWeight vertex pin.position pin.radius
                    pin.stiffness options
                  ) pinRestStates
                totalWeight = foldl (+) 0.0 vertexWeights
                normalizedWeights =
                  if options.normalize && totalWeight > 0.0
                  then map (\w -> w / totalWeight) vertexWeights
                  else vertexWeights
            in normalizedWeights
      in foldl (\acc v -> acc <> processVertex v) [] vertices

--------------------------------------------------------------------------------
-- Deformation Application
--------------------------------------------------------------------------------

-- | Apply a single pin's transformation to a vertex.
-- |
-- | Handles translation, rotation, and scale based on pin delta.
applyPinTransform :: Point2D -> PinState -> PinRestState
                  -> Boolean -> Boolean -> Boolean -> Point2D
applyPinTransform vertex pinState restState
                  applyTranslation applyRotation applyScale =
  let
      -- Apply translation
      v1 = if applyTranslation
           then translatePoint vertex pinState.delta
           else vertex

      -- Apply rotation around pin position
      v2 = if applyRotation
           then let rotationDelta = pinState.rotation - restState.rotation
                in if abs rotationDelta > 0.001
                   then rotatePoint v1 pinState.position rotationDelta
                   else v1
           else v1

      -- Apply scale around pin position
      v3 = if applyScale
           then if abs (pinState.scale - restState.scale) > 0.001
                then let scaleDelta = pinState.scale / restState.scale
                     in scalePoint v2 pinState.position scaleDelta
                else v2
           else v2
  in v3

-- | Deform a single vertex using weighted pin influences.
-- |
-- | Computes weighted average of per-pin deformed positions.
deformVertex :: Point2D -> Int -> Array PinState -> Array PinRestState
             -> Array Number -> Point2D
deformVertex vertex vertexIndex pinStates pinRestStates weights
  | length pinStates == 0 = vertex
  | otherwise =
      let pinCount = length pinStates
          -- Accumulate weighted positions using fold with index
          result = foldl
            (\acc p ->
              let weight = fromMaybe 0.0 (weights !! (vertexIndex * pinCount + p))
              in if weight <= 0.0
                 then acc
                 else case Tuple (pinStates !! p) (pinRestStates !! p) of
                   Tuple (Just pinState) (Just restState) ->
                     let deformed = applyPinTransform vertex pinState restState
                                      true true true
                     in { totalX: acc.totalX + p2dX deformed * weight
                        , totalY: acc.totalY + p2dY deformed * weight
                        , totalWeight: acc.totalWeight + weight
                        }
                   _ -> acc
            ) { totalX: 0.0, totalY: 0.0, totalWeight: 0.0 }
            (range 0 (pinCount - 1))
      in if result.totalWeight > 0.0
         then mkPoint2D (result.totalX / result.totalWeight) (result.totalY / result.totalWeight)
         else vertex

-- | Helper: generate range of integers
range :: Int -> Int -> Array Int
range start end
  | start > end = []
  | otherwise = [start] <> range (start + 1) end

-- | Deform all vertices in a mesh.
-- |
-- | Returns array of deformed vertex positions.
deformMesh :: Array Point2D -> Array PinState -> Array PinRestState
           -> Array Number -> Array Point2D
deformMesh vertices pinStates pinRestStates weights =
  mapWithIndex (\i vertex -> deformVertex vertex i pinStates pinRestStates weights) vertices

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Create pin state from current and rest positions
createPinState :: Point2D -> Number -> Number -> Point2D -> PinState
createPinState position rotation scale restPosition =
  { position: position
  , rotation: rotation
  , scale: scale
  , delta: mkPoint2D (p2dX position - p2dX restPosition)
                     (p2dY position - p2dY restPosition)
  }

-- | Linear interpolation between two points
lerpPoint :: Point2D -> Point2D -> Number -> Point2D
lerpPoint a b t =
  let tc = max 0.0 (min 1.0 t)
  in mkPoint2D
       (p2dX a + (p2dX b - p2dX a) * tc)
       (p2dY a + (p2dY b - p2dY a) * tc)

-- | Linear interpolation between two values
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * max 0.0 (min 1.0 t)
