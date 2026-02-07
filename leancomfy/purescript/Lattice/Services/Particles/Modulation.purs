-- | Lattice.Services.Particles.Modulation - Property Modulation Curves
-- |
-- | Pure mathematical functions for particle property modulation:
-- | - Size curves over lifetime
-- | - Opacity/alpha curves
-- | - Color interpolation
-- | - Velocity modulation
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/particleSystem.ts (applyModulations)

module Lattice.Services.Particles.Modulation
  ( ModulationType(..)
  , CurvePoint(..)
  , ModulationResult(..)
  , defaultModulationResult
  , evaluateLinear
  , modulateSize
  , modulateOpacity
  , modulateColor
  , modulateVelocity
  , applyModulations
  , linearFadeOut
  , linearFadeIn
  , pulseWave
  ) where

import Prelude

import Data.Array (length, (!!), foldl)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Math (max, min)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Type of property being modulated
data ModulationType
  = ModSize
  | ModOpacity
  | ModColorR
  | ModColorG
  | ModColorB
  | ModVelocity

derive instance eqModulationType :: Eq ModulationType

instance showModulationType :: Show ModulationType where
  show ModSize = "ModSize"
  show ModOpacity = "ModOpacity"
  show ModColorR = "ModColorR"
  show ModColorG = "ModColorG"
  show ModColorB = "ModColorB"
  show ModVelocity = "ModVelocity"

-- | A point on a modulation curve
type CurvePoint =
  { t :: Number      -- Time (life ratio 0-1)
  , value :: Number  -- Value at this time
  }

-- | Modulation result
type ModulationResult =
  { sizeMult :: Number
  , opacityMult :: Number
  , colorMult :: Tuple Number (Tuple Number Number)  -- RGB multipliers
  , velocityMult :: Number
  }

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default modulation result (no change)
defaultModulationResult :: ModulationResult
defaultModulationResult =
  { sizeMult: 1.0
  , opacityMult: 1.0
  , colorMult: Tuple 1.0 (Tuple 1.0 1.0)
  , velocityMult: 1.0
  }

--------------------------------------------------------------------------------
-- Curve Evaluation
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 x = max 0.0 (min 1.0 x)

-- | Linear interpolation
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Find segment containing t (returns index of point before t)
findSegmentIndex :: Array CurvePoint -> Number -> Int
findSegmentIndex points t = go 0
  where
    n = length points
    go i
      | i + 1 >= n = i
      | otherwise =
          case points !! (i + 1) of
            Just p | p.t > t -> i
            _ -> go (i + 1)

-- | Evaluate linear curve at parameter t.
evaluateLinear :: Array CurvePoint -> Number -> Number
evaluateLinear points t =
  case length points of
    0 -> 1.0  -- Default: no change
    1 -> fromMaybe 1.0 (map _.value (points !! 0))
    _ ->
      let
        clampedT = clamp01 t
        segIdx = findSegmentIndex points clampedT
      in
        case Tuple (points !! segIdx) (points !! (segIdx + 1)) of
          Tuple (Just p0) (Just p1) ->
            let
              range = p1.t - p0.t
              localT = if range > 0.0001
                       then (clampedT - p0.t) / range
                       else 0.0
            in
              lerp p0.value p1.value (clamp01 localT)
          Tuple (Just p0) Nothing -> p0.value
          _ -> 1.0

--------------------------------------------------------------------------------
-- Property Modulation
--------------------------------------------------------------------------------

-- | Modulate size (result >= 0)
modulateSize :: Array CurvePoint -> Number -> Number
modulateSize curve lifeRatio = max 0.0 (evaluateLinear curve lifeRatio)

-- | Modulate opacity (result in [0, 1])
modulateOpacity :: Array CurvePoint -> Number -> Number
modulateOpacity curve lifeRatio = clamp01 (evaluateLinear curve lifeRatio)

-- | Modulate color channel (result in [0, 1])
modulateColor :: Array CurvePoint -> Number -> Number
modulateColor curve lifeRatio = clamp01 (evaluateLinear curve lifeRatio)

-- | Modulate velocity (result >= 0)
modulateVelocity :: Array CurvePoint -> Number -> Number
modulateVelocity curve lifeRatio = max 0.0 (evaluateLinear curve lifeRatio)

--------------------------------------------------------------------------------
-- Combined Application
--------------------------------------------------------------------------------

-- | Apply all modulations to get combined result.
applyModulations
  :: Array { emitterId :: String, target :: ModulationType, curve :: Array CurvePoint, enabled :: Boolean }
  -> String
  -> Number
  -> ModulationResult
applyModulations mods emitterId lifeRatio =
  foldl (combineModulation lifeRatio) defaultModulationResult relevantMods
  where
    relevantMods = filterRelevant mods emitterId

    filterRelevant :: Array _ -> String -> Array _
    filterRelevant ms eid = filter (\m -> m.enabled && (m.emitterId == "*" || m.emitterId == eid)) ms

    combineModulation :: Number -> ModulationResult -> _ -> ModulationResult
    combineModulation lr result mod =
      case mod.target of
        ModSize ->
          result { sizeMult = result.sizeMult * modulateSize mod.curve lr }
        ModOpacity ->
          result { opacityMult = result.opacityMult * modulateOpacity mod.curve lr }
        ModColorR ->
          let Tuple r (Tuple g b) = result.colorMult
              newR = r * modulateColor mod.curve lr
          in result { colorMult = Tuple newR (Tuple g b) }
        ModColorG ->
          let Tuple r (Tuple g b) = result.colorMult
              newG = g * modulateColor mod.curve lr
          in result { colorMult = Tuple r (Tuple newG b) }
        ModColorB ->
          let Tuple r (Tuple g b) = result.colorMult
              newB = b * modulateColor mod.curve lr
          in result { colorMult = Tuple r (Tuple g newB) }
        ModVelocity ->
          result { velocityMult = result.velocityMult * modulateVelocity mod.curve lr }

--------------------------------------------------------------------------------
-- Preset Curves
--------------------------------------------------------------------------------

-- | Linear fade out: 1 at birth, 0 at death
linearFadeOut :: Array CurvePoint
linearFadeOut = [{ t: 0.0, value: 1.0 }, { t: 1.0, value: 0.0 }]

-- | Linear fade in: 0 at birth, 1 at death
linearFadeIn :: Array CurvePoint
linearFadeIn = [{ t: 0.0, value: 0.0 }, { t: 1.0, value: 1.0 }]

-- | Pulse: up then down
pulseWave :: Array CurvePoint
pulseWave =
  [ { t: 0.0, value: 0.0 }
  , { t: 0.25, value: 1.0 }
  , { t: 0.75, value: 1.0 }
  , { t: 1.0, value: 0.0 }
  ]

-- | Filter function
filter :: forall a. (a -> Boolean) -> Array a -> Array a
filter _ [] = []
filter pred (x : xs) = if pred x then x : filter pred xs else filter pred xs
