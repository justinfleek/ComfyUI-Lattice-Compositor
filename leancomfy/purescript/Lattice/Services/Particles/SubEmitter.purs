-- | Lattice.Services.Particles.SubEmitter - Sub-Emitter Death Triggers
-- |
-- | Pure functions for sub-emitter particle spawning:
-- | - Death trigger configuration
-- | - Sub-particle property inheritance
-- | - Burst emission on parent death
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/particleSystem.ts (triggerSubEmitters)

module Lattice.Services.Particles.SubEmitter
  ( SubEmitterTrigger(..)
  , InheritMode(..)
  , SubEmitterConfig(..)
  , SubSpawnResult(..)
  , shouldTrigger
  , calculateSubSpawns
  , inheritVelocity
  , inheritSize
  , inheritColor
  , subEmitterBurst
  ) where

import Prelude

import Data.Int (round, toNumber)
import Data.Tuple (Tuple(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | What triggers sub-emission
data SubEmitterTrigger
  = TriggerDeath
  | TriggerCollision
  | TriggerLifetime

derive instance eqSubEmitterTrigger :: Eq SubEmitterTrigger

instance showSubEmitterTrigger :: Show SubEmitterTrigger where
  show TriggerDeath = "TriggerDeath"
  show TriggerCollision = "TriggerCollision"
  show TriggerLifetime = "TriggerLifetime"

-- | How properties are inherited from parent
data InheritMode
  = InheritNone
  | InheritFull
  | InheritPartial Number
  | InheritInverse

derive instance eqInheritMode :: Eq InheritMode

instance showInheritMode :: Show InheritMode where
  show InheritNone = "InheritNone"
  show InheritFull = "InheritFull"
  show (InheritPartial n) = "InheritPartial " <> show n
  show InheritInverse = "InheritInverse"

-- | Sub-emitter configuration
type SubEmitterConfig =
  { id :: String
  , parentEmitterId :: String
  , trigger :: SubEmitterTrigger
  , burstCount :: Int
  , burstCountVariance :: Number
  , inheritVelocity :: InheritMode
  , inheritSize :: InheritMode
  , inheritColor :: InheritMode
  , velocitySpread :: Number
  , sizeMultiplier :: Number
  , lifetimeMultiplier :: Number
  , enabled :: Boolean
  }

-- | Result of sub-spawn calculation
type SubSpawnResult =
  { count :: Int
  , baseX :: Number
  , baseY :: Number
  , baseVx :: Number
  , baseVy :: Number
  , baseSize :: Number
  , baseColor :: Tuple Number (Tuple Number Number)  -- RGB
  , lifetime :: Number
  }

--------------------------------------------------------------------------------
-- Trigger Check
--------------------------------------------------------------------------------

-- | Check if sub-emitter should trigger.
shouldTrigger
  :: SubEmitterConfig
  -> String
  -> SubEmitterTrigger
  -> Number
  -> Number
  -> Boolean
shouldTrigger config parentEmitterId trigger lifeRatio threshold =
  config.enabled
  && (config.parentEmitterId == "*" || config.parentEmitterId == parentEmitterId)
  && matchesTrigger config.trigger trigger lifeRatio threshold
  where
    matchesTrigger :: SubEmitterTrigger -> SubEmitterTrigger -> Number -> Number -> Boolean
    matchesTrigger TriggerDeath TriggerDeath _ _ = true
    matchesTrigger TriggerCollision TriggerCollision _ _ = true
    matchesTrigger TriggerLifetime TriggerLifetime lr thr = lr >= thr
    matchesTrigger _ _ _ _ = false

--------------------------------------------------------------------------------
-- Sub-Emission Calculation
--------------------------------------------------------------------------------

-- | Calculate sub-spawn parameters from parent particle.
calculateSubSpawns
  :: SubEmitterConfig
  -> Number -> Number      -- parent position
  -> Number -> Number      -- parent velocity
  -> Number                -- parent size
  -> Tuple Number (Tuple Number Number)  -- parent color (RGB)
  -> Number                -- parent lifetime
  -> Number                -- random for variance
  -> SubSpawnResult
calculateSubSpawns config px py pvx pvy psize pcolor plife randomVar =
  let
    count = subEmitterBurst config.burstCount config.burstCountVariance randomVar
    Tuple vx vy = inheritVelocity' pvx pvy config.inheritVelocity
    size = inheritSize' psize config.inheritSize config.sizeMultiplier
    color = inheritColor' pcolor config.inheritColor
    lifetime = plife * config.lifetimeMultiplier
  in
    { count
    , baseX: px
    , baseY: py
    , baseVx: vx
    , baseVy: vy
    , baseSize: max 1.0 size
    , baseColor: color
    , lifetime: max 1.0 lifetime
    }

-- | Calculate burst count with variance.
subEmitterBurst :: Int -> Number -> Number -> Int
subEmitterBurst base variance randomVal =
  let
    varianceAmount = toNumber base * variance * (randomVal - 0.5) * 2.0
  in
    max 0 (round (toNumber base + varianceAmount))

--------------------------------------------------------------------------------
-- Property Inheritance
--------------------------------------------------------------------------------

-- | Inherit velocity from parent.
inheritVelocity :: Number -> Number -> InheritMode -> Tuple Number Number
inheritVelocity = inheritVelocity'

inheritVelocity' :: Number -> Number -> InheritMode -> Tuple Number Number
inheritVelocity' vx vy mode =
  case mode of
    InheritNone -> Tuple 0.0 0.0
    InheritFull -> Tuple vx vy
    InheritPartial mult -> Tuple (vx * mult) (vy * mult)
    InheritInverse -> Tuple (-vx) (-vy)

-- | Inherit size from parent.
inheritSize :: Number -> InheritMode -> Number -> Number
inheritSize = inheritSize'

inheritSize' :: Number -> InheritMode -> Number -> Number
inheritSize' size mode multiplier =
  let
    baseSize = case mode of
      InheritNone -> 10.0
      InheritFull -> size
      InheritPartial mult -> size * mult
      InheritInverse -> 10.0
  in
    baseSize * multiplier

-- | Inherit color from parent.
inheritColor :: Tuple Number (Tuple Number Number) -> InheritMode -> Tuple Number (Tuple Number Number)
inheritColor = inheritColor'

inheritColor' :: Tuple Number (Tuple Number Number) -> InheritMode -> Tuple Number (Tuple Number Number)
inheritColor' (Tuple r (Tuple g b)) mode =
  case mode of
    InheritNone -> Tuple 255.0 (Tuple 255.0 255.0)
    InheritFull -> Tuple r (Tuple g b)
    InheritPartial mult -> Tuple (r * mult) (Tuple (g * mult) (b * mult))
    InheritInverse -> Tuple (255.0 - r) (Tuple (255.0 - g) (255.0 - b))
