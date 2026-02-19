{-|
Module      : Lattice.Services.Particles.SubEmitter
Description : Sub-Emitter Death Trigger System
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure functions for sub-emitter particle spawning:
- Death trigger configuration
- Sub-particle property inheritance
- Burst emission on parent death
- Collision-triggered sub-emission

All functions are total and deterministic.
Randomness is provided as pre-computed values.

Source: ui/src/services/particleSystem.ts (triggerSubEmitters, SubEmitterConfig)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Particles.SubEmitter
  ( -- * Types
    SubEmitterConfig(..)
  , SubEmitterTrigger(..)
  , InheritMode(..)
  , SubSpawnResult(..)
    -- * Sub-Emission
  , shouldTrigger
  , calculateSubSpawns
  , inheritProperty
    -- * Property Inheritance
  , inheritVelocity
  , inheritSize
  , inheritColor
  , inheritPosition
    -- * Burst Calculation
  , subEmitterBurst
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | What triggers sub-emission
data SubEmitterTrigger
  = TriggerDeath       -- ^ When parent particle dies
  | TriggerCollision   -- ^ When parent particle collides
  | TriggerLifetime    -- ^ At specific lifetime ratio
  deriving (Show, Eq)

-- | How properties are inherited from parent
data InheritMode
  = InheritNone        -- ^ Don't inherit (use sub-emitter default)
  | InheritFull        -- ^ Inherit 100%
  | InheritPartial Double  -- ^ Inherit with multiplier (0-1)
  | InheritInverse     -- ^ Inherit inverted (e.g., opposite direction)
  deriving (Show, Eq)

-- | Sub-emitter configuration
data SubEmitterConfig = SubEmitterConfig
  { secId :: String
  , secParentEmitterId :: String  -- ^ Which emitter's particles trigger this
  , secTrigger :: SubEmitterTrigger
  , secBurstCount :: Int          -- ^ Particles per trigger
  , secBurstCountVariance :: Double
  , secInheritVelocity :: InheritMode
  , secInheritSize :: InheritMode
  , secInheritColor :: InheritMode
  , secVelocitySpread :: Double   -- ^ Additional velocity spread (degrees)
  , secSizeMultiplier :: Double   -- ^ Size relative to parent
  , secLifetimeMultiplier :: Double
  , secEnabled :: Bool
  } deriving (Show, Eq)

-- | Result of sub-spawn calculation
data SubSpawnResult = SubSpawnResult
  { ssrCount :: Int            -- ^ Number of sub-particles to spawn
  , ssrBaseX :: Double         -- ^ Spawn X position
  , ssrBaseY :: Double         -- ^ Spawn Y position
  , ssrBaseVx :: Double        -- ^ Base velocity X
  , ssrBaseVy :: Double        -- ^ Base velocity Y
  , ssrBaseSize :: Double      -- ^ Base size
  , ssrBaseColor :: (Double, Double, Double)  -- ^ Base color (RGB)
  , ssrLifetime :: Double      -- ^ Sub-particle lifetime
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Trigger Check
--------------------------------------------------------------------------------

-- | Check if sub-emitter should trigger.
--
-- @param config Sub-emitter configuration
-- @param parentEmitterId Parent particle's emitter ID
-- @param trigger Current trigger event
-- @param lifetimeRatio Current lifetime ratio (for TriggerLifetime)
-- @param triggerThreshold Lifetime threshold (for TriggerLifetime)
-- @return Whether to trigger
shouldTrigger
  :: SubEmitterConfig
  -> String
  -> SubEmitterTrigger
  -> Double
  -> Double
  -> Bool
shouldTrigger config parentEmitterId trigger lifeRatio threshold =
  secEnabled config
  && (secParentEmitterId config == "*" || secParentEmitterId config == parentEmitterId)
  && case (secTrigger config, trigger) of
       (TriggerDeath, TriggerDeath) -> True
       (TriggerCollision, TriggerCollision) -> True
       (TriggerLifetime, TriggerLifetime) -> lifeRatio >= threshold
       _ -> False

--------------------------------------------------------------------------------
-- Sub-Emission Calculation
--------------------------------------------------------------------------------

-- | Calculate sub-spawn parameters from parent particle.
--
-- @param config Sub-emitter configuration
-- @param parentX Parent X position
-- @param parentY Parent Y position
-- @param parentVx Parent X velocity
-- @param parentVy Parent Y velocity
-- @param parentSize Parent size
-- @param parentColor Parent color (RGB)
-- @param parentLifetime Parent lifetime
-- @param randomVariance Random value for count variance (0-1)
-- @return Sub-spawn parameters
calculateSubSpawns
  :: SubEmitterConfig
  -> Double -> Double      -- ^ Parent position
  -> Double -> Double      -- ^ Parent velocity
  -> Double                -- ^ Parent size
  -> (Double, Double, Double)  -- ^ Parent color
  -> Double                -- ^ Parent lifetime
  -> Double                -- ^ Random for variance
  -> SubSpawnResult
calculateSubSpawns config px py pvx pvy psize pcolor plife randomVar =
  let count = subEmitterBurst (secBurstCount config) (secBurstCountVariance config) randomVar
      -- Inherit properties
      (vx, vy) = inheritVelocity pvx pvy (secInheritVelocity config)
      size = inheritSize psize (secInheritSize config) (secSizeMultiplier config)
      color = inheritColor pcolor (secInheritColor config)
      lifetime = plife * secLifetimeMultiplier config
  in SubSpawnResult
       { ssrCount = count
       , ssrBaseX = px
       , ssrBaseY = py
       , ssrBaseVx = vx
       , ssrBaseVy = vy
       , ssrBaseSize = max 1 size
       , ssrBaseColor = color
       , ssrLifetime = max 1 lifetime
       }

-- | Calculate burst count with variance.
subEmitterBurst :: Int -> Double -> Double -> Int
subEmitterBurst base variance randomVal =
  let varianceAmount = fromIntegral base * variance * (randomVal - 0.5) * 2
  in max 0 (round (fromIntegral base + varianceAmount))

--------------------------------------------------------------------------------
-- Property Inheritance
--------------------------------------------------------------------------------

-- | Inherit velocity from parent based on mode.
inheritVelocity :: Double -> Double -> InheritMode -> (Double, Double)
inheritVelocity vx vy mode =
  case mode of
    InheritNone -> (0, 0)
    InheritFull -> (vx, vy)
    InheritPartial mult -> (vx * mult, vy * mult)
    InheritInverse -> (-vx, -vy)

-- | Inherit size from parent based on mode.
inheritSize :: Double -> InheritMode -> Double -> Double
inheritSize size mode multiplier =
  let baseSize = case mode of
        InheritNone -> 10  -- Default sub-particle size
        InheritFull -> size
        InheritPartial mult -> size * mult
        InheritInverse -> 10  -- Doesn't make sense for size
  in baseSize * multiplier

-- | Inherit color from parent based on mode.
inheritColor :: (Double, Double, Double) -> InheritMode -> (Double, Double, Double)
inheritColor (r, g, b) mode =
  case mode of
    InheritNone -> (255, 255, 255)  -- Default white
    InheritFull -> (r, g, b)
    InheritPartial mult -> (r * mult, g * mult, b * mult)
    InheritInverse -> (255 - r, 255 - g, 255 - b)  -- Complement

-- | Apply a general inheritance to any numeric property.
inheritProperty :: Double -> InheritMode -> Double -> Double
inheritProperty value mode defaultVal =
  case mode of
    InheritNone -> defaultVal
    InheritFull -> value
    InheritPartial mult -> value * mult
    InheritInverse -> -value

-- | Inherit position (always inherits parent position).
inheritPosition :: Double -> Double -> (Double, Double)
inheritPosition x y = (x, y)
