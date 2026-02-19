{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Particles.Lifecycle
Description : Particle Spawn, Update, and Death Logic
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure functions for particle lifecycle management:
- Particle creation with initial properties
- Position and velocity updates
- Age progression and death check
- Trail history management
- Property interpolation over lifetime

All functions are total and deterministic.
Randomness is provided as pre-computed values from seeded RNG.

Source: ui/src/services/particleSystem.ts (lines 938-1054, 525-718)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Particles.Lifecycle
  ( -- * Types
    Particle(..)
  , RGBA(..)
  , TrailPoint(..)
    -- * Particle Creation
  , createParticle
  , resetParticle
    -- * Position Update
  , updatePosition
  , storePreviousPosition
    -- * Age and Death
  , incrementAge
  , isExpired
  , lifeRatio
    -- * Trail Management
  , addTrailPoint
  , pruneTrail
  , maxTrailLength
    -- * Property Calculation
  , baseToCurrentSize
  , baseToCurrentColor
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | RGBA color with values in 0-255 range
data RGBA = RGBA
  { rgbaR :: Double
  , rgbaG :: Double
  , rgbaB :: Double
  , rgbaA :: Double
  } deriving (Show, Eq)

-- | A point in trail history
data TrailPoint = TrailPoint
  { tpX :: Double
  , tpY :: Double
  } deriving (Show, Eq)

-- | Particle state
data Particle = Particle
  { pId :: Int               -- ^ Unique particle ID
  , pX :: Double             -- ^ Current X position (normalized 0-1)
  , pY :: Double             -- ^ Current Y position (normalized 0-1)
  , pPrevX :: Double         -- ^ Previous X (for motion blur/trails)
  , pPrevY :: Double         -- ^ Previous Y
  , pVx :: Double            -- ^ X velocity (normalized units/frame)
  , pVy :: Double            -- ^ Y velocity
  , pAge :: Double           -- ^ Current age in frames
  , pLifetime :: Double      -- ^ Total lifetime in frames
  , pSize :: Double          -- ^ Current size in pixels
  , pBaseSize :: Double      -- ^ Initial size (for modulation reference)
  , pColor :: RGBA           -- ^ Current color
  , pBaseColor :: RGBA       -- ^ Initial color (for modulation reference)
  , pEmitterId :: String     -- ^ Source emitter ID
  , pIsSubParticle :: Bool   -- ^ Whether spawned by sub-emitter
  , pRotation :: Double      -- ^ Current rotation in radians
  , pAngularVelocity :: Double -- ^ Rotation speed (rad/frame)
  , pSpriteIndex :: Int      -- ^ Current sprite frame index
  , pCollisionCount :: Int   -- ^ Number of collisions experienced
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Maximum trail history length
maxTrailLength :: Int
maxTrailLength = 20

--------------------------------------------------------------------------------
-- Particle Creation
--------------------------------------------------------------------------------

-- | Create a new particle with initial properties.
--
-- All randomness should be pre-computed by the caller using seeded RNG.
--
-- @param pid Unique particle ID
-- @param x Initial X position
-- @param y Initial Y position
-- @param vx Initial X velocity
-- @param vy Initial Y velocity
-- @param size Initial size
-- @param lifetime Total lifetime in frames
-- @param color Initial color (RGB, 0-255)
-- @param emitterId Source emitter ID
-- @param rotation Initial rotation (radians)
-- @param angularVel Angular velocity (rad/frame)
-- @param spriteIdx Initial sprite frame
-- @return New particle
createParticle
  :: Int -> Double -> Double -> Double -> Double
  -> Double -> Double -> (Double, Double, Double)
  -> String -> Double -> Double -> Int
  -> Particle
createParticle pid x y vx vy size lifetime (r, g, b) emitterId rotation angularVel spriteIdx =
  let baseColor = RGBA r g b 255
  in Particle
       { pId = pid
       , pX = x
       , pY = y
       , pPrevX = x
       , pPrevY = y
       , pVx = vx
       , pVy = vy
       , pAge = 0
       , pLifetime = max 1 lifetime
       , pSize = max 1 size
       , pBaseSize = max 1 size
       , pColor = baseColor
       , pBaseColor = baseColor
       , pEmitterId = emitterId
       , pIsSubParticle = False
       , pRotation = rotation
       , pAngularVelocity = angularVel
       , pSpriteIndex = spriteIdx
       , pCollisionCount = 0
       }

-- | Reset a particle for pool reuse.
--
-- Reuses the existing Particle record with new values.
resetParticle
  :: Particle -> Int -> Double -> Double -> Double -> Double
  -> Double -> Double -> (Double, Double, Double)
  -> String -> Double -> Double -> Int
  -> Particle
resetParticle p pid x y vx vy size lifetime (r, g, b) emitterId rotation angularVel spriteIdx =
  let baseColor = RGBA r g b 255
  in p { pId = pid
       , pX = x
       , pY = y
       , pPrevX = x
       , pPrevY = y
       , pVx = vx
       , pVy = vy
       , pAge = 0
       , pLifetime = max 1 lifetime
       , pSize = max 1 size
       , pBaseSize = max 1 size
       , pColor = baseColor
       , pBaseColor = baseColor
       , pEmitterId = emitterId
       , pIsSubParticle = False
       , pRotation = rotation
       , pAngularVelocity = angularVel
       , pSpriteIndex = spriteIdx
       , pCollisionCount = 0
       }

--------------------------------------------------------------------------------
-- Position Update
--------------------------------------------------------------------------------

-- | Store current position as previous (for trails/motion blur).
storePreviousPosition :: Particle -> Particle
storePreviousPosition p = p { pPrevX = pX p, pPrevY = pY p }

-- | Update particle position based on velocity.
--
-- @param p Particle to update
-- @param deltaTime Frame delta time
-- @return Updated particle
updatePosition :: Particle -> Double -> Particle
updatePosition p deltaTime = p
  { pX = pX p + pVx p * deltaTime
  , pY = pY p + pVy p * deltaTime
  , pRotation = pRotation p + pAngularVelocity p * deltaTime
  }

--------------------------------------------------------------------------------
-- Age and Death
--------------------------------------------------------------------------------

-- | Increment particle age.
incrementAge :: Particle -> Double -> Particle
incrementAge p deltaTime = p { pAge = pAge p + deltaTime }

-- | Check if particle has exceeded its lifetime.
isExpired :: Particle -> Bool
isExpired p = pAge p > pLifetime p

-- | Calculate life ratio (0 at birth, 1 at death).
--
-- Returns clamped value in [0, 1].
lifeRatio :: Particle -> Double
lifeRatio p =
  let ratio = pAge p / max 1 (pLifetime p)
  in max 0 (min 1 ratio)

--------------------------------------------------------------------------------
-- Trail Management
--------------------------------------------------------------------------------

-- | Add current position to trail history.
addTrailPoint :: Particle -> [TrailPoint] -> [TrailPoint]
addTrailPoint p trail = TrailPoint (pX p) (pY p) : trail

-- | Prune trail to maximum length.
pruneTrail :: [TrailPoint] -> [TrailPoint]
pruneTrail trail
  | length trail > maxTrailLength = take maxTrailLength trail
  | otherwise = trail

--------------------------------------------------------------------------------
-- Property Calculation
--------------------------------------------------------------------------------

-- | Calculate current size from base size and modulation factor.
--
-- @param baseSize Original particle size
-- @param sizeModulation Modulation multiplier (1.0 = no change)
-- @return Current size (always >= 1)
baseToCurrentSize :: Double -> Double -> Double
baseToCurrentSize baseSize sizeModulation =
  max 1 (baseSize * max 0 sizeModulation)

-- | Calculate current color from base color and modulation.
--
-- @param baseColor Original color
-- @param colorMod Color modulation (r, g, b, a multipliers)
-- @return Current color (clamped to 0-255)
baseToCurrentColor :: RGBA -> (Double, Double, Double, Double) -> RGBA
baseToCurrentColor base (rMod, gMod, bMod, aMod) =
  let clamp v = max 0 (min 255 v)
  in RGBA
       (clamp $ rgbaR base * rMod)
       (clamp $ rgbaG base * gMod)
       (clamp $ rgbaB base * bMod)
       (clamp $ rgbaA base * aMod)
