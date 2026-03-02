-- | Lattice.Services.Particles.Lifecycle - Particle Lifecycle Management
-- |
-- | Pure functions for particle lifecycle:
-- | - Particle creation with initial properties
-- | - Position and velocity updates
-- | - Age progression and death check
-- | - Trail history management
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/particleSystem.ts (lines 938-1054, 525-718)

module Lattice.Services.Particles.Lifecycle
  ( Particle(..)
  , RGBA(..)
  , TrailPoint(..)
  , maxTrailLength
  , createParticle
  , storePreviousPosition
  , updatePosition
  , incrementAge
  , isExpired
  , lifeRatio
  , addTrailPoint
  , pruneTrail
  , baseToCurrentSize
  , baseToCurrentColor
  ) where

import Prelude

import Data.Array (cons, take)
import Data.Tuple (Tuple(..))
import Math (max, min)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | RGBA color with values in 0-255 range
type RGBA =
  { r :: Number
  , g :: Number
  , b :: Number
  , a :: Number
  }

-- | A point in trail history
type TrailPoint =
  { x :: Number
  , y :: Number
  }

-- | Particle state
type Particle =
  { id :: Int                 -- Unique particle ID
  , x :: Number               -- Current X position (normalized 0-1)
  , y :: Number               -- Current Y position
  , prevX :: Number           -- Previous X (for trails)
  , prevY :: Number           -- Previous Y
  , vx :: Number              -- X velocity
  , vy :: Number              -- Y velocity
  , age :: Number             -- Current age in frames
  , lifetime :: Number        -- Total lifetime in frames
  , size :: Number            -- Current size
  , baseSize :: Number        -- Initial size
  , color :: RGBA             -- Current color
  , baseColor :: RGBA         -- Initial color
  , emitterId :: String       -- Source emitter ID
  , isSubParticle :: Boolean  -- Spawned by sub-emitter
  , rotation :: Number        -- Current rotation (radians)
  , angularVelocity :: Number -- Rotation speed
  , spriteIndex :: Int        -- Current sprite frame
  , collisionCount :: Int     -- Collision counter
  }

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
createParticle
  :: Int           -- id
  -> Number        -- x
  -> Number        -- y
  -> Number        -- vx
  -> Number        -- vy
  -> Number        -- size
  -> Number        -- lifetime
  -> Tuple Number (Tuple Number Number)  -- color (r, (g, b))
  -> String        -- emitterId
  -> Number        -- rotation
  -> Number        -- angularVelocity
  -> Int           -- spriteIndex
  -> Particle
createParticle pid x y vx vy size lifetime (Tuple r (Tuple g b)) emitterId rotation angularVel spriteIdx =
  let
    baseColor = { r, g, b, a: 255.0 }
    safeSize = max 1.0 size
    safeLifetime = max 1.0 lifetime
  in
    { id: pid
    , x
    , y
    , prevX: x
    , prevY: y
    , vx
    , vy
    , age: 0.0
    , lifetime: safeLifetime
    , size: safeSize
    , baseSize: safeSize
    , color: baseColor
    , baseColor
    , emitterId
    , isSubParticle: false
    , rotation
    , angularVelocity: angularVel
    , spriteIndex: spriteIdx
    , collisionCount: 0
    }

--------------------------------------------------------------------------------
-- Position Update
--------------------------------------------------------------------------------

-- | Store current position as previous (for trails).
storePreviousPosition :: Particle -> Particle
storePreviousPosition p = p { prevX = p.x, prevY = p.y }

-- | Update particle position based on velocity.
updatePosition :: Particle -> Number -> Particle
updatePosition p deltaTime = p
  { x = p.x + p.vx * deltaTime
  , y = p.y + p.vy * deltaTime
  , rotation = p.rotation + p.angularVelocity * deltaTime
  }

--------------------------------------------------------------------------------
-- Age and Death
--------------------------------------------------------------------------------

-- | Increment particle age.
incrementAge :: Particle -> Number -> Particle
incrementAge p deltaTime = p { age = p.age + deltaTime }

-- | Check if particle has exceeded its lifetime.
isExpired :: Particle -> Boolean
isExpired p = p.age > p.lifetime

-- | Calculate life ratio (0 at birth, 1 at death).
lifeRatio :: Particle -> Number
lifeRatio p =
  let
    ratio = p.age / max 1.0 p.lifetime
  in
    max 0.0 (min 1.0 ratio)

--------------------------------------------------------------------------------
-- Trail Management
--------------------------------------------------------------------------------

-- | Add current position to trail history.
addTrailPoint :: Particle -> Array TrailPoint -> Array TrailPoint
addTrailPoint p trail = cons { x: p.x, y: p.y } trail

-- | Prune trail to maximum length.
pruneTrail :: Array TrailPoint -> Array TrailPoint
pruneTrail trail = take maxTrailLength trail

--------------------------------------------------------------------------------
-- Property Calculation
--------------------------------------------------------------------------------

-- | Calculate current size from base size and modulation factor.
baseToCurrentSize :: Number -> Number -> Number
baseToCurrentSize baseSize sizeModulation =
  max 1.0 (baseSize * max 0.0 sizeModulation)

-- | Calculate current color from base color and modulation.
baseToCurrentColor :: RGBA -> Tuple Number (Tuple Number (Tuple Number Number)) -> RGBA
baseToCurrentColor base (Tuple rMod (Tuple gMod (Tuple bMod aMod))) =
  let
    clamp v = max 0.0 (min 255.0 v)
  in
    { r: clamp (base.r * rMod)
    , g: clamp (base.g * gMod)
    , b: clamp (base.b * bMod)
    , a: clamp (base.a * aMod)
    }
