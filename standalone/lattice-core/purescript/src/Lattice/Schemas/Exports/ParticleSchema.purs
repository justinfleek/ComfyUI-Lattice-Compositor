-- | Lattice.Schemas.Exports.ParticleSchema - Particle trajectory export format types
-- |
-- | Particle trajectory export format types.
-- |
-- | Source: ui/src/schemas/exports/particle-schema.ts

module Lattice.Schemas.Exports.ParticleSchema
  ( -- Constants
    maxFrames
  , maxParticles
  , maxVelocity
  , maxParticleRate
  , maxCoordinate
    -- Structures
  , ParticlePosition
  , ParticleVelocity
  , ParticleColor
  , ParticleData
  , Position3D
  , EmitterConfig
  , ParticleTrajectoryMetadata
  , ParticleTrajectoryExport
    -- Validation
  , isValidPosition
  , isValidVelocity
  , isValidColor
  , isValidParticleData
  , isValidEmitterConfig
  , isValidMetadata
  , isValidExport
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Array (length)
import Data.Number (abs)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxFrames :: Int
maxFrames = 100000

maxParticles :: Int
maxParticles = 10000000

maxVelocity :: Number
maxVelocity = 100000.0

maxParticleRate :: Int
maxParticleRate = 1000000

maxCoordinate :: Number
maxCoordinate = 16384.0

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Particle position at a frame
type ParticlePosition =
  { frame :: Int
  , x :: Number
  , y :: Number
  , z :: Maybe Number
  }

-- | Particle velocity at a frame
type ParticleVelocity =
  { frame :: Int
  , vx :: Number
  , vy :: Number
  , vz :: Number
  }

-- | Particle color (normalized 0-1)
type ParticleColor =
  { r :: Number
  , g :: Number
  , b :: Number
  }

-- | Particle data with full lifecycle
type ParticleData =
  { id :: Int
  , birthFrame :: Int
  , deathFrame :: Int
  , positions :: Array ParticlePosition
  , velocities :: Maybe (Array ParticleVelocity)
  , size :: Maybe (Array Number)
  , opacity :: Maybe (Array Number)
  , color :: Maybe (Array ParticleColor)
  }

-- | 3D position
type Position3D =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Emitter configuration
type EmitterConfig =
  { emitterType :: String
  , position :: Position3D
  , rate :: Int
  , lifetime :: Int
  }

-- | Particle trajectory export metadata
type ParticleTrajectoryMetadata =
  { totalParticles :: Int
  , frameCount :: Int
  , maxActiveParticles :: Int
  }

-- | Particle trajectory export
type ParticleTrajectoryExport =
  { particles :: Array ParticleData
  , emitterConfig :: EmitterConfig
  , metadata :: ParticleTrajectoryMetadata
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if particle position is valid
isValidPosition :: ParticlePosition -> Boolean
isValidPosition p = p.frame <= maxFrames

-- | Check if particle velocity is valid
isValidVelocity :: ParticleVelocity -> Boolean
isValidVelocity v =
  v.frame <= maxFrames &&
  abs v.vx <= maxVelocity &&
  abs v.vy <= maxVelocity &&
  abs v.vz <= maxVelocity

-- | Check if particle color is normalized
isValidColor :: ParticleColor -> Boolean
isValidColor c =
  c.r >= 0.0 && c.r <= 1.0 &&
  c.g >= 0.0 && c.g <= 1.0 &&
  c.b >= 0.0 && c.b <= 1.0

-- | Check if particle data is valid
isValidParticleData :: ParticleData -> Boolean
isValidParticleData d =
  d.id <= maxParticles &&
  d.birthFrame <= maxFrames &&
  d.deathFrame <= maxFrames &&
  d.deathFrame >= d.birthFrame &&
  length d.positions == (d.deathFrame - d.birthFrame + 1)

-- | Check if emitter config is valid
isValidEmitterConfig :: EmitterConfig -> Boolean
isValidEmitterConfig c =
  c.rate <= maxParticleRate &&
  c.lifetime <= maxFrames

-- | Check if metadata is valid
isValidMetadata :: ParticleTrajectoryMetadata -> Boolean
isValidMetadata m =
  m.totalParticles <= maxParticles &&
  m.frameCount <= maxFrames &&
  m.maxActiveParticles <= maxParticles

-- | Check if trajectory export is valid
isValidExport :: ParticleTrajectoryExport -> Boolean
isValidExport e =
  isValidMetadata e.metadata &&
  isValidEmitterConfig e.emitterConfig &&
  length e.particles == e.metadata.totalParticles
