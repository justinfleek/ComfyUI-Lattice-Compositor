{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.ParticleSchema
Description : Particle trajectory export format types
Copyright   : (c) Lattice, 2026
License     : MIT

Particle trajectory export format types.

Source: ui/src/schemas/exports/particle-schema.ts
-}

module Lattice.Schemas.Exports.ParticleSchema
  ( -- * Constants
    maxFrames
  , maxParticles
  , maxVelocity
  , maxParticleRate
  , maxCoordinate
    -- * Structures
  , ParticlePosition(..)
  , ParticleVelocity(..)
  , ParticleColor(..)
  , ParticleData(..)
  , Position3D(..)
  , EmitterConfig(..)
  , ParticleTrajectoryMetadata(..)
  , ParticleTrajectoryExport(..)
    -- * Validation
  , isValidPosition
  , isValidVelocity
  , isValidColor
  , isValidParticleData
  , isValidEmitterConfig
  , isValidMetadata
  , isValidExport
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxFrames :: Int
maxFrames = 100000

maxParticles :: Int
maxParticles = 10000000

maxVelocity :: Double
maxVelocity = 100000.0

maxParticleRate :: Int
maxParticleRate = 1000000

maxCoordinate :: Double
maxCoordinate = 16384.0

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Particle position at a frame
data ParticlePosition = ParticlePosition
  { ppFrame :: !Int
  , ppX :: !Double
  , ppY :: !Double
  , ppZ :: !(Maybe Double)
  }
  deriving stock (Eq, Show, Generic)

-- | Particle velocity at a frame
data ParticleVelocity = ParticleVelocity
  { pvFrame :: !Int
  , pvVx :: !Double
  , pvVy :: !Double
  , pvVz :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Particle color (normalized 0-1)
data ParticleColor = ParticleColor
  { pcR :: !Double
  , pcG :: !Double
  , pcB :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Particle data with full lifecycle
data ParticleData = ParticleData
  { pdId :: !Int
  , pdBirthFrame :: !Int
  , pdDeathFrame :: !Int
  , pdPositions :: !(Vector ParticlePosition)
  , pdVelocities :: !(Maybe (Vector ParticleVelocity))
  , pdSize :: !(Maybe (Vector Double))
  , pdOpacity :: !(Maybe (Vector Double))
  , pdColor :: !(Maybe (Vector ParticleColor))
  }
  deriving stock (Eq, Show, Generic)

-- | 3D position
data Position3D = Position3D
  { p3dX :: !Double
  , p3dY :: !Double
  , p3dZ :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Emitter configuration
data EmitterConfig = EmitterConfig
  { ecEmitterType :: !Text
  , ecPosition :: !Position3D
  , ecRate :: !Int
  , ecLifetime :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Particle trajectory export metadata
data ParticleTrajectoryMetadata = ParticleTrajectoryMetadata
  { ptmTotalParticles :: !Int
  , ptmFrameCount :: !Int
  , ptmMaxActiveParticles :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Particle trajectory export
data ParticleTrajectoryExport = ParticleTrajectoryExport
  { pteParticles :: !(Vector ParticleData)
  , pteEmitterConfig :: !EmitterConfig
  , pteMetadata :: !ParticleTrajectoryMetadata
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if particle position is valid
isValidPosition :: ParticlePosition -> Bool
isValidPosition p = ppFrame p <= maxFrames

-- | Check if particle velocity is valid
isValidVelocity :: ParticleVelocity -> Bool
isValidVelocity v =
  pvFrame v <= maxFrames &&
  abs (pvVx v) <= maxVelocity &&
  abs (pvVy v) <= maxVelocity &&
  abs (pvVz v) <= maxVelocity

-- | Check if particle color is normalized
isValidColor :: ParticleColor -> Bool
isValidColor c =
  pcR c >= 0 && pcR c <= 1 &&
  pcG c >= 0 && pcG c <= 1 &&
  pcB c >= 0 && pcB c <= 1

-- | Check if particle data is valid
isValidParticleData :: ParticleData -> Bool
isValidParticleData d =
  pdId d <= maxParticles &&
  pdBirthFrame d <= maxFrames &&
  pdDeathFrame d <= maxFrames &&
  pdDeathFrame d >= pdBirthFrame d &&
  V.length (pdPositions d) == (pdDeathFrame d - pdBirthFrame d + 1)

-- | Check if emitter config is valid
isValidEmitterConfig :: EmitterConfig -> Bool
isValidEmitterConfig c =
  ecRate c <= maxParticleRate &&
  ecLifetime c <= maxFrames

-- | Check if metadata is valid
isValidMetadata :: ParticleTrajectoryMetadata -> Bool
isValidMetadata m =
  ptmTotalParticles m <= maxParticles &&
  ptmFrameCount m <= maxFrames &&
  ptmMaxActiveParticles m <= maxParticles

-- | Check if trajectory export is valid
isValidExport :: ParticleTrajectoryExport -> Bool
isValidExport e =
  isValidMetadata (pteMetadata e) &&
  isValidEmitterConfig (pteEmitterConfig e) &&
  V.length (pteParticles e) == ptmTotalParticles (pteMetadata e)
