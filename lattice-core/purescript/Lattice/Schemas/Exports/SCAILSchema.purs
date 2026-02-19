-- | Lattice.Schemas.Exports.SCAILSchema - SCAIL export format types
-- |
-- | SCAIL (Pose-Driven Video) export format types.
-- | SCAIL uses reference image (identity/appearance) + pose video/sequence for motion guidance.
-- |
-- | Source: ui/src/schemas/exports/scail-schema.ts

module Lattice.Schemas.Exports.SCAILSchema
  ( -- Constants
    maxDimension
  , maxFrames
  , maxFPS
    -- Structures
  , SCAILExportConfig
  , SCAILExportResult
    -- Validation
  , isValidConfig
  , isValidResult
  ) where

import Prelude
import Data.Maybe (Maybe)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxDimension :: Int
maxDimension = 16384

maxFrames :: Int
maxFrames = 100000

maxFPS :: Number
maxFPS = 120.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | SCAIL export configuration
type SCAILExportConfig =
  { referenceImage :: String       -- ^ Reference image filename
  , poseVideo :: Maybe String      -- ^ Pose video filename or path
  , poseDirectory :: Maybe String  -- ^ Directory of pose frame images
  , width :: Int
  , height :: Int
  , frameCount :: Int
  , fps :: Number
  , prompt :: String
  , negativePrompt :: Maybe String
  }

-- | SCAIL export result
type SCAILExportResult =
  { referenceImage :: String      -- ^ Uploaded reference image filename
  , poseInput :: String           -- ^ Uploaded pose video or image sequence
  , poseWidth :: Int
  , poseHeight :: Int
  , generationWidth :: Int
  , generationHeight :: Int
  , frameCount :: Int
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if export config is valid
isValidConfig :: SCAILExportConfig -> Boolean
isValidConfig c =
  c.width > 0 && c.width <= maxDimension &&
  c.height > 0 && c.height <= maxDimension &&
  c.frameCount > 0 && c.frameCount <= maxFrames &&
  c.fps > 0.0 && c.fps <= maxFPS

-- | Check if export result is valid
isValidResult :: SCAILExportResult -> Boolean
isValidResult r =
  r.poseWidth > 0 && r.poseWidth <= maxDimension &&
  r.poseHeight > 0 && r.poseHeight <= maxDimension &&
  r.generationWidth > 0 && r.generationWidth <= maxDimension &&
  r.generationHeight > 0 && r.generationHeight <= maxDimension &&
  r.frameCount > 0 && r.frameCount <= maxFrames
