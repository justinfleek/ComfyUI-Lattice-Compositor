{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.SCAILSchema
Description : SCAIL export format types
Copyright   : (c) Lattice, 2026
License     : MIT

SCAIL (Pose-Driven Video) export format types.
SCAIL uses reference image (identity/appearance) + pose video/sequence for motion guidance.

Source: ui/src/schemas/exports/scail-schema.ts
-}

module Lattice.Schemas.Exports.SCAILSchema
  ( -- * Constants
    maxDimension
  , maxFrames
  , maxFPS
    -- * Structures
  , SCAILExportConfig(..)
  , SCAILExportResult(..)
    -- * Validation
  , isValidConfig
  , isValidResult
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxDimension :: Int
maxDimension = 16384

maxFrames :: Int
maxFrames = 100000

maxFPS :: Double
maxFPS = 120.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | SCAIL export configuration
data SCAILExportConfig = SCAILExportConfig
  { secReferenceImage :: !Text       -- ^ Reference image filename
  , secPoseVideo :: !(Maybe Text)    -- ^ Pose video filename or path
  , secPoseDirectory :: !(Maybe Text) -- ^ Directory of pose frame images
  , secWidth :: !Int
  , secHeight :: !Int
  , secFrameCount :: !Int
  , secFps :: !Double
  , secPrompt :: !Text
  , secNegativePrompt :: !(Maybe Text)
  }
  deriving stock (Eq, Show, Generic)

-- | SCAIL export result
data SCAILExportResult = SCAILExportResult
  { serReferenceImage :: !Text      -- ^ Uploaded reference image filename
  , serPoseInput :: !Text           -- ^ Uploaded pose video or image sequence
  , serPoseWidth :: !Int
  , serPoseHeight :: !Int
  , serGenerationWidth :: !Int
  , serGenerationHeight :: !Int
  , serFrameCount :: !Int
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if export config is valid
isValidConfig :: SCAILExportConfig -> Bool
isValidConfig c =
  secWidth c > 0 && secWidth c <= maxDimension &&
  secHeight c > 0 && secHeight c <= maxDimension &&
  secFrameCount c > 0 && secFrameCount c <= maxFrames &&
  secFps c > 0 && secFps c <= maxFPS

-- | Check if export result is valid
isValidResult :: SCAILExportResult -> Bool
isValidResult r =
  serPoseWidth r > 0 && serPoseWidth r <= maxDimension &&
  serPoseHeight r > 0 && serPoseHeight r <= maxDimension &&
  serGenerationWidth r > 0 && serGenerationWidth r <= maxDimension &&
  serGenerationHeight r > 0 && serGenerationHeight r <= maxDimension &&
  serFrameCount r > 0 && serFrameCount r <= maxFrames
