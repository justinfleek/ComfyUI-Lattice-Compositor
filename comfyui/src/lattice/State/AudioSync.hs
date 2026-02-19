-- |
-- Module      : Lattice.State.AudioSync
-- Description : Pure state management functions for audio synchronization
-- 
-- Migrated from ui/src/stores/audioSync.ts
-- Pure functions extracted - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.AudioSync
  ( -- Comparison functions
    checkAudioStateSync
  -- Types
  , AudioState(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.Maybe (Maybe)
import Data.Text (Text)
import GHC.Generics (Generic)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // audio // state
-- ════════════════════════════════════════════════════════════════════════════

-- | Audio state with minimal fields for sync comparison
-- In TypeScript, this compares by reference, but in Haskell we compare by ID/value
data AudioState = AudioState
  { audioStateBufferId :: Maybe Text -- AudioBuffer ID (or hash)
  , audioStateFileId :: Maybe Text -- File ID (or hash)
  }
  deriving (Eq, Show, Generic)

instance ToJSON AudioState where
  toJSON (AudioState bufferId fileId) =
    object
      [ "audioBufferId" .= bufferId
      , "audioFileId" .= fileId
      ]

instance FromJSON AudioState where
  parseJSON = withObject "AudioState" $ \o -> do
    bufferId <- o .:? "audioBufferId"
    fileId <- o .:? "audioFileId"
    return (AudioState bufferId fileId)

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // comparison // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if two audio states are in sync
-- Pure function: takes two audio states, returns Bool
-- In TypeScript this compares by reference, but in Haskell we compare by ID/value
checkAudioStateSync :: AudioState -> AudioState -> Bool
checkAudioStateSync a b =
  audioStateBufferId a == audioStateBufferId b
    && audioStateFileId a == audioStateFileId b
