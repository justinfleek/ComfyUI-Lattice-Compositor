-- |
-- Module      : Lattice.State.Playback
-- Description : Pure state management functions for playback store
-- 
-- Migrated from ui/src/stores/playbackStore.ts
-- Pure query and calculation functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Playback
  ( PlaybackState(..)
  -- Pure queries (getters)
  , playing
  , hasWorkArea
  , effectiveStartFrame
  , effectiveEndFrame
  -- Pure calculations
  , clampFrame
  , stepForwardFrame
  , stepBackwardFrame
  ) where

import Data.Aeson.Types ((.!=))
import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Utils.NumericSafety
  ( ensureFinite
  )

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Playback state (for pure queries)
-- EVERY VALUE HAS EXPLICIT DEFAULTS - NO Maybe/Nothing
data PlaybackState = PlaybackState
  { playbackStateIsPlaying :: Bool  -- Default: False
  , playbackStateWorkAreaStart :: Double  -- Default: 0.0 (min: 0.0, max: no upper bound)
  , playbackStateWorkAreaStartSet :: Bool  -- Explicit flag: start is set (default: False)
  , playbackStateWorkAreaEnd :: Double  -- Default: 0.0 (min: 0.0, max: no upper bound)
  , playbackStateWorkAreaEndSet :: Bool  -- Explicit flag: end is set (default: False)
  }
  deriving (Eq, Show, Generic)

instance ToJSON PlaybackState where
  toJSON (PlaybackState isPlaying start startSet end_ endSet) =
    let
      baseFields = ["isPlaying" .= isPlaying, "workAreaStartSet" .= startSet, "workAreaEndSet" .= endSet]
      withStart = if startSet then ("workAreaStart" .= start) : baseFields else baseFields
      withEnd = if endSet then ("workAreaEnd" .= end_) : withStart else withStart
    in object withEnd

instance FromJSON PlaybackState where
  parseJSON = withObject "PlaybackState" $ \o -> do
    isPlaying <- o .:? "isPlaying" .!= False
    start <- o .:? "workAreaStart" .!= 0.0
    startSet <- o .:? "workAreaStartSet" .!= False
    end_ <- o .:? "workAreaEnd" .!= 0.0
    endSet <- o .:? "workAreaEndSet" .!= False
    return (PlaybackState isPlaying start startSet end_ endSet)

-- ============================================================================
-- PURE QUERIES (GETTERS)
-- ============================================================================

-- | Check if playback is currently playing
-- Pure function: takes playback state, returns boolean
playing ::
  PlaybackState ->
  Bool
playing state = playbackStateIsPlaying state

-- | Check if work area is set
-- Pure function: takes playback state, returns boolean
-- Uses explicit flags - no Maybe/Nothing
hasWorkArea ::
  PlaybackState ->
  Bool
hasWorkArea state =
  playbackStateWorkAreaStartSet state && playbackStateWorkAreaEndSet state

-- | Get effective start frame (workAreaStart or 0)
-- Pure function: takes playback state, returns start frame
-- Uses explicit flag - no Maybe/Nothing
effectiveStartFrame ::
  PlaybackState ->
  Double
effectiveStartFrame state =
  if playbackStateWorkAreaStartSet state
  then
    let start = playbackStateWorkAreaStart state
        finiteStart = ensureFinite start 0.0
    in if finiteStart >= 0 then finiteStart else 0.0
  else 0.0

-- | Get effective end frame (workAreaEnd or frameCount - 1)
-- Pure function: takes playback state and frameCount, returns end frame
-- Uses explicit flag - no Maybe/Nothing
effectiveEndFrame ::
  PlaybackState ->
  Double ->
  Double
effectiveEndFrame state frameCount =
  let
    finiteFrameCount = ensureFinite frameCount 1.0
    validFrameCount = if finiteFrameCount > 0 then finiteFrameCount else 1.0
    defaultEnd = validFrameCount - 1.0
  in
    if playbackStateWorkAreaEndSet state
    then
      let end_ = playbackStateWorkAreaEnd state
          finiteEnd = ensureFinite end_ defaultEnd
      in if finiteEnd >= 0 then finiteEnd else defaultEnd
    else defaultEnd

-- ============================================================================
-- PURE CALCULATIONS
-- ============================================================================

-- | Clamp frame to valid range [0, frameCount - 1]
-- Pure function: takes frame and frameCount, returns clamped frame
clampFrame ::
  Double ->
  Double ->
  Double
clampFrame frame frameCount =
  let
    finiteFrameCount = ensureFinite frameCount 1.0
    validFrameCount = if finiteFrameCount > 0 then finiteFrameCount else 1.0
    maxFrame = validFrameCount - 1.0
    finiteFrame = ensureFinite frame 0.0
    clamped = if finiteFrame < 0.0 then 0.0 else if finiteFrame > maxFrame then maxFrame else finiteFrame
  in
    clamped

-- | Step forward one frame (increment, clamped to max)
-- Pure function: takes currentFrame and frameCount, returns new frame
stepForwardFrame ::
  Double ->
  Double ->
  Double
stepForwardFrame currentFrame frameCount =
  let
    finiteFrameCount = ensureFinite frameCount 1.0
    validFrameCount = if finiteFrameCount > 0 then finiteFrameCount else 1.0
    maxFrame = validFrameCount - 1.0
    finiteCurrentFrame = ensureFinite currentFrame 0.0
    newFrame = finiteCurrentFrame + 1.0
  in
    if newFrame > maxFrame then maxFrame else newFrame

-- | Step backward one frame (decrement, clamped to min)
-- Pure function: takes currentFrame, returns new frame
stepBackwardFrame ::
  Double ->
  Double
stepBackwardFrame currentFrame =
  let
    finiteCurrentFrame = ensureFinite currentFrame 0.0
    newFrame = finiteCurrentFrame - 1.0
  in
    if newFrame < 0.0 then 0.0 else newFrame
