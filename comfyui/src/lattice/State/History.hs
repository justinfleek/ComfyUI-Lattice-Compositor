-- |
-- Module      : Lattice.State.History
-- Description : Pure state management functions for history store
-- 
-- Migrated from ui/src/stores/historyStore.ts
-- Pure query functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.History
  ( -- Pure queries (getters)
    canUndo
  , canRedo
  , currentIndex
  , stackSize
  -- Types
  , HistoryState(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  )
import GHC.Generics (Generic)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | History State (for pure queries)
-- Note: We don't store the actual project stack here, just metadata
-- The actual stack is managed in TypeScript
data HistoryState = HistoryState
  { historyStateIndex :: Int
  , historyStateStackSize :: Int
  }
  deriving (Eq, Show, Generic)

instance ToJSON HistoryState where
  toJSON (HistoryState index stackSize) =
    object ["index" .= index, "stackSize" .= stackSize]

instance FromJSON HistoryState where
  parseJSON = withObject "HistoryState" $ \o ->
    HistoryState <$> o .: "index" <*> o .: "stackSize"

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // pure // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if undo is possible
-- Pure function: takes history state, returns boolean
canUndo ::
  HistoryState ->
  Bool
canUndo state = historyStateIndex state > 0

-- | Check if redo is possible
-- Pure function: takes history state, returns boolean
canRedo ::
  HistoryState ->
  Bool
canRedo state =
  let
    idx = historyStateIndex state
    size = historyStateStackSize state
  in
    idx < size - 1

-- | Get current index
-- Pure function: takes history state, returns index
currentIndex ::
  HistoryState ->
  Int
currentIndex state = historyStateIndex state

-- | Get stack size
-- Pure function: takes history state, returns stack size
stackSize ::
  HistoryState ->
  Int
stackSize state = historyStateStackSize state
