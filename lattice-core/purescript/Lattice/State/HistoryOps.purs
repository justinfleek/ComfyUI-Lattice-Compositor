-- | Lattice.State.HistoryOps - Pure history/undo/redo state transitions
-- |
-- | Port of ui/src/stores/projectStore/history.ts (pure subset)
-- | All functions are pure state transitions on a HistoryState record.

module Lattice.State.HistoryOps
  ( HistoryState
  , mkHistoryState
  , pushHistory
  , undo
  , redo
  , canUndo
  , canRedo
  , clearHistory
  , historyLength
  , maxHistorySize
  ) where

import Prelude

import Data.Array (length, snoc, index, slice, take)
import Data.Maybe (Maybe(..), fromMaybe)

-- | Maximum number of history states
maxHistorySize :: Int
maxHistorySize = 50

-- | A generic history state container
-- | `a` is the snapshot type (e.g., project JSON string)
type HistoryState a =
  { stack :: Array a
  , index :: Int
  }

-- | Create initial history state with one snapshot
mkHistoryState :: forall a. a -> HistoryState a
mkHistoryState initial =
  { stack: [initial]
  , index: 0
  }

-- | Push a new state snapshot. Truncates future history if we've undone.
-- | Enforces maximum history size.
pushHistory :: forall a. a -> HistoryState a -> HistoryState a
pushHistory snapshot state =
  let
    -- Truncate any future states (everything after current index)
    truncated = take (state.index + 1) state.stack
    -- Add new snapshot
    withNew = snoc truncated snapshot
    -- Enforce max size - drop oldest if needed
    trimmed = if length withNew > maxHistorySize
              then slice (length withNew - maxHistorySize) (length withNew) withNew
              else withNew
  in { stack: trimmed
     , index: length trimmed - 1
     }

-- | Undo: move index back one step. Returns current snapshot at new index.
undo :: forall a. HistoryState a -> { state :: HistoryState a, snapshot :: Maybe a }
undo state =
  if canUndo state
  then
    let newIdx = state.index - 1
        newState = state { index = newIdx }
    in { state: newState, snapshot: index state.stack newIdx }
  else { state: state, snapshot: Nothing }

-- | Redo: move index forward one step. Returns current snapshot at new index.
redo :: forall a. HistoryState a -> { state :: HistoryState a, snapshot :: Maybe a }
redo state =
  if canRedo state
  then
    let newIdx = state.index + 1
        newState = state { index = newIdx }
    in { state: newState, snapshot: index state.stack newIdx }
  else { state: state, snapshot: Nothing }

-- | Check if undo is possible
canUndo :: forall a. HistoryState a -> Boolean
canUndo state = state.index > 0

-- | Check if redo is possible
canRedo :: forall a. HistoryState a -> Boolean
canRedo state = state.index < length state.stack - 1

-- | Clear history, keeping only the current state
clearHistory :: forall a. HistoryState a -> HistoryState a
clearHistory state =
  case index state.stack state.index of
    Just current -> mkHistoryState current
    Nothing -> state

-- | Get total number of history states
historyLength :: forall a. HistoryState a -> Int
historyLength state = length state.stack
