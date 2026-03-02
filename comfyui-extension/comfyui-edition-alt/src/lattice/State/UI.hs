-- |
-- Module      : Lattice.State.UI
-- Description : Pure state management functions for UI store
-- 
-- Migrated from ui/src/stores/uiStore.ts
-- Pure query functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.UI
  ( -- Pure queries (getters)
    isCurveEditorVisible
  , shouldHideMinimizedLayers
  -- Types
  , UIState(..)
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

-- | UI State (for pure queries)
data UIState = UIState
  { uiStateCurveEditorVisible :: Bool
  , uiStateHideMinimizedLayers :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON UIState where
  toJSON (UIState curveEditorVisible hideMinimizedLayers) =
    object
      [ "curveEditorVisible" .= curveEditorVisible
      , "hideMinimizedLayers" .= hideMinimizedLayers
      ]

instance FromJSON UIState where
  parseJSON = withObject "UIState" $ \o ->
    UIState <$> o .: "curveEditorVisible" <*> o .: "hideMinimizedLayers"

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // pure // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if curve editor is visible
-- Pure function: takes UI state, returns boolean
isCurveEditorVisible ::
  UIState ->
  Bool
isCurveEditorVisible state = uiStateCurveEditorVisible state

-- | Check if minimized layers should be hidden
-- Pure function: takes UI state, returns boolean
shouldHideMinimizedLayers ::
  UIState ->
  Bool
shouldHideMinimizedLayers state = uiStateHideMinimizedLayers state
