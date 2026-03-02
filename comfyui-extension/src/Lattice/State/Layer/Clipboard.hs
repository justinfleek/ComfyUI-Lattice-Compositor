-- |
-- Module      : Lattice.State.Layer.Clipboard
-- Description : Clipboard operations for layers
-- 
-- Extracted from Lattice.State.Layer
-- Pure functions for copying, cutting, and pasting layers
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Clipboard
  ( setClipboard
  , clearClipboard
  , getClipboardLayers
  , copySelectedLayers
  , pasteLayers
  , cutSelectedLayers
  ) where

import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.List (foldl)
import Data.Text (Text)
import Lattice.State.Layer.CRUD (cleanUpLayerReferences, regenerateKeyframeIds)
import Lattice.State.Layer.Types (LayerStateClipboard(..))
import Lattice.Types.Animation (ClipboardKeyframe(..))
import Lattice.Types.Layer (Layer(..))

-- ============================================================================
-- CLIPBOARD OPERATIONS
-- ============================================================================

-- | Set clipboard contents
-- Pure function: takes layers and keyframes, returns new clipboard state
setClipboard ::
  [Layer] -> -- Layers to copy
  [ClipboardKeyframe] -> -- Keyframes to copy
  LayerStateClipboard -> -- Current clipboard state
  LayerStateClipboard -- New clipboard state with copied items
setClipboard layers keyframes _ =
  LayerStateClipboard
    { layerStateClipboardLayers = layers
    , layerStateClipboardKeyframes = keyframes
    }

-- | Clear clipboard contents
-- Pure function: returns empty clipboard state
clearClipboard :: LayerStateClipboard -> LayerStateClipboard
clearClipboard _ =
  LayerStateClipboard
    { layerStateClipboardLayers = []
    , layerStateClipboardKeyframes = []
    }

-- | Get clipboard layers
-- Pure function: takes clipboard state, returns layers
getClipboardLayers :: LayerStateClipboard -> [Layer]
getClipboardLayers clipboard = layerStateClipboardLayers clipboard

-- | Copy selected layers to clipboard
-- Pure function: takes selected layer IDs and layers list, returns new clipboard state
copySelectedLayers ::
  HashSet Text -> -- Selected layer IDs
  [Layer] -> -- All layers
  LayerStateClipboard -> -- Current clipboard state
  LayerStateClipboard -- New clipboard state with copied layers
copySelectedLayers selectedIds layers _ =
  let
    selectedLayers = filter (\l -> HS.member (layerId l) selectedIds) layers
  in
    LayerStateClipboard
      { layerStateClipboardLayers = selectedLayers
      , layerStateClipboardKeyframes = []
      }

-- | Paste layers from clipboard
-- Pure function: takes clipboard state, ID generators, and layers list
-- Returns new layers list with pasted layers inserted at the beginning
-- Regenerates IDs and clears parent references
pasteLayers ::
  LayerStateClipboard -> -- Clipboard state
  (Text -> Text) -> -- ID generator for new layer IDs
  (Text -> Text) -> -- ID generator for regenerating keyframe IDs
  [Layer] -> -- Current layers list
  [Layer] -- Returns new layers list with pasted layers
pasteLayers clipboard genLayerId genKeyframeId layers =
  let
    clipboardLayers = layerStateClipboardLayers clipboard
  in
    if null clipboardLayers
      then layers
      else
        let
          -- Paste each clipboard layer with new IDs
          pastedLayers =
            map (\clipboardLayer ->
              let
                newLayerId = genLayerId (layerId clipboardLayer)
                layerWithNewId = clipboardLayer
                  { layerId = newLayerId
                  , layerName = layerName clipboardLayer <> " Copy"
                  , layerParentId = Nothing -- Clear parent reference
                  }
                layerWithNewKeyframes = regenerateKeyframeIds genKeyframeId layerWithNewId
              in
                layerWithNewKeyframes
            )
            clipboardLayers
        in
          pastedLayers ++ layers -- Insert at beginning

-- | Cut selected layers (copy + delete)
-- Pure function: takes selected layer IDs, layers list, and clipboard state
-- Returns new layers list (with selected layers removed) and new clipboard state (with copied layers)
cutSelectedLayers ::
  HashSet Text -> -- Selected layer IDs
  [Layer] -> -- Current layers list
  LayerStateClipboard -> -- Current clipboard state
  ([Layer], LayerStateClipboard) -- Returns (new layers list without cut layers, new clipboard state with copied layers)
cutSelectedLayers selectedIds layers currentClipboard =
  let
    -- Copy selected layers to clipboard
    selectedLayers = filter (\l -> HS.member (layerId l) selectedIds) layers
    newClipboard = LayerStateClipboard
      { layerStateClipboardLayers = selectedLayers
      , layerStateClipboardKeyframes = []
      }
    
    -- Delete selected layers from layers list
    remainingLayers = filter (\l -> not (HS.member (layerId l) selectedIds)) layers
    
    -- Clean up references to deleted layers
    deletedIds = HS.toList selectedIds
    cleanedLayers = foldl (\acc deletedId -> cleanUpLayerReferences deletedId acc) remainingLayers deletedIds
  in
    (cleanedLayers, newClipboard)
