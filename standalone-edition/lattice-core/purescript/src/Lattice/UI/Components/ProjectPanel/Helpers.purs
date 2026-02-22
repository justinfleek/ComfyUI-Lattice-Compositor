-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | ProjectPanel Helpers
-- |
-- | Data transformation and utility functions for project panel.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.ProjectPanel.Helpers
  ( getAllFolders
  , compositionToItem
  , getFilteredFolders
  , filterBySearch
  , matchesSearch
  , getRootItems
  , getAllItems
  , getSelectedPreview
  , getSelectedItemDetails
  , getItemInfo
  , getItemIcon
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Tuple (Tuple(..))

import Lattice.UI.Utils as Utils
import Lattice.UI.Components.ProjectPanel.Types
  ( State
  , ProjectItem
  , ProjectItemType(..)
  , Folder
  , CompositionInfo
  , SelectedPreview
  )

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // folder management
-- ════════════════════════════════════════════════════════════════════════════

getAllFolders :: State -> Array Folder
getAllFolders state =
  let
    compositionFolder =
      { id: "compositions"
      , name: "Compositions"
      , items: map compositionToItem state.input.compositions
      }
    footageFolder =
      { id: "footage"
      , name: "Footage"
      , items: state.input.footage
      }
    solidsFolder =
      { id: "solids"
      , name: "Solids"
      , items: state.input.solids
      }
  in
    [ compositionFolder, footageFolder, solidsFolder ] <> state.customFolders

compositionToItem :: CompositionInfo -> ProjectItem
compositionToItem comp =
  { id: comp.id
  , name: comp.name
  , itemType: ItemComposition
  , width: Just comp.width
  , height: Just comp.height
  , duration: Just comp.frameCount
  , fps: Just comp.fps
  , dataType: Nothing
  , dataInfo: Nothing
  }

getFilteredFolders :: State -> Array Folder
getFilteredFolders state =
  if String.null state.searchQuery
    then getAllFolders state
    else
      let
        query = String.toLower state.searchQuery
        filterFolder folder =
          let
            filtered = Array.filter (matchesSearch query) folder.items
            nameMatch = String.contains (String.Pattern query) (String.toLower folder.name)
          in
            if Array.null filtered && not nameMatch
              then Nothing
              else Just (folder { items = filtered })
      in
        Array.mapMaybe filterFolder (getAllFolders state)

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // search filtering
-- ════════════════════════════════════════════════════════════════════════════

filterBySearch :: String -> Array ProjectItem -> Array ProjectItem
filterBySearch query items =
  if String.null query
    then items
    else
      let q = String.toLower query
      in Array.filter (matchesSearch q) items

matchesSearch :: String -> ProjectItem -> Boolean
matchesSearch query item =
  String.contains (String.Pattern query) (String.toLower item.name)

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // item collection
-- ════════════════════════════════════════════════════════════════════════════

getRootItems :: State -> Array ProjectItem
getRootItems _state = []

getAllItems :: State -> Array ProjectItem
getAllItems state =
  let
    folders = getAllFolders state
    folderItems = Array.concatMap _.items folders
  in
    folderItems <> getRootItems state

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // preview helpers
-- ════════════════════════════════════════════════════════════════════════════

getSelectedPreview :: State -> Maybe SelectedPreview
getSelectedPreview state =
  case state.selectedItem of
    Nothing -> Nothing
    Just itemId ->
      let
        allItems = getAllItems state
        maybeItem = Array.find (\i -> i.id == itemId) allItems
      in
        case maybeItem of
          Nothing -> Nothing
          Just item ->
            Just
              { previewType: show item.itemType
              , name: item.name
              , details: getItemInfo item
              , icon: getPreviewIcon item.itemType
              , url: Nothing
              }

getPreviewIcon :: ProjectItemType -> String
getPreviewIcon = case _ of
  ItemComposition -> "[C]"
  ItemFootage -> "[F]"
  ItemSolid -> "[S]"
  ItemAudio -> "[A]"
  ItemFolder -> "[D]"
  ItemData -> "[I]"

getSelectedItemDetails :: State -> Maybe { name :: String, info :: String }
getSelectedItemDetails state =
  case state.selectedItem of
    Nothing -> Nothing
    Just itemId ->
      let
        allItems = getAllItems state
        maybeItem = Array.find (\i -> i.id == itemId) allItems
      in
        case maybeItem of
          Nothing -> Nothing
          Just item ->
            Just { name: item.name, info: getItemInfo item }

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // item info formatting
-- ════════════════════════════════════════════════════════════════════════════

getItemInfo :: ProjectItem -> String
getItemInfo item =
  case item.itemType of
    ItemComposition ->
      let
        dims = case item.width, item.height of
          Just w, Just h -> show w <> "x" <> show h
          _, _ -> "Unknown size"
        dur = case item.duration of
          Just d -> show d <> " frames"
          Nothing -> "Unknown duration"
      in dims <> " | " <> dur
    ItemFootage ->
      let
        dims = case item.width, item.height of
          Just w, Just h -> show w <> "x" <> show h
          _, _ -> ""
        dur = case item.duration, item.fps of
          Just d, Just f | f > 0 ->
            let secs = Utils.toNumber d / Utils.toNumber f
            in Utils.formatFixed 1 secs <> "s"
          _, _ -> ""
        parts = Array.filter (_ /= "") [dims, dur]
      in String.joinWith " | " parts
    ItemSolid ->
      case item.width, item.height of
        Just w, Just h -> show w <> "x" <> show h
        _, _ -> "Solid"
    ItemAudio ->
      case item.duration of
        Just d -> show d <> " frames"
        Nothing -> "Audio"
    ItemFolder ->
      "Folder"
    ItemData ->
      formatDataInfo item

getItemIcon :: ProjectItemType -> String
getItemIcon = case _ of
  ItemComposition -> "[C]"
  ItemFootage -> "[F]"
  ItemSolid -> "[S]"
  ItemAudio -> "[A]"
  ItemFolder -> "[D]"
  ItemData -> "[I]"

formatDataInfo :: ProjectItem -> String
formatDataInfo item =
  let
    dtype = fromMaybe "" item.dataType
    info = fromMaybe "" item.dataInfo
    parts = Array.filter (\s -> s /= "") [String.toUpper dtype, info]
  in
    String.joinWith " - " parts
