-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Project Panel Component
-- |
-- | Project management panel for organizing compositions, footage, and assets.
-- | Supports:
-- | - Folder hierarchy with expand/collapse
-- | - Search filtering
-- | - Asset preview thumbnails
-- | - Drag and drop for timeline import
-- | - Keyboard navigation (Arrow keys, Enter, Space)
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/ProjectPanel.vue
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.ProjectPanel
  ( component
  , module Types
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Components.ProjectPanel.Types
  ( Input
  , Output(..)
  , Query(..)
  , Slot
  , ProjectItem
  , ProjectItemType(..)
  , Folder
  , State
  , Action(..)
  , Slots
  ) as Types
import Lattice.UI.Components.ProjectPanel.Render (render)
import Lattice.UI.Components.ProjectPanel.Helpers (getAllItems)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Types.Query Types.Input Types.Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Types.Initialize
      , receive = Just <<< Types.Receive
      }
  }

initialState :: Types.Input -> Types.State
initialState input =
  { input: input
  , baseId: "project-panel"
  , showSearch: false
  , showNewMenu: false
  , searchQuery: ""
  , selectedItem: Nothing
  , expandedFolders: ["compositions", "footage"]
  , customFolders: []
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Types.Action -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
handleAction = case _ of
  Types.Initialize -> pure unit

  Types.Receive input -> do
    H.modify_ _ { input = input }

  Types.ToggleSearch -> do
    H.modify_ \s -> s { showSearch = not s.showSearch }

  Types.ToggleNewMenu -> do
    H.modify_ \s -> s { showNewMenu = not s.showNewMenu }

  Types.UpdateSearchQuery query -> do
    H.modify_ _ { searchQuery = query }

  Types.SelectItem itemId -> do
    H.modify_ _ { selectedItem = Just itemId, showNewMenu = false }

  Types.ToggleFolder folderId -> do
    H.modify_ \s ->
      if Array.elem folderId s.expandedFolders
        then s { expandedFolders = Array.filter (_ /= folderId) s.expandedFolders }
        else s { expandedFolders = s.expandedFolders <> [folderId] }

  Types.OpenItem item -> do
    case item.itemType of
      Types.ItemComposition -> H.raise (Types.OpenComposition item.id)
      Types.ItemFolder -> handleAction (Types.ToggleFolder item.id)
      _ -> H.raise (Types.CreateLayer item)

  Types.HandleKeyDown _idx event -> do
    let key = KE.key event
    case key of
      "Enter" -> do
        state <- H.get
        case state.selectedItem of
          Nothing -> pure unit
          Just itemId -> do
            let allItems = getAllItems state
            case Array.find (\i -> i.id == itemId) allItems of
              Just item -> handleAction (Types.OpenItem item)
              Nothing -> pure unit
      "ArrowDown" -> navigateItems 1
      "ArrowUp" -> navigateItems (-1)
      "ArrowRight" -> expandSelected
      "ArrowLeft" -> collapseSelected
      _ -> pure unit

  Types.TriggerImport -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.ImportFile

  Types.CreateCompositionAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.CreateComposition

  Types.CreateFolderAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.CreateFolder

  Types.CreateSolidAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.CreateSolid

  Types.CreateTextAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.CreateText

  Types.CreateSplineAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.CreateSpline

  Types.CreateModelAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.CreateModel

  Types.CreatePointCloudAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.CreatePointCloud

  Types.OpenDecomposeAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.OpenDecomposeDialog

  Types.OpenVectorizeAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.OpenVectorizeDialog

  Types.CleanupAction -> do
    H.modify_ _ { showNewMenu = false }
    H.raise Types.CleanupUnusedAssets

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // navigation
-- ════════════════════════════════════════════════════════════════════════════

navigateItems :: forall m. MonadAff m => Int -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
navigateItems delta = do
  state <- H.get
  let
    allItems = getAllItems state
    maybeIdx = case state.selectedItem of
      Nothing -> if delta > 0 then Just 0 else Nothing
      Just itemId -> Array.findIndex (\i -> i.id == itemId) allItems
    newIdx = case maybeIdx of
      Nothing -> 0
      Just idx -> max 0 (min (Array.length allItems - 1) (idx + delta))
  case Array.index allItems newIdx of
    Just item -> H.modify_ _ { selectedItem = Just item.id }
    Nothing -> pure unit

expandSelected :: forall m. MonadAff m => H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
expandSelected = do
  state <- H.get
  case state.selectedItem of
    Nothing -> pure unit
    Just itemId ->
      if not (Array.elem itemId state.expandedFolders)
        then H.modify_ \s -> s { expandedFolders = s.expandedFolders <> [itemId] }
        else pure unit

collapseSelected :: forall m. MonadAff m => H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
collapseSelected = do
  state <- H.get
  case state.selectedItem of
    Nothing -> pure unit
    Just itemId ->
      if Array.elem itemId state.expandedFolders
        then H.modify_ \s -> s { expandedFolders = Array.filter (_ /= itemId) s.expandedFolders }
        else pure unit

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Types.Query a -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m (Maybe a)
handleQuery = case _ of
  Types.RefreshItems next -> do
    pure (Just next)

  Types.SetSelectedItem maybeId next -> do
    H.modify_ _ { selectedItem = maybeId }
    pure (Just next)
