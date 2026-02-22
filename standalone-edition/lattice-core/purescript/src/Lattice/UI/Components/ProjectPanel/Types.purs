-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | ProjectPanel Types
-- |
-- | Type definitions for project management panel.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.ProjectPanel.Types
  ( Input
  , Output(..)
  , Query(..)
  , Slot
  , ProjectItem
  , ProjectItemType(..)
  , Folder
  , CompositionInfo
  , SelectedPreview
  , State
  , Action(..)
  , Slots
  ) where

import Prelude

import Data.Maybe (Maybe)
import Halogen as H
import Web.UIEvent.KeyboardEvent as KE

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // input
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { compositions :: Array CompositionInfo
  , footage :: Array ProjectItem
  , solids :: Array ProjectItem
  , dataAssets :: Array ProjectItem
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // output
-- ════════════════════════════════════════════════════════════════════════════

data Output
  = OpenComposition String
  | CreateLayer ProjectItem
  | ImportFile
  | CreateComposition
  | CreateFolder
  | CreateSolid
  | CreateText
  | CreateSpline
  | CreateModel
  | CreatePointCloud
  | OpenDecomposeDialog
  | OpenVectorizeDialog
  | CleanupUnusedAssets

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // query
-- ════════════════════════════════════════════════════════════════════════════

data Query a
  = RefreshItems a
  | SetSelectedItem (Maybe String) a

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // project item types
-- ════════════════════════════════════════════════════════════════════════════

data ProjectItemType
  = ItemComposition
  | ItemFootage
  | ItemSolid
  | ItemAudio
  | ItemFolder
  | ItemData

derive instance eqProjectItemType :: Eq ProjectItemType

instance showProjectItemType :: Show ProjectItemType where
  show = case _ of
    ItemComposition -> "composition"
    ItemFootage -> "footage"
    ItemSolid -> "solid"
    ItemAudio -> "audio"
    ItemFolder -> "folder"
    ItemData -> "data"

type ProjectItem =
  { id :: String
  , name :: String
  , itemType :: ProjectItemType
  , width :: Maybe Int
  , height :: Maybe Int
  , duration :: Maybe Int
  , fps :: Maybe Int
  , dataType :: Maybe String
  , dataInfo :: Maybe String
  }

type CompositionInfo =
  { id :: String
  , name :: String
  , width :: Int
  , height :: Int
  , fps :: Int
  , frameCount :: Int
  }

type Folder =
  { id :: String
  , name :: String
  , items :: Array ProjectItem
  }

type SelectedPreview =
  { previewType :: String
  , name :: String
  , details :: String
  , icon :: String
  , url :: Maybe String
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { input :: Input
  , baseId :: String
  , showSearch :: Boolean
  , showNewMenu :: Boolean
  , searchQuery :: String
  , selectedItem :: Maybe String
  , expandedFolders :: Array String
  , customFolders :: Array Folder
  }

data Action
  = Initialize
  | Receive Input
  | ToggleSearch
  | ToggleNewMenu
  | UpdateSearchQuery String
  | SelectItem String
  | ToggleFolder String
  | OpenItem ProjectItem
  | HandleKeyDown Int KE.KeyboardEvent
  | TriggerImport
  | CreateCompositionAction
  | CreateFolderAction
  | CreateSolidAction
  | CreateTextAction
  | CreateSplineAction
  | CreateModelAction
  | CreatePointCloudAction
  | OpenDecomposeAction
  | OpenVectorizeAction
  | CleanupAction

type Slots :: Row Type
type Slots = ()
