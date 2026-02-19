-- | Project Store
-- |
-- | Centralized state management for the current project.
-- | Uses a simple ReaderT pattern for state access.
module Lattice.UI.Store.ProjectStore
  ( ProjectState
  , ProjectAction(..)
  , initialProjectState
  , projectReducer
  , getSelectedLayers
  , getVisibleLayers
  , findLayerById
  ) where

import Prelude

import Data.Array (filter, find, take, drop)
import Data.Maybe (Maybe(..))
import Lattice.Project (LatticeProject, LayerBase, Composition, createEmptyProject)
import Lattice.Primitives (NonEmptyString, mkNonEmptyString)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type ProjectState =
  { project :: LatticeProject
  , currentCompId :: String
  , selectedLayerIds :: Array String
  , currentFrame :: Int
  , isPlaying :: Boolean
  , isDirty :: Boolean
  }

data ProjectAction
  = SetProject LatticeProject
  | SelectLayer String
  | SelectLayers (Array String)
  | DeselectAll
  | ToggleLayerSelection String
  | SetLayerVisibility String Boolean
  | SetLayerLocked String Boolean
  | SetCurrentFrame Int
  | SetPlaying Boolean
  | AddLayer LayerBase
  | RemoveLayer String
  | ReorderLayer String Int
  | SetCurrentComposition String

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // initial // state
-- ════════════════════════════════════════════════════════════════════════════

initialProjectState :: ProjectState
initialProjectState =
  let
    timestamp = case mkNonEmptyString "2026-02-19T00:00:00Z" of
      Just t -> t
      Nothing -> unsafeNes "now"
    project = createEmptyProject 1920 1080 timestamp
  in
  { project
  , currentCompId: "main"
  , selectedLayerIds: []
  , currentFrame: 0
  , isPlaying: false
  , isDirty: false
  }
  where
    unsafeNes :: String -> NonEmptyString
    unsafeNes s = case mkNonEmptyString s of
      Just v -> v
      Nothing -> unsafeNes "error"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // reducer
-- ════════════════════════════════════════════════════════════════════════════

projectReducer :: ProjectState -> ProjectAction -> ProjectState
projectReducer state = case _ of
  SetProject project ->
    state { project = project, isDirty = false }
  
  SelectLayer layerId ->
    state { selectedLayerIds = [layerId] }
  
  SelectLayers layerIds ->
    state { selectedLayerIds = layerIds }
  
  DeselectAll ->
    state { selectedLayerIds = [] }
  
  ToggleLayerSelection layerId ->
    let
      isSelected = layerId `elem` state.selectedLayerIds
      newIds = if isSelected
        then filter (_ /= layerId) state.selectedLayerIds
        else state.selectedLayerIds <> [layerId]
    in
    state { selectedLayerIds = newIds }
  
  SetLayerVisibility layerId visible ->
    updateLayer state layerId (_ { visible = visible })
  
  SetLayerLocked layerId locked ->
    updateLayer state layerId (_ { locked = locked })
  
  SetCurrentFrame frame ->
    state { currentFrame = frame }
  
  SetPlaying playing ->
    state { isPlaying = playing }
  
  AddLayer layer ->
    addLayerToComp state layer
  
  RemoveLayer layerId ->
    removeLayerFromComp state layerId
  
  ReorderLayer layerId targetIndex ->
    reorderLayerInComp state layerId targetIndex
  
  SetCurrentComposition compId ->
    state { currentCompId = compId }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Get the current composition
getCurrentComp :: ProjectState -> Maybe Composition
getCurrentComp state =
  find (\c -> show c.id == state.currentCompId) state.project.compositions

-- | Get layers from current composition
getCurrentLayers :: ProjectState -> Array LayerBase
getCurrentLayers state =
  case getCurrentComp state of
    Just comp -> comp.layers
    Nothing -> []

-- | Get selected layers
getSelectedLayers :: ProjectState -> Array LayerBase
getSelectedLayers state =
  let layers = getCurrentLayers state
  in filter (\l -> show l.id `elem` state.selectedLayerIds) layers

-- | Get visible layers
getVisibleLayers :: ProjectState -> Array LayerBase
getVisibleLayers state =
  filter _.visible (getCurrentLayers state)

-- | Find a layer by ID
findLayerById :: ProjectState -> String -> Maybe LayerBase
findLayerById state layerId =
  find (\l -> show l.id == layerId) (getCurrentLayers state)

-- | Update a layer in the current composition
updateLayer :: ProjectState -> String -> (LayerBase -> LayerBase) -> ProjectState
updateLayer state layerId f =
  let
    updateComp comp =
      if show comp.id == state.currentCompId
        then comp { layers = map updateIfMatch comp.layers }
        else comp
    updateIfMatch layer =
      if show layer.id == layerId
        then f layer
        else layer
    newComps = map updateComp state.project.compositions
    newProject = state.project { compositions = newComps }
  in
  state { project = newProject, isDirty = true }

-- | Add a layer to the current composition
addLayerToComp :: ProjectState -> LayerBase -> ProjectState
addLayerToComp state layer =
  let
    updateComp comp =
      if show comp.id == state.currentCompId
        then comp { layers = [layer] <> comp.layers }
        else comp
    newComps = map updateComp state.project.compositions
    newProject = state.project { compositions = newComps }
  in
  state { project = newProject, isDirty = true }

-- | Remove a layer from the current composition
removeLayerFromComp :: ProjectState -> String -> ProjectState
removeLayerFromComp state layerId =
  let
    updateComp comp =
      if show comp.id == state.currentCompId
        then comp { layers = filter (\l -> show l.id /= layerId) comp.layers }
        else comp
    newComps = map updateComp state.project.compositions
    newProject = state.project { compositions = newComps }
    newSelected = filter (_ /= layerId) state.selectedLayerIds
  in
  state { project = newProject, selectedLayerIds = newSelected, isDirty = true }

-- | Reorder a layer to a new index
reorderLayerInComp :: ProjectState -> String -> Int -> ProjectState
reorderLayerInComp state layerId targetIndex =
  let
    updateComp comp =
      if show comp.id == state.currentCompId
        then comp { layers = reorderArray comp.layers layerId targetIndex }
        else comp
    newComps = map updateComp state.project.compositions
    newProject = state.project { compositions = newComps }
  in
  state { project = newProject, isDirty = true }

-- | Reorder an array by moving an element to a new index
reorderArray :: Array LayerBase -> String -> Int -> Array LayerBase
reorderArray layers layerId targetIndex =
  case find (\l -> show l.id == layerId) layers of
    Nothing -> layers
    Just layer ->
      let
        without = filter (\l -> show l.id /= layerId) layers
        before = take targetIndex without
        after = drop targetIndex without
      in
      before <> [layer] <> after

-- | Check if element is in array
elem :: forall a. Eq a => a -> Array a -> Boolean
elem x arr = case find (_ == x) arr of
  Just _ -> true
  Nothing -> false
