-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Effect Controls Panel Component
-- |
-- | Displays and edits effect parameters for a selected layer.
-- | Features:
-- | - Collapsible effect sections with enable/disable toggles
-- | - Parameter editing (sliders, color pickers, angles, positions, enums)
-- | - Keyframe animation toggles per parameter
-- | - Drag-and-drop effect reordering
-- | - Add effect dropdown menu by category
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/EffectControlsPanel.vue
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.EffectControlsPanel
  ( component
  , module Types
  ) where

import Prelude

import Control.Monad (when)
import Data.Array (filter, snoc)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Components.EffectControlsPanel.Types
  ( Input
  , Output(..)
  , Query
  , Slot
  , State
  , Action(..)
  , Slots
  , EffectInstance
  , EffectParameter
  , ParameterType(..)
  , ParameterValue(..)
  ) as Types
import Lattice.UI.Components.EffectControlsPanel.Render (render)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Types.Input Types.Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Types.Initialize
      , receive = Just <<< Types.Receive
      }
  }

initialState :: Types.Input -> Types.State
initialState input =
  { layer: input.layer
  , availableLayers: input.availableLayers
  , showAddMenu: false
  , expandedCategories: []
  , dragState: Nothing
  , baseId: "lattice-effect-controls"
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Types.Action -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
handleAction = case _ of
  Types.Initialize -> pure unit

  Types.Receive input -> do
    H.modify_ _ { layer = input.layer, availableLayers = input.availableLayers }

  Types.ToggleAddMenu -> do
    H.modify_ \s -> s { showAddMenu = not s.showAddMenu }

  Types.CloseAddMenu -> do
    H.modify_ _ { showAddMenu = false }

  Types.ToggleEffectCategory cat -> do
    state <- H.get
    let cats = state.expandedCategories
    let newCats = if Array.elem cat cats
                    then filter (_ /= cat) cats
                    else snoc cats cat
    H.modify_ _ { expandedCategories = newCats }

  Types.AddEffect effectKey -> do
    state <- H.get
    case state.layer of
      Just layer -> do
        H.raise (Types.EffectAdded layer.id effectKey)
        H.modify_ _ { showAddMenu = false }
      Nothing -> pure unit

  Types.RemoveEffect effectId -> do
    state <- H.get
    case state.layer of
      Just layer -> H.raise (Types.EffectRemoved layer.id effectId)
      Nothing -> pure unit

  Types.ToggleEffect effectId -> do
    state <- H.get
    case state.layer of
      Just layer ->
        case Array.find (\e -> e.id == effectId) layer.effects of
          Just effect -> H.raise (Types.EffectToggled layer.id effectId (not effect.enabled))
          Nothing -> pure unit
      Nothing -> pure unit

  Types.ToggleEffectExpanded effectId -> do
    -- toggle locally in layer data
    state <- H.get
    case state.layer of
      Just layer ->
        let
          updatedEffects = map (\e -> 
            if e.id == effectId 
              then e { expanded = not e.expanded }
              else e
          ) layer.effects
          updatedLayer = layer { effects = updatedEffects }
        in
          H.modify_ _ { layer = Just updatedLayer }
      Nothing -> pure unit

  Types.UpdateParameter effectId paramKey value -> do
    state <- H.get
    case state.layer of
      Just layer -> H.raise (Types.ParameterChanged layer.id effectId paramKey value)
      Nothing -> pure unit

  Types.ToggleParameterAnimation effectId paramKey -> do
    state <- H.get
    case state.layer of
      Just layer ->
        case Array.find (\e -> e.id == effectId) layer.effects of
          Just effect ->
            case Array.find (\(Tuple k _) -> k == paramKey) effect.parameters of
              Just (Tuple _ param) ->
                H.raise (Types.ParameterAnimationToggled layer.id effectId paramKey (not param.animated))
              Nothing -> pure unit
          Nothing -> pure unit
      Nothing -> pure unit

  Types.StartDrag index -> do
    H.modify_ _ { dragState = Just { fromIndex: index, overIndex: Nothing } }

  Types.DragOver index -> do
    H.modify_ \s -> case s.dragState of
      Just ds -> s { dragState = Just (ds { overIndex = Just index }) }
      Nothing -> s

  Types.DragEnd -> do
    H.modify_ _ { dragState = Nothing }

  Types.Drop targetIndex -> do
    state <- H.get
    case state.dragState, state.layer of
      Just ds, Just layer -> do
        when (ds.fromIndex /= targetIndex) do
          H.raise (Types.EffectReordered layer.id ds.fromIndex targetIndex)
        H.modify_ _ { dragState = Nothing }
      _, _ -> H.modify_ _ { dragState = Nothing }

  Types.HandleKeyDown ke -> do
    let key = KE.key ke
    case key of
      "Escape" -> handleAction Types.CloseAddMenu
      _ -> pure unit
