-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Effect Controls Panel Render
-- |
-- | Render functions for effect parameter editing UI.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.EffectControlsPanel.Render
  ( render
  ) where

import Prelude

import Data.Array (length, mapWithIndex)
import Data.Array as Array
import Data.Maybe (Maybe(..), isJust)
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls, emptyState)
import Lattice.UI.Components.EffectControlsPanel.Types
  ( State
  , Action(..)
  , Slots
  , EffectInstance
  , EffectParameter
  , EffectCategoryDef
  , EffectDef
  , layerIcon
  , effectCategories
  , effectsForCategoryKey
  )
import Lattice.UI.Components.EffectControlsPanel.Styles as S
import Lattice.UI.Components.EffectControlsPanel.RenderControls (renderParameterControl)

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // main render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-effect-controls" ]
    , HP.attr (HH.AttrName "style") S.panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-label") "Effect Controls"
    ]
    [ renderHeader state
    , renderContent state
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // header
-- ════════════════════════════════════════════════════════════════════════════

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "lattice-panel-header" ]
    , HP.attr (HH.AttrName "style") S.headerStyle
    ]
    [ HH.div
        [ cls [ "header-row" ]
        , HP.attr (HH.AttrName "style") S.headerRowStyle
        ]
        [ HH.h3 
            [ HP.attr (HH.AttrName "style") S.titleStyle ] 
            [ HH.text "Effect Controls" ]
        , case state.layer of
            Just layer ->
              HH.div
                [ cls [ "layer-badge" ]
                , HP.attr (HH.AttrName "style") S.layerBadgeStyle
                ]
                [ HH.span [ cls [ "layer-type-icon" ] ] 
                    [ HH.text (layerIcon layer.layerType) ]
                , HH.text layer.name
                ]
            Nothing -> HH.text ""
        ]
    , renderAddEffectButton state
    ]

renderAddEffectButton :: forall m. State -> H.ComponentHTML Action Slots m
renderAddEffectButton state =
  HH.div
    [ cls [ "add-effect-wrapper" ]
    , HP.attr (HH.AttrName "style") "position: relative;"
    ]
    [ HH.button
        [ cls [ "lattice-btn", "add-btn" ]
        , HP.attr (HH.AttrName "style") S.addButtonStyle
        , HP.disabled (not (isJust state.layer))
        , HE.onClick \_ -> ToggleAddMenu
        , HP.attr (HH.AttrName "aria-haspopup") "menu"
        , HP.attr (HH.AttrName "aria-expanded") (if state.showAddMenu then "true" else "false")
        ]
        [ HH.span [ cls [ "icon" ] ] [ HH.text "+" ]
        , HH.text " Add Effect"
        ]
    , if state.showAddMenu
        then renderEffectMenu state
        else HH.text ""
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // effect menu
-- ════════════════════════════════════════════════════════════════════════════

renderEffectMenu :: forall m. State -> H.ComponentHTML Action Slots m
renderEffectMenu state =
  HH.div
    [ cls [ "effect-menu" ]
    , HP.attr (HH.AttrName "style") S.effectMenuStyle
    , HP.attr (HH.AttrName "role") "menu"
    , HP.attr (HH.AttrName "aria-label") "Add effect"
    ]
    (map (renderEffectCategoryMenu state) effectCategories)

renderEffectCategoryMenu :: forall m. State -> EffectCategoryDef -> H.ComponentHTML Action Slots m
renderEffectCategoryMenu state cat =
  let
    isExpanded = Array.elem cat.key state.expandedCategories
    effects = effectsForCategoryKey cat.key
  in
    HH.div
      [ cls [ "effect-category" ]
      ]
      [ HH.div
          [ cls [ "category-label" ]
          , HP.attr (HH.AttrName "style") S.categoryLabelStyle
          , HE.onClick \_ -> ToggleEffectCategory cat.key
          , HP.attr (HH.AttrName "role") "menuitem"
          , HP.attr (HH.AttrName "aria-expanded") (if isExpanded then "true" else "false")
          ]
          [ HH.span [ cls [ "cat-icon" ] ] [ HH.text cat.icon ]
          , HH.text (" " <> cat.label)
          , HH.span [ cls [ "expand-arrow" ], HP.attr (HH.AttrName "style") "margin-left: auto;" ]
              [ HH.text (if isExpanded then "v" else ">") ]
          ]
      , if isExpanded
          then HH.div
                 [ cls [ "category-items" ]
                 , HP.attr (HH.AttrName "style") S.categoryItemsStyle
                 , HP.attr (HH.AttrName "role") "group"
                 ]
                 (map renderEffectMenuItem effects)
          else HH.text ""
      ]

renderEffectMenuItem :: forall m. EffectDef -> H.ComponentHTML Action Slots m
renderEffectMenuItem effect =
  HH.button
    [ cls [ "effect-menu-item" ]
    , HP.attr (HH.AttrName "style") S.effectMenuItemStyle
    , HP.attr (HH.AttrName "role") "menuitem"
    , HE.onClick \_ -> AddEffect effect.key
    ]
    [ HH.text effect.name ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // content
-- ════════════════════════════════════════════════════════════════════════════

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "lattice-panel-content" ]
    , HP.attr (HH.AttrName "style") S.contentStyle
    ]
    [ case state.layer of
        Nothing ->
          emptyState "No Layer Selected" "Select a layer to edit its effects"
        Just layer ->
          if length layer.effects == 0
            then emptyState "No Effects Applied" "Click 'Add Effect' to add effects to this layer"
            else HH.div
                   [ cls [ "effects-list" ]
                   , HP.attr (HH.AttrName "role") "list"
                   ]
                   (mapWithIndex (renderEffectItem state layer.id) layer.effects)
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // effect item
-- ════════════════════════════════════════════════════════════════════════════

renderEffectItem :: forall m. State -> String -> Int -> EffectInstance -> H.ComponentHTML Action Slots m
renderEffectItem state layerId index effect =
  let
    isDragOver = case state.dragState of
      Just ds -> ds.overIndex == Just index
      Nothing -> false
  in
    HH.div
      [ cls [ "effect-item" ]
      , HP.attr (HH.AttrName "style") (S.effectItemStyle effect.expanded isDragOver)
      , HP.attr (HH.AttrName "role") "listitem"
      , HP.attr (HH.AttrName "draggable") "true"
      , HE.onDragStart \_ -> StartDrag index
      , HE.onDragOver \_ -> DragOver index
      , HE.onDragEnd \_ -> DragEnd
      , HE.onDrop \_ -> Drop index
      ]
      [ renderEffectHeader effect
      , if effect.expanded
          then renderEffectParams state layerId effect
          else HH.text ""
      ]

renderEffectHeader :: forall m. EffectInstance -> H.ComponentHTML Action Slots m
renderEffectHeader effect =
  HH.div
    [ cls [ "effect-header" ]
    , HP.attr (HH.AttrName "style") S.effectHeaderStyle
    , HE.onClick \_ -> ToggleEffectExpanded effect.id
    ]
    [ HH.div 
        [ cls [ "header-left" ]
        , HP.attr (HH.AttrName "style") "display: flex; align-items: center; gap: 4px;"
        ]
        [ HH.span [ cls [ "arrow" ], HP.attr (HH.AttrName "style") S.arrowStyle ]
            [ HH.text (if effect.expanded then "v" else ">") ]
        , HH.button
            [ cls [ "icon-btn" ]
            , HP.attr (HH.AttrName "style") S.iconBtnStyle
            , HE.onClick \_ -> ToggleEffect effect.id
            , HP.attr (HH.AttrName "aria-label") (if effect.enabled then "Disable effect" else "Enable effect")
            , HP.attr (HH.AttrName "aria-pressed") (if effect.enabled then "true" else "false")
            ]
            [ HH.span 
                [ cls [ "fx-icon" ]
                , HP.attr (HH.AttrName "style") (S.fxIconStyle effect.enabled)
                ] 
                [ HH.text "fx" ]
            ]
        , HH.span [ cls [ "effect-name" ], HP.attr (HH.AttrName "style") S.effectNameStyle ]
            [ HH.text effect.name ]
        ]
    , HH.div [ cls [ "header-right" ] ]
        [ HH.button
            [ cls [ "icon-btn", "delete" ]
            , HP.attr (HH.AttrName "style") (S.iconBtnStyle <> " color: var(--lattice-danger);")
            , HP.attr (HH.AttrName "title") "Remove Effect"
            , HP.attr (HH.AttrName "aria-label") "Remove effect"
            , HE.onClick \_ -> RemoveEffect effect.id
            ]
            [ HH.text "x" ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // effect params
-- ════════════════════════════════════════════════════════════════════════════

renderEffectParams :: forall m. State -> String -> EffectInstance -> H.ComponentHTML Action Slots m
renderEffectParams state _layerId effect =
  HH.div
    [ cls [ "effect-params" ]
    , HP.attr (HH.AttrName "style") S.effectParamsStyle
    ]
    (map (renderParameter state effect.id) effect.parameters)

renderParameter :: forall m. State -> String -> Tuple String EffectParameter -> H.ComponentHTML Action Slots m
renderParameter state effectId (Tuple paramKey param) =
  HH.div
    [ cls [ "param-row" ]
    , HP.attr (HH.AttrName "style") S.paramRowStyle
    ]
    [ HH.div
        [ cls [ "param-header" ]
        , HP.attr (HH.AttrName "style") S.paramHeaderStyle
        ]
        [ HH.span 
            [ cls [ "param-name" ]
            , HP.attr (HH.AttrName "style") S.paramNameStyle
            , HP.attr (HH.AttrName "title") paramKey
            ] 
            [ HH.text param.name ]
        , HH.button
            [ cls [ "keyframe-toggle" ]
            , HP.attr (HH.AttrName "style") (S.keyframeToggleStyle param.animated)
            , HP.attr (HH.AttrName "aria-label") "Toggle animation"
            , HP.attr (HH.AttrName "aria-pressed") (if param.animated then "true" else "false")
            , HP.attr (HH.AttrName "title") "Toggle Animation"
            , HE.onClick \_ -> ToggleParameterAnimation effectId paramKey
            ]
            [ HH.text "<>" ]
        ]
    , HH.div [ cls [ "param-control" ] ]
        [ renderParameterControl state effectId paramKey param ]
    ]
