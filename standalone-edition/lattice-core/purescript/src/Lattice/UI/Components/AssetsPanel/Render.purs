-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Assets Panel Render Functions
-- |
-- | Core render functions for the asset management panel.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.AssetsPanel.Render
  ( render
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)

import Lattice.UI.Components.AssetsPanel.Types
  ( State
  , Action(..)
  , Slots
  , AssetTab(..)
  , allTabs
  , tabLabel
  , tabIcon
  , tabTooltip
  )
import Lattice.UI.Components.AssetsPanel.Styles as S
import Lattice.UI.Components.AssetsPanel.RenderTabs
  ( renderMaterialsTab
  , renderSvgTab
  , renderMeshesTab
  , renderSpritesTab
  , renderEnvironmentTab
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-assets-panel" ]
    , HP.attr (HH.AttrName "style") S.panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "Asset Manager"
    ]
    [ renderTabs state
    , renderContent state
    , renderLoadingOverlay state
    , renderErrorToast state
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // tabs
-- ════════════════════════════════════════════════════════════════════════════

renderTabs :: forall m. State -> H.ComponentHTML Action Slots m
renderTabs state =
  HH.div
    [ cls [ "asset-tabs" ]
    , HP.attr (HH.AttrName "style") S.tabsStyle
    , HP.attr (HH.AttrName "role") "tablist"
    , ARIA.label "Asset type tabs"
    , HP.attr (HH.AttrName "aria-orientation") "horizontal"
    ]
    (Array.mapWithIndex (renderTabButton state) allTabs)

renderTabButton :: forall m. State -> Int -> AssetTab -> H.ComponentHTML Action Slots m
renderTabButton state idx tab =
  let
    isSelected = tab == state.activeTab
    tabId = state.baseId <> "-tab-" <> show tab
    panelId = state.baseId <> "-panel-" <> show tab
  in
  HH.button
    [ cls [ "asset-tab" ]
    , HP.type_ HP.ButtonButton
    , HP.id tabId
    , HP.tabIndex (if isSelected then 0 else (-1))
    , HP.attr (HH.AttrName "style") (S.tabButtonStyle isSelected)
    , HP.attr (HH.AttrName "title") (tabTooltip tab)
    , HP.attr (HH.AttrName "role") "tab"
    , ARIA.selected (show isSelected)
    , ARIA.controls panelId
    , HP.attr (HH.AttrName "data-state") (if isSelected then "active" else "inactive")
    , HE.onClick \_ -> SetActiveTab tab
    , HE.onKeyDown (HandleTabKeyDown idx)
    ]
    [ HH.span 
        [ cls [ "tab-icon" ]
        , HP.attr (HH.AttrName "style") S.tabIconStyle
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ] 
        [ HH.text (tabIcon tab) ]
    , HH.span 
        [ cls [ "tab-label" ]
        , HP.attr (HH.AttrName "style") S.tabLabelStyle
        ] 
        [ HH.text (tabLabel tab) ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // content
-- ════════════════════════════════════════════════════════════════════════════

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  let
    tabId = state.baseId <> "-tab-" <> show state.activeTab
    panelId = state.baseId <> "-panel-" <> show state.activeTab
  in
  HH.div
    [ cls [ "asset-content" ]
    , HP.id panelId
    , HP.attr (HH.AttrName "style") S.contentStyle
    , HP.attr (HH.AttrName "role") "tabpanel"
    , HP.tabIndex 0
    , ARIA.labelledBy tabId
    , HP.attr (HH.AttrName "data-state") "active"
    ]
    [ case state.activeTab of
        TabMaterials -> renderMaterialsTab state
        TabSvg -> renderSvgTab state
        TabMeshes -> renderMeshesTab state
        TabSprites -> renderSpritesTab state
        TabEnvironment -> renderEnvironmentTab state
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // overlays
-- ════════════════════════════════════════════════════════════════════════════

renderLoadingOverlay :: forall m. State -> H.ComponentHTML Action Slots m
renderLoadingOverlay state =
  if state.isLoading
    then
      HH.div
        [ cls [ "loading-overlay" ]
        , HP.attr (HH.AttrName "style") S.loadingOverlayStyle
        , HP.attr (HH.AttrName "role") "alert"
        , ARIA.busy "true"
        ]
        [ HH.div [ cls [ "spinner" ], HP.attr (HH.AttrName "style") S.spinnerStyle ] []
        , HH.span_ [ HH.text "Loading..." ]
        ]
    else HH.text ""

renderErrorToast :: forall m. State -> H.ComponentHTML Action Slots m
renderErrorToast state =
  case state.lastError of
    Nothing -> HH.text ""
    Just err ->
      HH.div
        [ cls [ "error-toast" ]
        , HP.attr (HH.AttrName "style") S.errorToastStyle
        , HP.attr (HH.AttrName "role") "alert"
        , HE.onClick \_ -> ClearError
        ]
        [ HH.text err ]
