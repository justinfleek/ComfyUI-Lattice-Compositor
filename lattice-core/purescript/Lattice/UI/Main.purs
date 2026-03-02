-- | Lattice Compositor UI Entry Point
-- |
-- | Main entry point for the Standalone Edition PureScript/Halogen UI.
-- | This initializes the application, sets up routing, and renders
-- | the appropriate page components.
-- |
-- | All routes are fully implemented:
-- | - Workspace: Main compositor workspace
-- | - Project: Project browser and composition management
-- | - Assets: Asset library with categories and import
-- | - Export: Render queue and export settings
-- | - Settings: Theme selection and about info
-- | - NotFound: 404 page
module Lattice.UI.Main where

import Prelude

import Data.Const (Const)
import Data.Maybe (Maybe(..))
import Type.Proxy (Proxy(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.Aff as HA
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.Subscription as HS
import Halogen.VDom.Driver (runUI)
import Web.DOM.ParentNode (QuerySelector(..), querySelector)
import Web.HTML (window)
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window (document)
import Web.Event.Event (preventDefault)
import Web.UIEvent.MouseEvent (MouseEvent, toEvent)

import Lattice.UI.Core (cls)
import Lattice.UI.Router (Route(..), parseRoute, routeToPath, pushState, getPathname, onPopState)
import Lattice.UI.Layout.WorkspaceLayout as WorkspaceLayout
import Lattice.UI.Pages.Project as Project
import Lattice.UI.Pages.Assets as Assets
import Lattice.UI.Pages.Export as Export
import Lattice.UI.Pages.Settings as Settings

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // main // entry // point
-- ════════════════════════════════════════════════════════════════════════════

-- | Main entry point - call this from index.html
main :: Effect Unit
main = launchAff_ do
  HA.awaitLoad
  doc <- liftEffect $ window >>= document
  let parent = HTMLDocument.toParentNode doc
  mbContainer <- liftEffect $ querySelector (QuerySelector "#lattice-app") parent
  case mbContainer >>= HTMLElement.fromElement of
    Nothing -> pure unit
    Just container -> void $ runUI appComponent unit container

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // app // component
-- ════════════════════════════════════════════════════════════════════════════

type AppState = 
  { route :: Route
  }

data AppAction
  = Initialize
  | Navigate Route MouseEvent
  | NavigateTo Route
  | RouteChanged String

type AppSlots =
  ( workspace :: H.Slot (Const Void) Void Unit
  , project :: H.Slot (Const Void) Void Unit
  , assets :: H.Slot (Const Void) Void Unit
  , export :: H.Slot (Const Void) Void Unit
  , settings :: H.Slot (Const Void) Void Unit
  )

_workspace :: Proxy "workspace"
_workspace = Proxy

_project :: Proxy "project"
_project = Proxy

_assets :: Proxy "assets"
_assets = Proxy

_export :: Proxy "export"
_export = Proxy

_settings :: Proxy "settings"
_settings = Proxy

-- | Main application component
appComponent :: forall q i o m. MonadAff m => H.Component q i o m
appComponent = H.mkComponent
  { initialState: const { route: Workspace }
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- | Handle application actions
handleAction :: forall o m. MonadAff m => AppAction -> H.HalogenM AppState AppAction AppSlots o m Unit
handleAction = case _ of
  Initialize -> do
    -- Get initial route from URL
    path <- liftEffect getPathname
    H.modify_ _ { route = parseRoute path }
    
    -- Subscribe to browser history changes
    { emitter, listener } <- liftEffect HS.create
    liftEffect $ onPopState (\p -> HS.notify listener (RouteChanged p))
    void $ H.subscribe emitter
  
  Navigate route event -> do
    liftEffect $ preventDefault (toEvent event)
    liftEffect $ pushState $ routeToPath route
    H.modify_ _ { route = route }
  
  NavigateTo route -> do
    liftEffect $ pushState $ routeToPath route
    H.modify_ _ { route = route }
  
  RouteChanged path -> do
    H.modify_ _ { route = parseRoute path }

-- | Render the application
render :: forall m. MonadAff m => AppState -> H.ComponentHTML AppAction AppSlots m
render state =
  HH.div
    [ cls [ "lattice-app" ]
    , HP.id "lattice-root"
    ]
    [ renderPage state.route
    ]

-- | Render the current page based on route
renderPage :: forall m. MonadAff m => Route -> H.ComponentHTML AppAction AppSlots m
renderPage = case _ of
  Workspace -> 
    HH.slot_ _workspace unit WorkspaceLayout.component unit
  
  Project ->
    HH.slot_ _project unit Project.component unit
  
  Assets ->
    HH.slot_ _assets unit Assets.component unit
  
  Export ->
    HH.slot_ _export unit Export.component unit
  
  Settings ->
    HH.slot_ _settings unit Settings.component unit
  
  NotFound path ->
    renderNotFoundPage path

-- | Render a 404 page for unknown routes
renderNotFoundPage :: forall m. MonadAff m => String -> H.ComponentHTML AppAction AppSlots m
renderNotFoundPage path =
  HH.div 
    [ cls [ "lattice-page", "lattice-not-found" ]
    , HP.attr (HH.AttrName "style") notFoundStyle
    ]
    [ HH.div [ cls [ "lattice-not-found-content" ] ]
        [ HH.div 
            [ cls [ "lattice-not-found-icon" ]
            , HP.attr (HH.AttrName "style") iconStyle
            ]
            [ HH.text "404" ]
        , HH.h1 
            [ HP.attr (HH.AttrName "style") headingStyle ]
            [ HH.text "Page Not Found" ]
        , HH.p 
            [ HP.attr (HH.AttrName "style") descStyle ]
            [ HH.text $ "The path '" <> path <> "' does not exist." ]
        , HH.button
            [ cls [ "lattice-btn", "lattice-btn-primary" ]
            , HP.attr (HH.AttrName "style") buttonStyle
            , HE.onClick \_ -> NavigateTo Workspace
            ]
            [ HH.text "Go to Workspace" ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                              // styles // for // 404 // page
-- ════════════════════════════════════════════════════════════════════════════

notFoundStyle :: String
notFoundStyle =
  "display: flex; align-items: center; justify-content: center; " <>
  "min-height: 100vh; background: var(--lattice-void); " <>
  "text-align: center; padding: var(--lattice-space-8);"

iconStyle :: String
iconStyle =
  "font-size: 64px; margin-bottom: var(--lattice-space-4); " <>
  "color: var(--lattice-text-muted); font-weight: var(--lattice-font-bold);"

headingStyle :: String
headingStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-2xl); " <>
  "font-weight: var(--lattice-font-semibold); margin: 0 0 var(--lattice-space-2);"

descStyle :: String
descStyle =
  "color: var(--lattice-text-secondary); font-size: var(--lattice-text-base); " <>
  "margin: 0 0 var(--lattice-space-6);"

buttonStyle :: String
buttonStyle =
  "min-width: 200px;"
