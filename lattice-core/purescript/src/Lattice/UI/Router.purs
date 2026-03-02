-- | Lattice Compositor Router
-- |
-- | Client-side routing for the Standalone Edition.
-- | Routes map to major views/workspaces in the compositor.
module Lattice.UI.Router
  ( Route(..)
  , parseRoute
  , routeToPath
  , getPathname
  , pushState
  , replaceState
  , onPopState
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Foreign (unsafeToForeign)
import Web.Event.Event (Event, EventType(..))
import Web.Event.EventTarget (addEventListener, eventListener)
import Web.HTML as HTML
import Web.HTML.History (DocumentTitle(..), URL(..))
import Web.HTML.History as History
import Web.HTML.Location as Location
import Web.HTML.Window as Window

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                    // routes
-- ════════════════════════════════════════════════════════════════════════════

-- | Main application routes
data Route
  = Workspace          -- Main compositor workspace
  | Project            -- Project browser / settings
  | Assets             -- Asset library
  | Export             -- Export / render queue
  | Settings           -- Application settings
  | NotFound String    -- 404 with original path

derive instance eqRoute :: Eq Route

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // route // parsing
-- ════════════════════════════════════════════════════════════════════════════

-- | Parse a URL path into a Route
parseRoute :: String -> Route
parseRoute path = case path of
  "/" -> Workspace
  "/workspace" -> Workspace
  "/workspace/" -> Workspace
  "/project" -> Project
  "/project/" -> Project
  "/assets" -> Assets
  "/assets/" -> Assets
  "/export" -> Export
  "/export/" -> Export
  "/render" -> Export
  "/render/" -> Export
  "/settings" -> Settings
  "/settings/" -> Settings
  "/preferences" -> Settings
  "/preferences/" -> Settings
  _ -> NotFound path

-- | Convert a Route to a URL path
routeToPath :: Route -> String
routeToPath = case _ of
  Workspace -> "/"
  Project -> "/project"
  Assets -> "/assets"
  Export -> "/export"
  Settings -> "/settings"
  NotFound _ -> "/"

-- ════════════════════════════════════════════════════════════════════════════
--                                                 // browser // history // api
-- ════════════════════════════════════════════════════════════════════════════

-- | Get the current pathname
getPathname :: Effect String
getPathname = do
  win <- HTML.window
  loc <- Window.location win
  Location.pathname loc

-- | Push a new state onto the history stack
pushState :: String -> Effect Unit
pushState path = do
  win <- HTML.window
  hist <- Window.history win
  -- pushState takes: state (Foreign), title (DocumentTitle), url (URL), history
  History.pushState (unsafeToForeign {}) (DocumentTitle "") (URL path) hist

-- | Replace the current history state
replaceState :: String -> Effect Unit
replaceState path = do
  win <- HTML.window
  hist <- Window.history win
  -- replaceState takes: state (Foreign), title (DocumentTitle), url (URL), history
  History.replaceState (unsafeToForeign {}) (DocumentTitle "") (URL path) hist

-- | Subscribe to popstate events (browser back/forward)
onPopState :: (String -> Effect Unit) -> Effect Unit
onPopState callback = do
  win <- HTML.window
  listener <- eventListener handlePopState
  addEventListener (EventType "popstate") listener false (Window.toEventTarget win)
  where
    handlePopState :: Event -> Effect Unit
    handlePopState _ = do
      path <- getPathname
      callback path
