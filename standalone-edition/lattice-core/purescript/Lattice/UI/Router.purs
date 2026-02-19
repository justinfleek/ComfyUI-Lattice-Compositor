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

import Effect (Effect)

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
foreign import getPathname :: Effect String

-- | Push a new state onto the history stack
foreign import pushState :: String -> Effect Unit

-- | Replace the current history state
foreign import replaceState :: String -> Effect Unit

-- | Subscribe to popstate events (browser back/forward)
foreign import onPopState :: (String -> Effect Unit) -> Effect Unit
