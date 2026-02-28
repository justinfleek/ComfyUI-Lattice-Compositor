-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // router
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Client-side routing infrastructure
-- |
-- | This module provides a typeclass-based routing system that allows
-- | applications to define their own route ADTs while using shared
-- | routing infrastructure.
-- |
-- | ## Usage
-- |
-- | 1. Define your route type:
-- | ```purescript
-- | data Route = Home | About | Dashboard | NotFound
-- | ```
-- |
-- | 2. Implement the Route class:
-- | ```purescript
-- | instance routeMyRoute :: Route Route where
-- |   parseRoute "/" = Home
-- |   parseRoute "/about" = About
-- |   parseRoute "/dashboard" = Dashboard
-- |   parseRoute _ = NotFound
-- |   
-- |   routeToPath Home = "/"
-- |   routeToPath About = "/about"
-- |   routeToPath Dashboard = "/dashboard"
-- |   routeToPath NotFound = "/"
-- | ```
-- |
-- | 3. Use the routing helpers:
-- | ```purescript
-- | handleAction Initialize = do
-- |   path <- liftEffect getPathname
-- |   let route = parseRoute path
-- |   ...
-- | ```
module Hydrogen.Router
  ( -- * Route typeclass
    class IsRoute
  , parseRoute
  , routeToPath
    -- * Route metadata
  , class RouteMetadata
  , isProtected
  , isStaticRoute
  , routeTitle
  , routeDescription
  , routeOgImage
    -- * Browser integration (FFI)
  , getPathname
  , getHostname
  , getOrigin
  , pushState
  , replaceState
  , onPopState
  , interceptLinks
    -- * Utilities
  , navigate
  , normalizeTrailingSlash
  ) where

import Prelude
  ( class Eq
  , Unit
  , (==)
  )

import Data.Maybe (Maybe)
import Data.String.CodeUnits as SCU
import Effect (Effect)

-- ============================================================
-- ROUTE TYPECLASS
-- ============================================================

-- | Typeclass for route types that can be parsed from and serialized to paths
-- |
-- | Laws:
-- | - `parseRoute (routeToPath r) == r` for all valid routes
-- | - `routeToPath` should produce paths starting with "/"
class IsRoute route where
  -- | Parse a URL path into a route
  parseRoute :: String -> route
  
  -- | Convert a route back to a URL path
  routeToPath :: route -> String

-- | Optional metadata for routes
-- |
-- | Implement this typeclass if your routes have protection or SSG semantics.
-- | This enables the "write once, SSG or dynamic" pattern where route metadata
-- | is defined once and used for both static generation and runtime rendering.
class RouteMetadata route where
  -- | Whether the route requires authentication
  isProtected :: route -> Boolean
  
  -- | Whether the route should be statically generated (SSG)
  -- | Returns true for public pages, false for SPA-only routes
  isStaticRoute :: route -> Boolean
  
  -- | Page title for the route (used in <title> and og:title)
  routeTitle :: route -> String
  
  -- | Meta description for the route (used in description and og:description)
  routeDescription :: route -> String
  
  -- | Optional OpenGraph image URL for the route
  routeOgImage :: route -> Maybe String

-- ============================================================
-- UTILITIES
-- ============================================================

-- | Normalize paths by removing trailing slashes (except for root)
-- |
-- | ```purescript
-- | normalizeTrailingSlash "/" == "/"
-- | normalizeTrailingSlash "/about/" == "/about"
-- | normalizeTrailingSlash "/about" == "/about"
-- | ```
normalizeTrailingSlash :: String -> String
normalizeTrailingSlash "/" = "/"
normalizeTrailingSlash path =
  if SCU.takeRight 1 path == "/" 
    then SCU.dropRight 1 path
    else path

-- | Navigate to a route programmatically
-- |
-- | This pushes the new path to browser history and can trigger
-- | your app's routing logic.
navigate :: forall route. IsRoute route => route -> Effect Unit
navigate route = pushState (routeToPath route)

-- ============================================================
-- BROWSER INTEGRATION (FFI)
-- ============================================================

-- | Get the current pathname from the browser location
foreign import getPathname :: Effect String

-- | Get the current hostname
foreign import getHostname :: Effect String

-- | Get the current origin (protocol + hostname + port)
foreign import getOrigin :: Effect String

-- | Push a new path to browser history
-- | This changes the URL without triggering a page reload
foreign import pushState :: String -> Effect Unit

-- | Replace the current history entry
-- | Useful for redirects that shouldn't be in browser history
foreign import replaceState :: String -> Effect Unit

-- | Subscribe to browser back/forward navigation events
-- | The callback receives the new pathname
foreign import onPopState :: (String -> Effect Unit) -> Effect Unit

-- | Intercept link clicks for SPA navigation
-- | Calls the callback with the href instead of navigating
-- | Only intercepts internal links (same origin, not target="_blank")
foreign import interceptLinks :: (String -> Effect Unit) -> Effect Unit
