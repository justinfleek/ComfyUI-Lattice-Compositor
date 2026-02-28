# Hydrogen.Router

Type-safe client-side routing with custom route ADTs.

## Overview

```purescript
import Hydrogen.Router (class IsRoute, class RouteMetadata, parseRoute, navigate)

-- Define routes as an ADT
data Route = Home | About | User String | Settings

-- Implement IsRoute for parsing/serialization
instance IsRoute Route where
  parseRoute = case _ of
    "/" -> Home
    "/about" -> About
    "/settings" -> Settings
    path | Just id <- stripPrefix "/user/" path -> User id
    _ -> Home
  
  routeToPath = case _ of
    Home -> "/"
    About -> "/about"
    User id -> "/user/" <> id
    Settings -> "/settings"

-- Optional: Metadata for SSG and auth
instance RouteMetadata Route where
  isProtected Settings = true
  isProtected _ = false
  
  isStaticRoute Home = true
  isStaticRoute About = true
  isStaticRoute _ = false
  
  routeTitle Home = "My App"
  routeTitle About = "About - My App"
  routeTitle (User _) = "User Profile"
  routeTitle Settings = "Settings"
  
  routeDescription = routeTitle  -- Simplified
  
  routeOgImage _ = Nothing
```

## Typeclasses

### IsRoute

```purescript
class IsRoute route where
  parseRoute :: String -> route
  routeToPath :: route -> String
```

Every route type must implement bidirectional conversion to URL paths.

### RouteMetadata

```purescript
class RouteMetadata route where
  isProtected :: route -> Boolean      -- Requires auth?
  isStaticRoute :: route -> Boolean    -- Can be pre-rendered?
  routeTitle :: route -> String        -- Page title
  routeDescription :: route -> String  -- Meta description
  routeOgImage :: route -> Maybe String -- OpenGraph image
```

Metadata is used by:
- **SSG**: Generate correct `<title>`, meta tags
- **Auth**: Redirect to login for protected routes
- **SEO**: OpenGraph/Twitter cards

## Navigation

### Programmatic

```purescript
-- Navigate (pushState)
navigate Settings

-- Replace current history entry
replaceState Settings

-- Get current path
path <- getPathname
let route = parseRoute path
```

### Link Interception

For SPA navigation without full page reloads:

```purescript
-- In your app init
interceptLinks \path -> do
  let route = parseRoute path
  handleRouteChange route
```

This intercepts clicks on `<a href="...">` and calls your handler instead.

### PopState (Back/Forward)

```purescript
onPopState \path -> do
  let route = parseRoute path
  handleRouteChange route
```

## URL Utilities

```purescript
getPathname :: Effect String   -- "/user/123"
getHostname :: Effect String   -- "example.com"
getOrigin :: Effect String     -- "https://example.com"

normalizeTrailingSlash :: String -> String
-- "/about/" -> "/about"
-- "/" -> "/"
```

## Integration with SSG

See [SSG Guide](ssg.md) for using route metadata in static generation:

```purescript
-- Route metadata flows directly to page generation
html = renderRouteStatic docConfig route content
-- Uses routeTitle, routeDescription, routeOgImage automatically
```
