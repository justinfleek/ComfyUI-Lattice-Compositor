# Hydrogen.SSG

Static site generation with route integration.

## Overview

```purescript
import Hydrogen.SSG (renderPage, renderRouteStatic, defaultDocConfig)

-- Configure document
docConfig :: DocConfig
docConfig = defaultDocConfig
  { siteName = "My App"
  , stylesheets = ["/styles.css"]
  , scripts = ["/main.js"]
  }

-- Generate page from route (uses RouteMetadata!)
html :: String
html = renderRouteStatic docConfig Home homeContent
```

## Document Configuration

```purescript
type DocConfig =
  { lang :: String              -- "en"
  , charset :: String           -- "utf-8"
  , viewport :: String          -- "width=device-width, initial-scale=1"
  , siteName :: String          -- For og:site_name
  , themeColor :: Maybe String  -- Mobile browser chrome color
  , manifest :: Maybe String    -- PWA manifest URL
  , favicon :: Maybe String     -- Favicon URL
  , stylesheets :: Array String -- CSS file URLs
  , scripts :: Array String     -- JS file URLs (loaded at end of body)
  }

defaultDocConfig :: DocConfig
defaultDocConfig =
  { lang: "en"
  , charset: "utf-8"
  , viewport: "width=device-width, initial-scale=1"
  , siteName: ""
  , themeColor: Nothing
  , favicon: Nothing
  , manifest: Nothing
  , stylesheets: []
  , scripts: []
  }
```

## Page Metadata

```purescript
type PageMeta =
  { title :: String
  , description :: String
  , path :: String
  , ogImage :: Maybe String
  , canonicalUrl :: Maybe String
  }
```

## Rendering

### From Route (Recommended)

If your route implements `RouteMetadata`, use `renderRouteStatic`:

```purescript
html = renderRouteStatic docConfig myRoute content
```

This automatically extracts title, description, ogImage from the route.

### Manual PageMeta

```purescript
html = renderPage docConfig
  { title: "My Page"
  , description: "Description for SEO"
  , path: "/my-page"
  , ogImage: Just "https://example.com/og.png"
  , canonicalUrl: Nothing
  }
  content
```

## Generated HTML

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width, initial-scale=1"/>
  <title>My Page</title>
  <meta name="description" content="Description for SEO"/>
  
  <!-- OpenGraph -->
  <meta property="og:type" content="website"/>
  <meta property="og:title" content="My Page"/>
  <meta property="og:description" content="Description for SEO"/>
  <meta property="og:url" content="/my-page"/>
  <meta property="og:image" content="https://example.com/og.png"/>
  
  <!-- Twitter Card -->
  <meta name="twitter:card" content="summary_large_image"/>
  <meta name="twitter:title" content="My Page"/>
  <meta name="twitter:description" content="Description for SEO"/>
  <meta name="twitter:image" content="https://example.com/og.png"/>
  
  <link rel="stylesheet" href="/styles.css"/>
</head>
<body>
  <!-- Your content here -->
  <script src="/main.js"></script>
</body>
</html>
```

## "Write Once, Render Anywhere"

Define metadata once in `RouteMetadata`, use everywhere:

```purescript
-- RouteMetadata instance (single source of truth)
instance RouteMetadata Route where
  routeTitle Home = "My App - Home"
  routeTitle (Post id) = "Post " <> id
  routeDescription Home = "Welcome to my app"
  -- ...

-- SSG build script
generateSite :: Effect Unit
generateSite = for_ allRoutes \route -> do
  let html = renderRouteStatic docConfig route (renderRoute route)
  let path = routeToPath route <> "/index.html"
  writeTextFile path html

-- Runtime (same metadata!)
render state = HH.div_
  [ HH.title_ [ HH.text (routeTitle state.route) ]
  , -- ...
  ]
```

## Meta Tag Helpers

For custom meta tag needs:

```purescript
metaTags :: DocConfig -> PageMeta -> Array (HTML w i)
ogTags :: DocConfig -> PageMeta -> Array (HTML w i)
twitterTags :: PageMeta -> Array (HTML w i)
```
