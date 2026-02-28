-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // hydrogen // ssg
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Static Site Generation utilities
-- |
-- | This module provides utilities for building static sites with Halogen:
-- | - HTML document generation
-- | - Meta tag helpers (SEO, OpenGraph, Twitter)
-- | - Page shell generation
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.SSG as SSG
-- | import Halogen.HTML.Renderer as Renderer
-- |
-- | myPage :: PageMeta
-- | myPage =
-- |   { title: "My Page"
-- |   , description: "A great page"
-- |   , path: "/my-page"
-- |   , ogImage: Nothing
-- |   }
-- |
-- | html :: String
-- | html = SSG.renderPage defaultDocConfig myPage pageContent
-- | ```
module Hydrogen.SSG
  ( -- * Document configuration
    DocConfig
  , defaultDocConfig
    -- * Page metadata
  , PageMeta
    -- * Rendering
  , renderPage
  , renderDocument
    -- * Route integration
  , pageMetaFromRoute
  , renderRouteStatic
    -- * Meta tags
  , metaTags
  , ogTags
  , twitterTags
  ) where

import Prelude
  ( map
  , ($)
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.HTML.Renderer as Renderer
import Hydrogen.Router (class IsRoute, class RouteMetadata, routeToPath, routeTitle, routeDescription, routeOgImage)

-- ============================================================
-- DOCUMENT CONFIGURATION
-- ============================================================

-- | Configuration for the HTML document
type DocConfig =
  { lang :: String              -- ^ HTML lang attribute
  , charset :: String           -- ^ Character encoding
  , viewport :: String          -- ^ Viewport meta content
  , siteName :: String          -- ^ Site name for OG tags
  , themeColor :: Maybe String  -- ^ Theme color for mobile browsers
  , manifest :: Maybe String    -- ^ Web app manifest URL
  , favicon :: Maybe String     -- ^ Favicon URL
  , stylesheets :: Array String -- ^ CSS file URLs
  , scripts :: Array String     -- ^ JavaScript file URLs (loaded at end of body)
  }

-- | Default document configuration
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

-- ============================================================
-- PAGE METADATA
-- ============================================================

-- | Metadata for a single page
type PageMeta =
  { title :: String             -- ^ Page title
  , description :: String       -- ^ Meta description
  , path :: String              -- ^ URL path
  , ogImage :: Maybe String     -- ^ OpenGraph image URL
  , canonicalUrl :: Maybe String -- ^ Canonical URL (if different from path)
  }

-- ============================================================
-- RENDERING
-- ============================================================

-- | Render a complete HTML page
-- |
-- | Combines document config, page meta, and body content into
-- | a complete HTML document string.
renderPage :: forall w i. DocConfig -> PageMeta -> HH.HTML w i -> String
renderPage config meta content =
  "<!DOCTYPE html>" <> renderDocument config meta content

-- | Render the HTML document (without DOCTYPE)
renderDocument :: forall w i. DocConfig -> PageMeta -> HH.HTML w i -> String
renderDocument config meta content =
  Renderer.render $ HH.html
    [ HP.attr (HH.AttrName "lang") config.lang ]
    [ HH.head_
        ( [ HH.meta [ HP.attr (HH.AttrName "charset") config.charset ]
          , HH.meta 
              [ HP.attr (HH.AttrName "name") "viewport"
              , HP.attr (HH.AttrName "content") config.viewport 
              ]
          , HH.title_ [ HH.text meta.title ]
          , HH.meta 
              [ HP.attr (HH.AttrName "name") "description"
              , HP.attr (HH.AttrName "content") meta.description 
              ]
          ]
          <> metaTags config meta
          <> ogTags config meta
          <> twitterTags meta
          <> stylesheetLinks config
          <> faviconLink config
          <> manifestLink config
          <> themeColorMeta config
        )
    , HH.body_
        ( [ content ] <> scriptTags config )
    ]

-- ============================================================
-- META TAGS
-- ============================================================

-- | Generate standard meta tags
metaTags :: forall w i. DocConfig -> PageMeta -> Array (HH.HTML w i)
metaTags _config meta =
  case meta.canonicalUrl of
    Just url -> [ HH.link [ HP.rel "canonical", HP.href url ] ]
    Nothing -> []

-- | Generate OpenGraph meta tags
ogTags :: forall w i. DocConfig -> PageMeta -> Array (HH.HTML w i)
ogTags config meta =
  [ ogMeta "og:type" "website"
  , ogMeta "og:title" meta.title
  , ogMeta "og:description" meta.description
  , ogMeta "og:url" meta.path
  ]
  <> siteName
  <> image
  where
  siteName = case config.siteName of
    "" -> []
    name -> [ ogMeta "og:site_name" name ]
  image = case meta.ogImage of
    Just url -> [ ogMeta "og:image" url ]
    Nothing -> []

-- | Generate Twitter Card meta tags
twitterTags :: forall w i. PageMeta -> Array (HH.HTML w i)
twitterTags meta =
  [ twitterMeta "twitter:card" "summary_large_image"
  , twitterMeta "twitter:title" meta.title
  , twitterMeta "twitter:description" meta.description
  ]
  <> image
  where
  image = case meta.ogImage of
    Just url -> [ twitterMeta "twitter:image" url ]
    Nothing -> []

-- ============================================================
-- HELPERS
-- ============================================================

ogMeta :: forall w i. String -> String -> HH.HTML w i
ogMeta property contentVal =
  HH.meta 
    [ HP.attr (HH.AttrName "property") property
    , HP.attr (HH.AttrName "content") contentVal 
    ]

twitterMeta :: forall w i. String -> String -> HH.HTML w i
twitterMeta name contentVal =
  HH.meta 
    [ HP.attr (HH.AttrName "name") name
    , HP.attr (HH.AttrName "content") contentVal 
    ]

stylesheetLinks :: forall w i. DocConfig -> Array (HH.HTML w i)
stylesheetLinks config =
  map (\href -> HH.link [ HP.rel "stylesheet", HP.href href ]) config.stylesheets

scriptTags :: forall w i. DocConfig -> Array (HH.HTML w i)
scriptTags config =
  map (\src -> HH.script [ HP.src src ] []) config.scripts

faviconLink :: forall w i. DocConfig -> Array (HH.HTML w i)
faviconLink config = case config.favicon of
  Just href -> [ HH.link [ HP.rel "icon", HP.href href ] ]
  Nothing -> []

manifestLink :: forall w i. DocConfig -> Array (HH.HTML w i)
manifestLink config = case config.manifest of
  Just href -> [ HH.link [ HP.rel "manifest", HP.href href ] ]
  Nothing -> []

themeColorMeta :: forall w i. DocConfig -> Array (HH.HTML w i)
themeColorMeta config = case config.themeColor of
  Just color -> 
    [ HH.meta 
        [ HP.attr (HH.AttrName "name") "theme-color"
        , HP.attr (HH.AttrName "content") color 
        ]
    ]
  Nothing -> []

-- ============================================================
-- ROUTE INTEGRATION
-- ============================================================

-- | Generate PageMeta from a route using the RouteMetadata typeclass
-- |
-- | This is the key to the "write once, SSG or dynamic" pattern:
-- | define your route metadata once in the typeclass, then use it
-- | for both static generation and runtime rendering.
-- |
-- | ```purescript
-- | import Hydrogen.SSG as SSG
-- | import MyApp.Router (Route(..), homeRoute)
-- |
-- | -- Generate static page
-- | homeMeta :: PageMeta
-- | homeMeta = pageMetaFromRoute homeRoute
-- |
-- | html :: String
-- | html = SSG.renderPage docConfig homeMeta content
-- | ```
pageMetaFromRoute :: forall route. IsRoute route => RouteMetadata route => route -> PageMeta
pageMetaFromRoute route =
  { title: routeTitle route
  , description: routeDescription route
  , path: routeToPath route
  , ogImage: routeOgImage route
  , canonicalUrl: Nothing
  }

-- | Render a route to a complete HTML page
-- |
-- | Combines pageMetaFromRoute with renderPage for a one-liner:
-- |
-- | ```purescript
-- | html :: String
-- | html = renderRouteStatic docConfig homeRoute homeContent
-- | ```
renderRouteStatic 
  :: forall route w i
   . IsRoute route 
  => RouteMetadata route 
  => DocConfig 
  -> route 
  -> HH.HTML w i 
  -> String
renderRouteStatic config route content =
  renderPage config (pageMetaFromRoute route) content
