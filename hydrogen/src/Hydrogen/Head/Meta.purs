-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // hydrogen // meta
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dynamic document head management
-- |
-- | Manage title, meta tags, links, and structured data.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Head.Meta as Meta
-- |
-- | -- Set page title
-- | Meta.setTitle "My Page - My App"
-- |
-- | -- Update meta tags
-- | Meta.setMeta "description" "Page description here"
-- | Meta.setMeta "og:title" "Share Title"
-- |
-- | -- Add structured data (JSON-LD)
-- | Meta.setJsonLd
-- |   { "@context": "https://schema.org"
-- |   , "@type": "Article"
-- |   , "headline": "Article Title"
-- |   }
-- |
-- | -- Preload resources
-- | Meta.preload "/api/data" "fetch"
-- | Meta.prefetch "/next-page"
-- | ```
module Hydrogen.Head.Meta
  ( -- * Title
    setTitle
  , getTitle
    -- * Meta Tags
  , setMeta
  , removeMeta
  , getMeta
    -- * Open Graph
  , setOgTags
  , OgTags
    -- * Twitter Cards
  , setTwitterCard
  , TwitterCard
    -- * Structured Data
  , setJsonLd
  , removeJsonLd
    -- * Resource Hints
  , preload
  , prefetch
  , preconnect
  , dnsPrefetch
    -- * Canonical & Links
  , setCanonical
  , addLink
  , removeLink
    -- * Favicon
  , setFavicon
  ) where

import Prelude

import Data.Argonaut (class EncodeJson, encodeJson, stringify)
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Open Graph tags
type OgTags =
  { title :: String
  , description :: String
  , image :: Maybe String
  , url :: Maybe String
  , type_ :: Maybe String
  , siteName :: Maybe String
  }

-- | Twitter Card
type TwitterCard =
  { card :: String  -- "summary", "summary_large_image", "app", "player"
  , title :: String
  , description :: String
  , image :: Maybe String
  , site :: Maybe String
  , creator :: Maybe String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import setTitleImpl :: String -> Effect Unit
foreign import getTitleImpl :: Effect String
foreign import setMetaImpl :: String -> String -> Effect Unit
foreign import removeMetaImpl :: String -> Effect Unit
foreign import getMetaImpl :: String -> Effect (Maybe String)
foreign import setJsonLdImpl :: String -> Effect Unit
foreign import removeJsonLdImpl :: Effect Unit
foreign import addLinkImpl :: String -> String -> String -> Effect Unit
foreign import removeLinkImpl :: String -> Effect Unit
foreign import setFaviconImpl :: String -> Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // title
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set document title
setTitle :: String -> Effect Unit
setTitle = setTitleImpl

-- | Get current document title
getTitle :: Effect String
getTitle = getTitleImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // meta tags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set a meta tag (creates or updates)
setMeta :: String -> String -> Effect Unit
setMeta = setMetaImpl

-- | Remove a meta tag
removeMeta :: String -> Effect Unit
removeMeta = removeMetaImpl

-- | Get meta tag value
getMeta :: String -> Effect (Maybe String)
getMeta = getMetaImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // open graph
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set Open Graph tags
setOgTags :: OgTags -> Effect Unit
setOgTags tags = do
  setMeta "og:title" tags.title
  setMeta "og:description" tags.description
  case tags.image of
    Just img -> setMeta "og:image" img
    Nothing -> pure unit
  case tags.url of
    Just url -> setMeta "og:url" url
    Nothing -> pure unit
  case tags.type_ of
    Just t -> setMeta "og:type" t
    Nothing -> pure unit
  case tags.siteName of
    Just name -> setMeta "og:site_name" name
    Nothing -> pure unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // twitter cards
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set Twitter Card tags
setTwitterCard :: TwitterCard -> Effect Unit
setTwitterCard card = do
  setMeta "twitter:card" card.card
  setMeta "twitter:title" card.title
  setMeta "twitter:description" card.description
  case card.image of
    Just img -> setMeta "twitter:image" img
    Nothing -> pure unit
  case card.site of
    Just site -> setMeta "twitter:site" site
    Nothing -> pure unit
  case card.creator of
    Just creator -> setMeta "twitter:creator" creator
    Nothing -> pure unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // structured data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set JSON-LD structured data
setJsonLd :: forall a. EncodeJson a => a -> Effect Unit
setJsonLd data' = setJsonLdImpl (stringify $ encodeJson data')

-- | Remove JSON-LD structured data
removeJsonLd :: Effect Unit
removeJsonLd = removeJsonLdImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // resource hints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preload a resource
-- | as: "script", "style", "image", "font", "fetch"
preload :: String -> String -> Effect Unit
preload href as_ = addLinkImpl "preload" href as_

-- | Prefetch a resource for future navigation
prefetch :: String -> Effect Unit
prefetch href = addLinkImpl "prefetch" href ""

-- | Preconnect to an origin
preconnect :: String -> Effect Unit
preconnect origin = addLinkImpl "preconnect" origin ""

-- | DNS prefetch for an origin
dnsPrefetch :: String -> Effect Unit
dnsPrefetch origin = addLinkImpl "dns-prefetch" origin ""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // links
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set canonical URL
setCanonical :: String -> Effect Unit
setCanonical url = addLinkImpl "canonical" url ""

-- | Add a link tag
addLink :: String -> String -> Effect Unit
addLink rel href = addLinkImpl rel href ""

-- | Remove a link tag by rel
removeLink :: String -> Effect Unit
removeLink = removeLinkImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // favicon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set favicon
setFavicon :: String -> Effect Unit
setFavicon = setFaviconImpl
