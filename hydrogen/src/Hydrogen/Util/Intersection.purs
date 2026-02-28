-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // intersection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Intersection Observer utilities
-- |
-- | Type-safe wrapper around the Intersection Observer API for
-- | detecting element visibility.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.Intersection as Intersection
-- |
-- | -- Observe an element
-- | unobserve <- Intersection.observe element
-- |   { threshold: 0.5
-- |   , rootMargin: "10px"
-- |   }
-- |   \entry -> when entry.isIntersecting do
-- |     Console.log "Element is 50% visible!"
-- |
-- | -- Lazy load images
-- | Intersection.lazyLoad imageElement \_ -> do
-- |   loadHighResImage imageElement
-- |
-- | -- Infinite scroll
-- | Intersection.observe sentinel
-- |   { threshold: 0.0 }
-- |   \entry -> when entry.isIntersecting do
-- |     loadMoreItems
-- | ```
module Hydrogen.Util.Intersection
  ( -- * Types
    IntersectionEntry
  , IntersectionConfig
  , BoundingRect
    -- * Core Observer
  , observe
  , observeOnce
    -- * Default Config
  , defaultConfig
    -- * Threshold Helpers
  , threshold
  , thresholds
  , rootMargin
  , root
    -- * Convenience Functions
  , lazyLoad
  , onEnterViewport
  , onExitViewport
  , onVisibilityChange
  ) where

import Prelude hiding (when)

import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Web.DOM.Element (Element)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Intersection entry data
type IntersectionEntry =
  { isIntersecting :: Boolean
  , intersectionRatio :: Number
  , boundingClientRect :: BoundingRect
  , time :: Number
  }

-- | Bounding rectangle
type BoundingRect =
  { top :: Number
  , right :: Number
  , bottom :: Number
  , left :: Number
  , width :: Number
  , height :: Number
  }

-- | Observer configuration
type IntersectionConfig =
  { threshold :: Array Number
  , rootMargin :: String
  , root :: Maybe Element
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import observeImpl
  :: Element
  -> { threshold :: Array Number, rootMargin :: String, root :: Maybe Element }
  -> (IntersectionEntry -> Effect Unit)
  -> Effect (Effect Unit)

foreign import observeOnceImpl
  :: Element
  -> { threshold :: Array Number, rootMargin :: String, root :: Maybe Element }
  -> (IntersectionEntry -> Effect Unit)
  -> Effect (Effect Unit)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // default config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default observer configuration
-- |
-- | - threshold: [0.0] (any pixel visible)
-- | - rootMargin: "0px"
-- | - root: viewport
defaultConfig :: IntersectionConfig
defaultConfig =
  { threshold: [0.0]
  , rootMargin: "0px"
  , root: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // config builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set a single threshold (0.0 to 1.0)
-- |
-- | ```purescript
-- | config = threshold 0.5 defaultConfig  -- Trigger at 50% visibility
-- | ```
threshold :: Number -> IntersectionConfig -> IntersectionConfig
threshold t config = config { threshold = [t] }

-- | Set multiple thresholds
-- |
-- | ```purescript
-- | config = thresholds [0.0, 0.25, 0.5, 0.75, 1.0] defaultConfig
-- | ```
thresholds :: Array Number -> IntersectionConfig -> IntersectionConfig
thresholds ts config = config { threshold = ts }

-- | Set root margin (CSS margin syntax)
-- |
-- | ```purescript
-- | config = rootMargin "100px 0px" defaultConfig  -- 100px vertical margin
-- | ```
rootMargin :: String -> IntersectionConfig -> IntersectionConfig
rootMargin margin config = config { rootMargin = margin }

-- | Set root element (defaults to viewport)
-- |
-- | ```purescript
-- | config = root (Just scrollContainer) defaultConfig
-- | ```
root :: Maybe Element -> IntersectionConfig -> IntersectionConfig
root r config = config { root = r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // core observer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Observe an element for intersection changes
-- |
-- | Returns an unobserve function to stop observing.
-- |
-- | ```purescript
-- | unobserve <- observe element config \entry ->
-- |   Console.log $ "Visibility: " <> show entry.intersectionRatio
-- | ```
observe 
  :: Element 
  -> IntersectionConfig 
  -> (IntersectionEntry -> Effect Unit) 
  -> Effect (Effect Unit)
observe element config callback = observeImpl element config callback

-- | Observe an element once, then automatically stop
-- |
-- | Useful for lazy loading or one-time animations.
observeOnce
  :: Element
  -> IntersectionConfig
  -> (IntersectionEntry -> Effect Unit)
  -> Effect (Effect Unit)
observeOnce element config callback = observeOnceImpl element config callback

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // convenience functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lazy load helper
-- |
-- | Calls the callback once when the element enters the viewport.
-- |
-- | ```purescript
-- | lazyLoad imageElement \_ -> do
-- |   setAttribute "src" element actualImageUrl
-- | ```
lazyLoad :: Element -> (IntersectionEntry -> Effect Unit) -> Effect (Effect Unit)
lazyLoad element callback =
  observeOnce element (rootMargin "100px" defaultConfig) callback

-- | Trigger callback when element enters viewport
-- |
-- | Only fires when transitioning from not-visible to visible.
onEnterViewport :: Element -> Effect Unit -> Effect (Effect Unit)
onEnterViewport element callback = do
  wasVisibleRef <- newBoolRef false
  observe element defaultConfig \entry -> do
    wasVisible <- readBoolRef wasVisibleRef
    when (entry.isIntersecting && not wasVisible) callback
    writeBoolRef wasVisibleRef entry.isIntersecting

-- | Trigger callback when element exits viewport
-- |
-- | Only fires when transitioning from visible to not-visible.
onExitViewport :: Element -> Effect Unit -> Effect (Effect Unit)
onExitViewport element callback = do
  wasVisibleRef <- newBoolRef false
  observe element defaultConfig \entry -> do
    wasVisible <- readBoolRef wasVisibleRef
    when (not entry.isIntersecting && wasVisible) callback
    writeBoolRef wasVisibleRef entry.isIntersecting

-- | Listen for visibility changes (enter and exit)
-- |
-- | Callback receives true when entering, false when exiting.
onVisibilityChange :: Element -> (Boolean -> Effect Unit) -> Effect (Effect Unit)
onVisibilityChange element callback = do
  wasVisibleRef <- newBoolRef false
  observe element defaultConfig \entry -> do
    wasVisible <- readBoolRef wasVisibleRef
    when (entry.isIntersecting /= wasVisible) do
      callback entry.isIntersecting
    writeBoolRef wasVisibleRef entry.isIntersecting

-- FFI for simple boolean refs
foreign import newBoolRef :: Boolean -> Effect BoolRef
foreign import readBoolRef :: BoolRef -> Effect Boolean
foreign import writeBoolRef :: BoolRef -> Boolean -> Effect Unit
foreign import data BoolRef :: Type

-- Local when helper
when :: Boolean -> Effect Unit -> Effect Unit
when true action = action
when false _ = pure unit
