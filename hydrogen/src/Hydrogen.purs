-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                   // hydrogen
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Web Framework
-- |
-- | The purest web design language ever created.
-- |
-- | Hydrogen is a pure rendering abstraction — UI as data, not framework-specific
-- | code. Built on lawful abstractions with Schema atoms composing into Elements.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Haskell (Business Logic)
-- |     ↓ generates
-- | PureScript Element (Pure Data)
-- |     ↓ interprets
-- | WebGPU Runtime (Rendering)
-- | ```
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hydrogen.Router (class IsRoute, parseRoute, routeToPath)
-- | import Hydrogen.API.Client (get, post, withAuth)
-- | import Hydrogen.Data.Format (formatBytes, formatDuration)
-- | import Hydrogen.Data.RemoteData (RemoteData(..))
-- | import Hydrogen.Element.Compound.Skeleton as Skeleton
-- | import Hydrogen.Element.Compound.Alert as Alert
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Dimension.Device as Device
-- | ```
-- |
-- | ## Modules
-- |
-- | ### Core
-- | - **Hydrogen.Router** - Type-safe client-side routing
-- | - **Hydrogen.API.Client** - HTTP client with JSON encoding
-- | - **Hydrogen.SSG** - Static site generation
-- | - **Hydrogen.HTML.Renderer** - Render Element to HTML strings
-- |
-- | ### Schema (Atomic Design Primitives)
-- | - **Hydrogen.Schema.Color** - Color spaces, atoms, conversions
-- | - **Hydrogen.Schema.Dimension** - Pixel, spacing, viewport atoms
-- | - **Hydrogen.Schema.Geometry** - Radius, corners, transforms
-- | - **Hydrogen.Schema.Typography** - Font size, weight, line height
-- | - **Hydrogen.Schema.Motion** - Easing, duration, spring physics
-- | - **Hydrogen.Schema.Elevation** - Shadow, z-index
-- |
-- | ### Element (Pure UI as Data)
-- | - **Hydrogen.Element.Compound** - Schema-native components
-- | - **Hydrogen.Element.Layout** - Container, Grid, Stack, etc.
-- |
-- | ### Data
-- | - **Hydrogen.Data.Format** - Number/byte/duration formatting
-- | - **Hydrogen.Data.RemoteData** - RemoteData type for async state
module Hydrogen
  ( -- * Core
    module Hydrogen.Router
  , module Hydrogen.API.Client
  , module Hydrogen.SSG
  , module Hydrogen.HTML.Renderer
    -- * Data
  , module Hydrogen.Data.Format
  , module Hydrogen.Data.RemoteData
  ) where

import Hydrogen.Router (class IsRoute, class RouteMetadata, parseRoute, routeToPath, isProtected, isStaticRoute, routeTitle, routeDescription, routeOgImage, getPathname, getHostname, getOrigin, pushState, replaceState, onPopState, interceptLinks, navigate, normalizeTrailingSlash)
import Hydrogen.API.Client (ApiConfig, defaultConfig, withAuth, withLogging, get, post, put, patch, delete, ApiResult)
import Hydrogen.Data.Format (formatBytes, formatBytesCompact, parseBytes, kb, mb, gb, tb, formatNum, formatNumCompact, formatPercent, formatCount, formatDuration, formatDurationCompact, formatDurationMs, percentage, rate, ratio)
import Hydrogen.Data.RemoteData (RemoteData(NotAsked, Loading, Failure, Success), fromEither, fromMaybe, toEither, toMaybe, fold, withDefault, isNotAsked, isLoading, isFailure, isSuccess, mapError, map2, map3, map4, sequence, traverse)
import Hydrogen.SSG (DocConfig, defaultDocConfig, PageMeta, renderPage, renderDocument, pageMetaFromRoute, renderRouteStatic, metaTags, ogTags, twitterTags)
import Hydrogen.HTML.Renderer (render, renderWith, RenderOptions, defaultOptions)
