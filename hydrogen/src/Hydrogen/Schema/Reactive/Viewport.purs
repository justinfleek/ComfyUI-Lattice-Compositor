-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // reactive // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport — A first-class container for displaying content.
-- |
-- | ## Philosophy
-- |
-- | A Viewport is NOT just "the browser window." It's a **bounded viewing region**
-- | with its own identity, settings, and controls. Think:
-- |
-- | - A video player viewport (with playback controls, fullscreen toggle)
-- | - A document viewport (with zoom, scroll position, page navigation)
-- | - A 3D scene viewport (with camera controls, render settings)
-- | - A dashboard viewport (with widget arrangement, refresh interval)
-- | - A code editor viewport (with syntax highlighting, line numbers)
-- | - A split pane viewport (one of N viewports in a layout)
-- |
-- | Each viewport has:
-- | - **Identity** (UUID5) — deterministic, reproducible across sessions
-- | - **Dimensions** — current width/height in CSS pixels
-- | - **Settings** — configuration specific to the content type
-- | - **Controls** — actions available to manipulate the viewport
-- | - **Content** — what's being displayed (polymorphic)
-- |
-- | ## Breakpoints vs Viewport
-- |
-- | Breakpoints describe **size thresholds** — they're properties OF a viewport.
-- | A viewport IS the container; breakpoints describe its current state.
-- |
-- | ## Container Queries
-- |
-- | Modern responsive design responds to **container size**, not just window size.
-- | A Viewport naturally supports this — its dimensions are always known,
-- | independent of the browser window.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Reactive.Viewport as Viewport
-- |
-- | -- Create a viewport for a dashboard
-- | dashboardViewport = Viewport.viewport
-- |   { namespace: "acme-corp"
-- |   , name: "main-dashboard"
-- |   , width: 1920
-- |   , height: 1080
-- |   , settings: DashboardSettings { refreshInterval: 30, theme: Dark }
-- |   }
-- |
-- | -- Get deterministic ID
-- | Viewport.id dashboardViewport  -- ViewportId "a3f8c2d1-..."
-- |
-- | -- Query current breakpoint
-- | Viewport.breakpoint dashboardViewport  -- Xxl
-- |
-- | -- Check if viewport supports certain content
-- | Viewport.canDisplay Video dashboardViewport  -- true
-- | ```

module Hydrogen.Schema.Reactive.Viewport
  ( -- * Viewport Identity
    ViewportId
  , viewportId
  , viewportIdFromString
  , unwrapViewportId
  , viewportIdToString
  , viewportNamespace
  
  -- * Breakpoint Type
  , Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl)
  , allBreakpoints
  
  -- * Breakpoint Values
  , breakpointMin
  , breakpointMax
  , breakpointRange
  
  -- * Breakpoint Detection
  , breakpointFromWidth
  , breakpointFromDimensions
  
  -- * Orientation
  , Orientation(Portrait, Landscape, Square)
  , orientationFromAspectRatio
  , orientationFromDimensions
  
  -- * Device Class
  , DeviceClass(Phone, Tablet, Desktop, LargeDesktop)
  , deviceClassFromBreakpoint
  , deviceClassFromWidth
  
  -- * Viewport Core
  , Viewport
  , viewport
  , viewportWithId
  
  -- * Viewport Accessors
  , getId
  , getWidth
  , getHeight
  , getBreakpoint
  , getOrientation
  , getDeviceClass
  , getDimensions
  
  -- * Viewport Controls
  , ViewportControl(Zoom, Pan, Scroll, Fullscreen, Refresh, Close)
  , ViewportControls
  , defaultControls
  , addControl
  , removeControl
  , hasControl
  
  -- * Viewport Settings
  , ZoomLevel(ZoomLevel)
  , zoomLevel
  , zoomFit
  , zoomFill
  , zoom100
  , zoom50
  , zoom200
  , unwrapZoom
  
  -- * Viewport State
  -- NOTE: ScrollPosition is re-exported from ScrollState (not defined here)
  , ViewportState
  , initialState
  , withZoom
  , withScroll
  , withFullscreen
  
  -- * ResponsiveValue
  , ResponsiveSpec
  , ResponsiveValue
  , responsive
  , static
  , resolve
  , resolveFor
  
  -- * CSS Generation
  , mediaQuery
  , mediaQueryMax
  , mediaQueryRange
  , containerQueryCss
  , breakpointClass
  
  -- * Breakpoint Comparison
  , isAtLeast
  , isAtMost
  , isBetween
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , (==)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (&&)
  , (<>)
  , ($)
  , Ordering(LT, EQ, GT)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Reactive.ScrollState (ScrollPosition, originScroll)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deterministic identifier for a viewport.
-- |
-- | Generated via UUID5 from namespace + name, ensuring the same viewport
-- | configuration always produces the same ID across sessions and systems.
newtype ViewportId = ViewportId String

derive instance eqViewportId :: Eq ViewportId
derive instance ordViewportId :: Ord ViewportId

instance showViewportId :: Show ViewportId where
  show (ViewportId id) = "ViewportId:" <> id

-- | UUID5 namespace for viewport identities.
viewportNamespace :: String
viewportNamespace = "viewport.hydrogen.schema"

-- | Create viewport ID from namespace and name.
-- |
-- | ```purescript
-- | viewportId "acme-corp" "main-dashboard"
-- | -- => ViewportId "a3f8c2d1-..." (deterministic)
-- | ```
viewportId :: String -> String -> ViewportId
viewportId ns name =
  let uuid = UUID5.uuid5 UUID5.nsElement (viewportNamespace <> ":" <> ns <> ":" <> name)
  in ViewportId (UUID5.toString uuid)

-- | Create viewport ID from raw string (for deserialization).
viewportIdFromString :: String -> ViewportId
viewportIdFromString = ViewportId

-- | Unwrap viewport ID to String.
unwrapViewportId :: ViewportId -> String
unwrapViewportId (ViewportId id) = id

-- | Convert to string (for serialization).
viewportIdToString :: ViewportId -> String
viewportIdToString = unwrapViewportId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // breakpoint type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard breakpoint tiers.
-- |
-- | Aligned with Tailwind CSS breakpoints for ecosystem compatibility.
-- | These are semantic size tiers, not arbitrary pixel values.
data Breakpoint
  = Xs   -- ^ Extra small: 0-639px (mobile portrait)
  | Sm   -- ^ Small: 640-767px (mobile landscape)
  | Md   -- ^ Medium: 768-1023px (tablet portrait)
  | Lg   -- ^ Large: 1024-1279px (tablet landscape / small desktop)
  | Xl   -- ^ Extra large: 1280-1535px (desktop)
  | Xxl  -- ^ 2x Extra large: 1536px+ (large desktop)

derive instance eqBreakpoint :: Eq Breakpoint

instance ordBreakpoint :: Ord Breakpoint where
  compare Xs Xs = EQ
  compare Xs _ = LT
  compare Sm Xs = GT
  compare Sm Sm = EQ
  compare Sm _ = LT
  compare Md Xs = GT
  compare Md Sm = GT
  compare Md Md = EQ
  compare Md _ = LT
  compare Lg Xs = GT
  compare Lg Sm = GT
  compare Lg Md = GT
  compare Lg Lg = EQ
  compare Lg _ = LT
  compare Xl Xxl = LT
  compare Xl Xl = EQ
  compare Xl _ = GT
  compare Xxl Xxl = EQ
  compare Xxl _ = GT

instance showBreakpoint :: Show Breakpoint where
  show Xs = "xs"
  show Sm = "sm"
  show Md = "md"
  show Lg = "lg"
  show Xl = "xl"
  show Xxl = "2xl"

-- | All breakpoints in order from smallest to largest.
allBreakpoints :: Array Breakpoint
allBreakpoints = [Xs, Sm, Md, Lg, Xl, Xxl]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // breakpoint values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum width (in CSS pixels) where this breakpoint begins.
breakpointMin :: Breakpoint -> Int
breakpointMin Xs = 0
breakpointMin Sm = 640
breakpointMin Md = 768
breakpointMin Lg = 1024
breakpointMin Xl = 1280
breakpointMin Xxl = 1536

-- | Maximum width (in CSS pixels) for this breakpoint (exclusive upper bound).
-- | Returns Nothing for Xxl since it has no upper bound.
breakpointMax :: Breakpoint -> Maybe Int
breakpointMax Xs = Just 639
breakpointMax Sm = Just 767
breakpointMax Md = Just 1023
breakpointMax Lg = Just 1279
breakpointMax Xl = Just 1535
breakpointMax Xxl = Nothing

-- | Get the pixel range for a breakpoint.
breakpointRange :: Breakpoint -> { min :: Int, max :: Maybe Int }
breakpointRange bp = { min: breakpointMin bp, max: breakpointMax bp }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // breakpoint detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Determine breakpoint from width in CSS pixels.
breakpointFromWidth :: Int -> Breakpoint
breakpointFromWidth w
  | w >= 1536 = Xxl
  | w >= 1280 = Xl
  | w >= 1024 = Lg
  | w >= 768 = Md
  | w >= 640 = Sm
  | otherwise = Xs

-- | Determine breakpoint and orientation from dimensions.
breakpointFromDimensions :: Int -> Int -> { breakpoint :: Breakpoint, orientation :: Orientation }
breakpointFromDimensions width height =
  { breakpoint: breakpointFromWidth width
  , orientation: orientationFromDimensions width height
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Screen/viewport orientation.
data Orientation
  = Portrait   -- ^ Height > Width
  | Landscape  -- ^ Width > Height
  | Square     -- ^ Width == Height

derive instance eqOrientation :: Eq Orientation

instance showOrientation :: Show Orientation where
  show Portrait = "portrait"
  show Landscape = "landscape"
  show Square = "square"

-- | Determine orientation from aspect ratio (width/height).
orientationFromAspectRatio :: Number -> Orientation
orientationFromAspectRatio ratio
  | ratio > 1.0 = Landscape
  | ratio < 1.0 = Portrait
  | otherwise = Square

-- | Determine orientation from dimensions.
orientationFromDimensions :: Int -> Int -> Orientation
orientationFromDimensions width height
  | width > height = Landscape
  | width < height = Portrait
  | otherwise = Square

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // device class
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic device classification.
-- |
-- | Higher-level than breakpoints — describes device capabilities,
-- | not just screen size.
data DeviceClass
  = Phone        -- ^ Xs, Sm — handheld, touch-primary
  | Tablet       -- ^ Md, Lg — portable, touch or stylus
  | Desktop      -- ^ Xl — stationary, mouse/keyboard primary
  | LargeDesktop -- ^ Xxl — multi-monitor, ultrawide

derive instance eqDeviceClass :: Eq DeviceClass

instance showDeviceClass :: Show DeviceClass where
  show Phone = "phone"
  show Tablet = "tablet"
  show Desktop = "desktop"
  show LargeDesktop = "large-desktop"

-- | Map breakpoint to device class.
deviceClassFromBreakpoint :: Breakpoint -> DeviceClass
deviceClassFromBreakpoint Xs = Phone
deviceClassFromBreakpoint Sm = Phone
deviceClassFromBreakpoint Md = Tablet
deviceClassFromBreakpoint Lg = Tablet
deviceClassFromBreakpoint Xl = Desktop
deviceClassFromBreakpoint Xxl = LargeDesktop

-- | Get device class from width.
deviceClassFromWidth :: Int -> DeviceClass
deviceClassFromWidth w = deviceClassFromBreakpoint (breakpointFromWidth w)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // viewport core
-- ═════════════════════════════════════════════════════════════════════════════

-- | A viewport — a bounded viewing region with identity and state.
-- |
-- | Viewports are first-class containers that can display any content.
-- | They have deterministic identity, dimensions, controls, and settings.
type Viewport =
  { id :: ViewportId
  , width :: Int
  , height :: Int
  , breakpoint :: Breakpoint
  , orientation :: Orientation
  , deviceClass :: DeviceClass
  , controls :: ViewportControls
  , state :: ViewportState
  }

-- | Create a viewport with auto-generated ID.
-- |
-- | ID is derived from namespace + name via UUID5.
viewport 
  :: { namespace :: String
     , name :: String
     , width :: Int
     , height :: Int
     }
  -> Viewport
viewport cfg =
  let
    bp = breakpointFromWidth cfg.width
    orient = orientationFromDimensions cfg.width cfg.height
  in
    { id: viewportId cfg.namespace cfg.name
    , width: cfg.width
    , height: cfg.height
    , breakpoint: bp
    , orientation: orient
    , deviceClass: deviceClassFromBreakpoint bp
    , controls: defaultControls
    , state: initialState
    }

-- | Create a viewport with explicit ID.
viewportWithId
  :: { id :: ViewportId
     , width :: Int
     , height :: Int
     }
  -> Viewport
viewportWithId cfg =
  let
    bp = breakpointFromWidth cfg.width
    orient = orientationFromDimensions cfg.width cfg.height
  in
    { id: cfg.id
    , width: cfg.width
    , height: cfg.height
    , breakpoint: bp
    , orientation: orient
    , deviceClass: deviceClassFromBreakpoint bp
    , controls: defaultControls
    , state: initialState
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // viewport accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get viewport ID.
getId :: Viewport -> ViewportId
getId vp = vp.id

-- | Get viewport width.
getWidth :: Viewport -> Int
getWidth vp = vp.width

-- | Get viewport height.
getHeight :: Viewport -> Int
getHeight vp = vp.height

-- | Get current breakpoint.
getBreakpoint :: Viewport -> Breakpoint
getBreakpoint vp = vp.breakpoint

-- | Get current orientation.
getOrientation :: Viewport -> Orientation
getOrientation vp = vp.orientation

-- | Get device class.
getDeviceClass :: Viewport -> DeviceClass
getDeviceClass vp = vp.deviceClass

-- | Get dimensions as record.
getDimensions :: Viewport -> { width :: Int, height :: Int }
getDimensions vp = { width: vp.width, height: vp.height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport controls
-- ═════════════════════════════════════════════════════════════════════════════

-- | Available viewport controls.
-- |
-- | Not all viewports support all controls — a document viewer might
-- | support Zoom and Scroll, while a video player supports Fullscreen.
data ViewportControl
  = Zoom       -- ^ Zoom in/out
  | Pan        -- ^ Pan/drag content
  | Scroll     -- ^ Scroll content
  | Fullscreen -- ^ Enter/exit fullscreen
  | Refresh    -- ^ Refresh/reload content
  | Close      -- ^ Close viewport

derive instance eqViewportControl :: Eq ViewportControl

instance showViewportControl :: Show ViewportControl where
  show Zoom = "zoom"
  show Pan = "pan"
  show Scroll = "scroll"
  show Fullscreen = "fullscreen"
  show Refresh = "refresh"
  show Close = "close"

-- | Set of available controls for a viewport.
type ViewportControls = Array ViewportControl

-- | Default controls for most viewports.
defaultControls :: ViewportControls
defaultControls = [Scroll, Zoom, Fullscreen]

-- | Add a control to viewport controls.
addControl :: ViewportControl -> ViewportControls -> ViewportControls
addControl ctrl ctrls =
  if Array.elem ctrl ctrls
    then ctrls
    else Array.snoc ctrls ctrl

-- | Remove a control from viewport controls.
removeControl :: ViewportControl -> ViewportControls -> ViewportControls
removeControl ctrl ctrls = Array.filter (\c -> not (c == ctrl)) ctrls

-- | Check if viewport has a control.
hasControl :: ViewportControl -> ViewportControls -> Boolean
hasControl ctrl ctrls = Array.elem ctrl ctrls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom level for viewport content.
-- |
-- | 1.0 = 100% (fit to viewport)
-- | 2.0 = 200% (zoomed in)
-- | 0.5 = 50% (zoomed out)
newtype ZoomLevel = ZoomLevel Number

derive instance eqZoomLevel :: Eq ZoomLevel
derive instance ordZoomLevel :: Ord ZoomLevel

instance showZoomLevel :: Show ZoomLevel where
  show (ZoomLevel z) = show z <> "x"

-- | Create zoom level from number.
zoomLevel :: Number -> ZoomLevel
zoomLevel = ZoomLevel

-- | Zoom to fit content in viewport.
zoomFit :: ZoomLevel
zoomFit = ZoomLevel 1.0

-- | Zoom to fill viewport (may crop).
zoomFill :: ZoomLevel
zoomFill = ZoomLevel 1.0

-- | 100% zoom.
zoom100 :: ZoomLevel
zoom100 = ZoomLevel 1.0

-- | 50% zoom.
zoom50 :: ZoomLevel
zoom50 = ZoomLevel 0.5

-- | 200% zoom.
zoom200 :: ZoomLevel
zoom200 = ZoomLevel 2.0

-- | Unwrap zoom level to Number.
unwrapZoom :: ZoomLevel -> Number
unwrapZoom (ZoomLevel z) = z

-- NOTE: ScrollPosition is imported from ScrollState to avoid duplication.
-- Use ScrollState.scrollPosition, ScrollState.originScroll, etc.

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // viewport state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mutable state of a viewport.
type ViewportState =
  { zoom :: ZoomLevel
  , scroll :: ScrollPosition
  , isFullscreen :: Boolean
  }

-- | Initial viewport state.
initialState :: ViewportState
initialState =
  { zoom: zoom100
  , scroll: originScroll
  , isFullscreen: false
  }

-- | Set zoom level.
withZoom :: ZoomLevel -> ViewportState -> ViewportState
withZoom z state = state { zoom = z }

-- | Set scroll position.
withScroll :: ScrollPosition -> ViewportState -> ViewportState
withScroll pos state = state { scroll = pos }

-- | Set fullscreen state.
withFullscreen :: Boolean -> ViewportState -> ViewportState
withFullscreen fs state = state { isFullscreen = fs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // responsive value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for responsive values.
-- |
-- | `base` is required (used for Xs and as fallback).
-- | Other breakpoints are optional — Nothing means "inherit from smaller".
type ResponsiveSpec a =
  { base :: a           -- ^ Value at Xs (required)
  , sm :: Maybe a       -- ^ Value at Sm (optional)
  , md :: Maybe a       -- ^ Value at Md (optional)
  , lg :: Maybe a       -- ^ Value at Lg (optional)
  , xl :: Maybe a       -- ^ Value at Xl (optional)
  , xxl :: Maybe a      -- ^ Value at Xxl (optional)
  }

-- | A value that changes at different breakpoints.
-- |
-- | Stores resolved value at each breakpoint.
type ResponsiveValue a =
  { xs :: a
  , sm :: a
  , md :: a
  , lg :: a
  , xl :: a
  , xxl :: a
  }

-- | Create a responsive value from a spec.
-- |
-- | Values cascade up — if a breakpoint is Nothing, it inherits
-- | from the previous smaller breakpoint.
responsive :: forall a. ResponsiveSpec a -> ResponsiveValue a
responsive spec =
  let
    xs = spec.base
    sm = resolveOr xs spec.sm
    md = resolveOr sm spec.md
    lg = resolveOr md spec.lg
    xl = resolveOr lg spec.xl
    xxl = resolveOr xl spec.xxl
  in
    { xs: xs, sm: sm, md: md, lg: lg, xl: xl, xxl: xxl }

-- | Helper: resolve Maybe with fallback.
resolveOr :: forall a. a -> Maybe a -> a
resolveOr fallback maybeVal = case maybeVal of
  Nothing -> fallback
  Just v -> v

-- | Create a static value (same at all breakpoints).
static :: forall a. a -> ResponsiveValue a
static a = { xs: a, sm: a, md: a, lg: a, xl: a, xxl: a }

-- | Resolve a responsive value at a specific breakpoint.
resolve :: forall a. ResponsiveValue a -> Breakpoint -> a
resolve rv Xs = rv.xs
resolve rv Sm = rv.sm
resolve rv Md = rv.md
resolve rv Lg = rv.lg
resolve rv Xl = rv.xl
resolve rv Xxl = rv.xxl

-- | Resolve a responsive value for a viewport.
resolveFor :: forall a. ResponsiveValue a -> Viewport -> a
resolveFor rv vp = resolve rv vp.breakpoint

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // css generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate CSS media query for breakpoint (min-width).
-- |
-- | ```purescript
-- | mediaQuery Lg  -- "@media (min-width: 1024px)"
-- | mediaQuery Xs  -- "" (no media query for base)
-- | ```
mediaQuery :: Breakpoint -> String
mediaQuery Xs = ""
mediaQuery bp = "@media (min-width: " <> show (breakpointMin bp) <> "px)"

-- | Generate CSS media query with max-width.
mediaQueryMax :: Breakpoint -> String
mediaQueryMax bp = case breakpointMax bp of
  Nothing -> ""
  Just maxPx -> "@media (max-width: " <> show maxPx <> "px)"

-- | Generate CSS media query for exact breakpoint range.
mediaQueryRange :: Breakpoint -> String
mediaQueryRange bp =
  let minPx = breakpointMin bp
  in case breakpointMax bp of
    Nothing -> "@media (min-width: " <> show minPx <> "px)"
    Just maxPx -> "@media (min-width: " <> show minPx <> "px) and (max-width: " <> show maxPx <> "px)"

-- | Generate CSS container query string.
-- |
-- | Responds to parent element size, not viewport.
-- | For full container query support, see ContainerQuery module.
containerQueryCss :: Breakpoint -> String
containerQueryCss Xs = ""
containerQueryCss bp = "@container (min-width: " <> show (breakpointMin bp) <> "px)"

-- | Get Tailwind-style class prefix for breakpoint.
-- |
-- | ```purescript
-- | breakpointClass Lg "grid-cols-4"  -- "lg:grid-cols-4"
-- | breakpointClass Xs "grid-cols-1"  -- "grid-cols-1"
-- | ```
breakpointClass :: Breakpoint -> String -> String
breakpointClass Xs cls = cls
breakpointClass bp cls = show bp <> ":" <> cls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if breakpoint is at least the threshold.
isAtLeast :: Breakpoint -> Breakpoint -> Boolean
isAtLeast threshold current = current >= threshold

-- | Check if breakpoint is at most the threshold.
isAtMost :: Breakpoint -> Breakpoint -> Boolean
isAtMost threshold current = current <= threshold

-- | Check if breakpoint is between two thresholds (inclusive).
isBetween :: Breakpoint -> Breakpoint -> Breakpoint -> Boolean
isBetween lower upper current = current >= lower && current <= upper
