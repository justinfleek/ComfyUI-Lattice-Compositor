-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // gestural // scroll
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scroll - scroll state, inertia, and snap points.
-- |
-- | Models scroll behavior for hyper-responsive interfaces.
-- | Supports inertial scrolling, overscroll, and snap points.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Math.Core (abs, clamp)
-- |
-- | ## Dependents
-- | - Component.* (scrollable components)
-- | - Interaction.InfiniteScroll
-- | - Interaction.PullToRefresh

module Hydrogen.Schema.Gestural.Scroll
  ( -- * Scroll Position
    ScrollPosition
  , scrollPosition
  , scrollX
  , scrollY
  , scrollTop
  , scrollLeft
  , addScrollPosition
    -- * Scroll Delta
  , ScrollDelta
  , scrollDelta
  , deltaPixel
  , deltaLine
  , deltaPage
  , normalizeDelta
  , isScrollingHorizontal
  , isScrollingVertical
    -- * Scroll Progress
  , ScrollProgress
  , scrollProgress
  , progressX
  , progressY
  , progressFromPosition
  , isAtStart
  , isAtEnd
  , isNearStart
  , isNearEnd
    -- * Scroll Bounds
  , ScrollBounds
  , scrollBounds
  , clampToScrollBounds
  , canScrollUp
  , canScrollDown
  , canScrollLeft
  , canScrollRight
  , scrollableHeight
  , scrollableWidth
    -- * Overscroll
  , OverscrollBehavior(OverscrollAuto, OverscrollContain, OverscrollNone)
  , OverscrollState
  , noOverscroll
  , overscrollAmount
  , isOverscrolling
  , applyOverscrollResistance
    -- * Snap Points
  , SnapAlignment(SnapStart, SnapCenter, SnapEnd)
  , SnapType(SnapMandatory, SnapProximity)
  , SnapPoint
  , snapPoint
  , findNearestSnap
  , shouldSnap
    -- * Scroll State
  , ScrollState
  , initialScrollState
  , updateScrollPosition
  , updateScrollVelocity
  , applyScrollDelta
  , isScrolling
  , scrollVelocity
    -- * Infinite Scroll
  , InfiniteScrollState
  , infiniteScroll
  , defaultInfiniteScroll
  , shouldLoadMore
  , startLoadingMore
  , finishLoadingMore
  , loadingError
  , resetInfiniteScroll
    -- * Pull to Refresh
  , PullToRefreshPhase(PullIdle, PullActive, PullThreshold, PullRefreshing, PullComplete)
  , PullToRefreshState
  , pullToRefresh
  , defaultPullToRefresh
  , canPullToRefresh
  , updatePullDistance
  , releasePull
  , completeRefresh
  , resetPullToRefresh
  , isRefreshing
  , isPastThreshold
  ) where

import Prelude hiding (clamp)

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core (abs, clamp)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // scroll // position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current scroll position
type ScrollPosition =
  { x :: Number    -- ^ Horizontal scroll offset (px)
  , y :: Number    -- ^ Vertical scroll offset (px)
  }

-- | Create scroll position
scrollPosition :: Number -> Number -> ScrollPosition
scrollPosition x y = { x, y }

-- | Get horizontal scroll
scrollX :: ScrollPosition -> Number
scrollX sp = sp.x

-- | Get vertical scroll
scrollY :: ScrollPosition -> Number
scrollY sp = sp.y

-- | Alias for scrollY (common DOM property name)
scrollTop :: ScrollPosition -> Number
scrollTop = scrollY

-- | Alias for scrollX (common DOM property name)
scrollLeft :: ScrollPosition -> Number
scrollLeft = scrollX

-- | Add two scroll positions
addScrollPosition :: ScrollPosition -> ScrollPosition -> ScrollPosition
addScrollPosition a b = { x: a.x + b.x, y: a.y + b.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll // delta
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll delta from wheel or touch events
type ScrollDelta =
  { deltaX :: Number    -- ^ Horizontal delta (px or lines)
  , deltaY :: Number    -- ^ Vertical delta (px or lines)
  , deltaMode :: Int    -- ^ 0=pixels, 1=lines, 2=pages (WheelEvent.deltaMode)
  }

-- | Create scroll delta
scrollDelta :: Number -> Number -> Int -> ScrollDelta
scrollDelta deltaX deltaY deltaMode = { deltaX, deltaY, deltaMode }

-- | Pixel delta mode (DOM_DELTA_PIXEL)
deltaPixel :: Int
deltaPixel = 0

-- | Line delta mode (DOM_DELTA_LINE)
deltaLine :: Int
deltaLine = 1

-- | Page delta mode (DOM_DELTA_PAGE)
deltaPage :: Int
deltaPage = 2

-- | Normalize delta to pixels
-- |
-- | Line = 16px, Page = viewport height (estimated at 800px)
normalizeDelta :: ScrollDelta -> ScrollDelta
normalizeDelta sd = case sd.deltaMode of
  1 -> sd { deltaX = sd.deltaX * 16.0, deltaY = sd.deltaY * 16.0, deltaMode = 0 }
  2 -> sd { deltaX = sd.deltaX * 800.0, deltaY = sd.deltaY * 800.0, deltaMode = 0 }
  _ -> sd

-- | Is scrolling horizontally?
isScrollingHorizontal :: ScrollDelta -> Boolean
isScrollingHorizontal sd = abs sd.deltaX > abs sd.deltaY

-- | Is scrolling vertically?
isScrollingVertical :: ScrollDelta -> Boolean
isScrollingVertical sd = abs sd.deltaY >= abs sd.deltaX

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // scroll // progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll progress as percentage (0.0 to 1.0)
type ScrollProgress =
  { x :: Number    -- ^ Horizontal progress (0-1)
  , y :: Number    -- ^ Vertical progress (0-1)
  }

-- | Create scroll progress
scrollProgress :: Number -> Number -> ScrollProgress
scrollProgress x y =
  { x: clamp 0.0 1.0 x
  , y: clamp 0.0 1.0 y
  }

-- | Get horizontal progress
progressX :: ScrollProgress -> Number
progressX sp = sp.x

-- | Get vertical progress
progressY :: ScrollProgress -> Number
progressY sp = sp.y

-- | Calculate progress from position and bounds
progressFromPosition :: ScrollPosition -> ScrollBounds -> ScrollProgress
progressFromPosition pos bounds =
  let
    maxX = scrollableWidth bounds
    maxY = scrollableHeight bounds
    px = if maxX > 0.0 then pos.x / maxX else 0.0
    py = if maxY > 0.0 then pos.y / maxY else 0.0
  in
    scrollProgress px py

-- | Is at start of scrollable area?
isAtStart :: ScrollProgress -> Boolean
isAtStart sp = sp.x <= 0.0 && sp.y <= 0.0

-- | Is at end of scrollable area?
isAtEnd :: ScrollProgress -> Boolean
isAtEnd sp = sp.x >= 1.0 && sp.y >= 1.0

-- | Is near start (within threshold)?
isNearStart :: Number -> ScrollProgress -> Boolean
isNearStart threshold sp = sp.x <= threshold || sp.y <= threshold

-- | Is near end (within threshold)?
isNearEnd :: Number -> ScrollProgress -> Boolean
isNearEnd threshold sp = sp.x >= (1.0 - threshold) || sp.y >= (1.0 - threshold)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // scroll // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scrollable bounds (viewport and content dimensions)
type ScrollBounds =
  { viewportWidth :: Number     -- ^ Visible viewport width
  , viewportHeight :: Number    -- ^ Visible viewport height
  , contentWidth :: Number      -- ^ Total content width
  , contentHeight :: Number     -- ^ Total content height
  }

-- | Create scroll bounds
scrollBounds :: Number -> Number -> Number -> Number -> ScrollBounds
scrollBounds viewportWidth viewportHeight contentWidth contentHeight =
  { viewportWidth, viewportHeight, contentWidth, contentHeight }

-- | Clamp position to valid scroll bounds
clampToScrollBounds :: ScrollBounds -> ScrollPosition -> ScrollPosition
clampToScrollBounds bounds pos =
  { x: clamp 0.0 (scrollableWidth bounds) pos.x
  , y: clamp 0.0 (scrollableHeight bounds) pos.y
  }

-- | Can scroll up from current position?
canScrollUp :: ScrollPosition -> Boolean
canScrollUp pos = pos.y > 0.0

-- | Can scroll down from current position?
canScrollDown :: ScrollPosition -> ScrollBounds -> Boolean
canScrollDown pos bounds = pos.y < scrollableHeight bounds

-- | Can scroll left from current position?
canScrollLeft :: ScrollPosition -> Boolean
canScrollLeft pos = pos.x > 0.0

-- | Can scroll right from current position?
canScrollRight :: ScrollPosition -> ScrollBounds -> Boolean
canScrollRight pos bounds = pos.x < scrollableWidth bounds

-- | Maximum scrollable height
scrollableHeight :: ScrollBounds -> Number
scrollableHeight bounds = max 0.0 (bounds.contentHeight - bounds.viewportHeight)

-- | Maximum scrollable width
scrollableWidth :: ScrollBounds -> Number
scrollableWidth bounds = max 0.0 (bounds.contentWidth - bounds.viewportWidth)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // scroll // over-scroll
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overscroll behavior (CSS overscroll-behavior values)
data OverscrollBehavior
  = OverscrollAuto     -- ^ Default browser behavior
  | OverscrollContain  -- ^ Prevent scroll chaining
  | OverscrollNone     -- ^ No overscroll effect

derive instance eqOverscrollBehavior :: Eq OverscrollBehavior
derive instance ordOverscrollBehavior :: Ord OverscrollBehavior

instance showOverscrollBehavior :: Show OverscrollBehavior where
  show OverscrollAuto = "auto"
  show OverscrollContain = "contain"
  show OverscrollNone = "none"

-- | Overscroll state (for rubber-band effect)
type OverscrollState =
  { top :: Number     -- ^ Overscroll above content
  , bottom :: Number  -- ^ Overscroll below content
  , left :: Number    -- ^ Overscroll left of content
  , right :: Number   -- ^ Overscroll right of content
  }

-- | No overscroll
noOverscroll :: OverscrollState
noOverscroll = { top: 0.0, bottom: 0.0, left: 0.0, right: 0.0 }

-- | Get total overscroll amount
overscrollAmount :: OverscrollState -> Number
overscrollAmount os = abs os.top + abs os.bottom + abs os.left + abs os.right

-- | Is currently overscrolling?
isOverscrolling :: OverscrollState -> Boolean
isOverscrolling os = overscrollAmount os > 0.0

-- | Apply resistance to overscroll (diminishing returns)
-- |
-- | Uses 1/(1+x) curve for natural rubber-band feel.
applyOverscrollResistance :: Number -> Number -> Number
applyOverscrollResistance maxOverscroll delta =
  let
    resistance = 0.5
    factor = 1.0 / (1.0 + abs delta / maxOverscroll * resistance)
  in
    delta * factor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // scroll // snap points
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snap alignment (CSS scroll-snap-align)
data SnapAlignment
  = SnapStart   -- ^ Snap to start of element
  | SnapCenter  -- ^ Snap to center of element
  | SnapEnd     -- ^ Snap to end of element

derive instance eqSnapAlignment :: Eq SnapAlignment
derive instance ordSnapAlignment :: Ord SnapAlignment

instance showSnapAlignment :: Show SnapAlignment where
  show SnapStart = "start"
  show SnapCenter = "center"
  show SnapEnd = "end"

-- | Snap strictness (CSS scroll-snap-type)
data SnapType
  = SnapMandatory  -- ^ Always snap after scrolling
  | SnapProximity  -- ^ Only snap if close enough

derive instance eqSnapType :: Eq SnapType
derive instance ordSnapType :: Ord SnapType

instance showSnapType :: Show SnapType where
  show SnapMandatory = "mandatory"
  show SnapProximity = "proximity"

-- | Snap point definition
type SnapPoint =
  { position :: Number       -- ^ Snap position (px)
  , alignment :: SnapAlignment  -- ^ How to align to this point
  }

-- | Create snap point
snapPoint :: Number -> SnapAlignment -> SnapPoint
snapPoint position alignment = { position, alignment }

-- | Find nearest snap point to position
findNearestSnap :: Array SnapPoint -> Number -> Maybe SnapPoint
findNearestSnap points pos = case points of
  [] -> Nothing
  _ -> Just (foldl closer (firstPoint points) points)
  where
    firstPoint :: Array SnapPoint -> SnapPoint
    firstPoint ps = case ps of
      [] -> { position: 0.0, alignment: SnapStart }
      _ -> unsafeFirst ps
    
    unsafeFirst :: Array SnapPoint -> SnapPoint
    unsafeFirst ps = foldl (\_ x -> x) { position: 0.0, alignment: SnapStart } (take1 ps)
    
    take1 :: Array SnapPoint -> Array SnapPoint
    take1 ps = case ps of
      [] -> []
      _ -> [foldl (\_ x -> x) { position: 0.0, alignment: SnapStart } ps]
    
    closer :: SnapPoint -> SnapPoint -> SnapPoint
    closer a b =
      if abs (a.position - pos) <= abs (b.position - pos)
        then a
        else b

-- | Should snap to point based on proximity threshold?
shouldSnap :: SnapType -> Number -> Number -> SnapPoint -> Boolean
shouldSnap snapType threshold currentPos point = case snapType of
  SnapMandatory -> true
  SnapProximity -> abs (point.position - currentPos) <= threshold

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete scroll state
type ScrollState =
  { position :: ScrollPosition     -- ^ Current scroll position
  , velocity :: ScrollPosition     -- ^ Current scroll velocity (px/ms)
  , bounds :: ScrollBounds         -- ^ Scrollable bounds
  , overscroll :: OverscrollState  -- ^ Overscroll state
  , isActive :: Boolean            -- ^ User actively scrolling
  , timestamp :: Number            -- ^ Last update timestamp
  }

-- | Initial scroll state
initialScrollState :: ScrollBounds -> ScrollState
initialScrollState bounds =
  { position: scrollPosition 0.0 0.0
  , velocity: scrollPosition 0.0 0.0
  , bounds
  , overscroll: noOverscroll
  , isActive: false
  , timestamp: 0.0
  }

-- | Update scroll position
updateScrollPosition :: ScrollPosition -> ScrollState -> ScrollState
updateScrollPosition newPos ss =
  ss { position = clampToScrollBounds ss.bounds newPos }

-- | Update scroll velocity
updateScrollVelocity :: ScrollPosition -> Number -> ScrollState -> ScrollState
updateScrollVelocity newVel timestamp ss =
  ss { velocity = newVel, timestamp = timestamp }

-- | Apply scroll delta to state
applyScrollDelta :: ScrollDelta -> ScrollState -> ScrollState
applyScrollDelta delta ss =
  let
    normalized = normalizeDelta delta
    newPos = addScrollPosition ss.position
      { x: normalized.deltaX, y: normalized.deltaY }
  in
    updateScrollPosition newPos ss

-- | Is currently scrolling (has velocity)?
isScrolling :: ScrollState -> Boolean
isScrolling ss = abs ss.velocity.x > 0.1 || abs ss.velocity.y > 0.1

-- | Get current scroll velocity
scrollVelocity :: ScrollState -> ScrollPosition
scrollVelocity ss = ss.velocity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // infinite scroll
-- ═════════════════════════════════════════════════════════════════════════════

-- | Infinite scroll state for loading more content
type InfiniteScrollState =
  { enabled :: Boolean          -- ^ Is infinite scroll enabled
  , loading :: Boolean          -- ^ Currently loading more
  , hasMore :: Boolean          -- ^ More content available
  , threshold :: Number         -- ^ Distance from bottom to trigger (px)
  , loadCount :: Int            -- ^ Number of loads performed
  , error :: Boolean            -- ^ Last load failed
  }

-- | Create infinite scroll state
infiniteScroll :: Number -> InfiniteScrollState
infiniteScroll threshold =
  { enabled: true
  , loading: false
  , hasMore: true
  , threshold
  , loadCount: 0
  , error: false
  }

-- | Default infinite scroll (100px threshold)
defaultInfiniteScroll :: InfiniteScrollState
defaultInfiniteScroll = infiniteScroll 100.0

-- | Should trigger load based on scroll state?
shouldLoadMore :: ScrollState -> InfiniteScrollState -> Boolean
shouldLoadMore ss is =
  is.enabled
  && is.hasMore
  && not is.loading
  && not is.error
  && distanceToBottom ss <= is.threshold
  where
  distanceToBottom :: ScrollState -> Number
  distanceToBottom scrollState =
    scrollableHeight scrollState.bounds - scrollState.position.y

-- | Start loading more
startLoadingMore :: InfiniteScrollState -> InfiniteScrollState
startLoadingMore is = is { loading = true, error = false }

-- | Finish loading (success)
finishLoadingMore :: Boolean -> InfiniteScrollState -> InfiniteScrollState
finishLoadingMore hasMore is = is
  { loading = false
  , hasMore = hasMore
  , loadCount = is.loadCount + 1
  }

-- | Finish loading (error)
loadingError :: InfiniteScrollState -> InfiniteScrollState
loadingError is = is { loading = false, error = true }

-- | Reset infinite scroll state
resetInfiniteScroll :: InfiniteScrollState -> InfiniteScrollState
resetInfiniteScroll is = is
  { loading = false
  , hasMore = true
  , loadCount = 0
  , error = false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pull to refresh
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pull to refresh phase
data PullToRefreshPhase
  = PullIdle         -- ^ Not pulling
  | PullActive       -- ^ Actively pulling down
  | PullThreshold    -- ^ Past threshold, will refresh on release
  | PullRefreshing   -- ^ Refreshing in progress
  | PullComplete     -- ^ Refresh complete, animating back

derive instance eqPullToRefreshPhase :: Eq PullToRefreshPhase
derive instance ordPullToRefreshPhase :: Ord PullToRefreshPhase

instance showPullToRefreshPhase :: Show PullToRefreshPhase where
  show PullIdle = "idle"
  show PullActive = "active"
  show PullThreshold = "threshold"
  show PullRefreshing = "refreshing"
  show PullComplete = "complete"

-- | Pull to refresh state
type PullToRefreshState =
  { phase :: PullToRefreshPhase  -- ^ Current phase
  , pullDistance :: Number       -- ^ Current pull distance (px)
  , threshold :: Number          -- ^ Distance to trigger refresh (px)
  , maxPull :: Number            -- ^ Maximum pull distance (px)
  , progress :: Number           -- ^ Progress 0-1 toward threshold
  , enabled :: Boolean           -- ^ Is pull to refresh enabled
  }

-- | Create pull to refresh state
pullToRefresh :: Number -> Number -> PullToRefreshState
pullToRefresh threshold maxPull =
  { phase: PullIdle
  , pullDistance: 0.0
  , threshold
  , maxPull
  , progress: 0.0
  , enabled: true
  }

-- | Default pull to refresh (64px threshold, 128px max)
defaultPullToRefresh :: PullToRefreshState
defaultPullToRefresh = pullToRefresh 64.0 128.0

-- | Can pull to refresh from current scroll position?
canPullToRefresh :: ScrollState -> Boolean
canPullToRefresh ss = ss.position.y <= 0.0

-- | Update pull distance (during drag)
updatePullDistance :: Number -> PullToRefreshState -> PullToRefreshState
updatePullDistance distance ptr
  | not ptr.enabled = ptr
  | otherwise =
    let
      clamped = max 0.0 (min ptr.maxPull distance)
      prog = if ptr.threshold > 0.0 then min 1.0 (clamped / ptr.threshold) else 0.0
      newPhase = 
        if clamped >= ptr.threshold 
          then PullThreshold
          else if clamped > 0.0 then PullActive else PullIdle
    in ptr
      { pullDistance = clamped
      , progress = prog
      , phase = if ptr.phase == PullRefreshing then PullRefreshing else newPhase
      }

-- | Release pull (triggers refresh if past threshold)
releasePull :: PullToRefreshState -> PullToRefreshState
releasePull ptr = case ptr.phase of
  PullThreshold -> ptr { phase = PullRefreshing }
  PullRefreshing -> ptr  -- Already refreshing
  _ -> ptr { phase = PullIdle, pullDistance = 0.0, progress = 0.0 }

-- | Complete refresh
completeRefresh :: PullToRefreshState -> PullToRefreshState
completeRefresh ptr = ptr
  { phase = PullComplete
  , pullDistance = 0.0
  , progress = 0.0
  }

-- | Reset to idle
resetPullToRefresh :: PullToRefreshState -> PullToRefreshState
resetPullToRefresh ptr = ptr
  { phase = PullIdle
  , pullDistance = 0.0
  , progress = 0.0
  }

-- | Is currently refreshing?
isRefreshing :: PullToRefreshState -> Boolean
isRefreshing ptr = ptr.phase == PullRefreshing

-- | Is pull past threshold?
isPastThreshold :: PullToRefreshState -> Boolean
isPastThreshold ptr = ptr.phase == PullThreshold
