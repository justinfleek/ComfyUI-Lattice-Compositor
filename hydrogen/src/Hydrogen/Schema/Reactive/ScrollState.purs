-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // reactive // scroll-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ScrollState - scroll position and behavior atoms.
-- |
-- | Models scroll position, direction, velocity, and snap points
-- | for scroll-driven animations and infinite scroll patterns.

module Hydrogen.Schema.Reactive.ScrollState
  ( -- * Scroll Direction
    ScrollDirection(..)
  , isScrollingUp
  , isScrollingDown
  , isScrollingLeft
  , isScrollingRight
  , isScrollIdle
  , isVerticalScroll
  , isHorizontalScroll
  -- * Scroll Behavior
  , ScrollBehavior(..)
  , isSmooth
  , isInstant
  , isAuto
  -- * Overflow Behavior
  , OverflowBehavior(..)
  , isOverflowAuto
  , isOverflowScroll
  , isOverflowHidden
  , isOverflowVisible
  -- * Overscroll Behavior
  , OverscrollBehavior(..)
  , isOverscrollAuto
  , isOverscrollContain
  , isOverscrollNone
  -- * Scroll Position (Molecule)
  , ScrollPosition
  , scrollPosition
  , originScroll
  , scrollX
  , scrollY
  , scrollTop
  , scrollLeft
  -- * Scroll Bounds
  , ScrollBounds
  , scrollBounds
  , maxScrollX
  , maxScrollY
  , canScrollX
  , canScrollY
  -- * Scroll Progress
  , ScrollProgress
  , scrollProgress
  , progressX
  , progressY
  , isAtStart
  , isAtEnd
  , isNearEnd
  -- * Scroll Velocity
  , ScrollVelocity
  , scrollVelocity
  , noVelocity
  , velocityX
  , velocityY
  , isScrolling
  , isFastScroll
  -- * Scroll Snap
  , ScrollSnapType(..)
  , isSnapMandatory
  , isSnapProximity
  , isSnapNone
  , ScrollSnapAlign(..)
  , isSnapStart
  , isSnapCenter
  , isSnapEnd
  -- * Scroll State (Compound)
  , ScrollState
  , scrollState
  , initialScrollState
  -- * State Updates
  , updateScrollPosition
  , updateScrollVelocity
  , setScrollBehavior
  -- * Computed Properties
  , shouldShowScrollbar
  , shouldLoadMore
  , distanceToEnd
  , scrollPercentage
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // scroll direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of scroll movement
data ScrollDirection
  = ScrollUp       -- ^ Scrolling toward top
  | ScrollDown     -- ^ Scrolling toward bottom
  | ScrollLeft     -- ^ Scrolling toward left
  | ScrollRight    -- ^ Scrolling toward right
  | ScrollIdle     -- ^ Not actively scrolling

derive instance eqScrollDirection :: Eq ScrollDirection
derive instance ordScrollDirection :: Ord ScrollDirection

instance showScrollDirection :: Show ScrollDirection where
  show ScrollUp = "up"
  show ScrollDown = "down"
  show ScrollLeft = "left"
  show ScrollRight = "right"
  show ScrollIdle = "idle"

isScrollingUp :: ScrollDirection -> Boolean
isScrollingUp ScrollUp = true
isScrollingUp _ = false

isScrollingDown :: ScrollDirection -> Boolean
isScrollingDown ScrollDown = true
isScrollingDown _ = false

isScrollingLeft :: ScrollDirection -> Boolean
isScrollingLeft ScrollLeft = true
isScrollingLeft _ = false

isScrollingRight :: ScrollDirection -> Boolean
isScrollingRight ScrollRight = true
isScrollingRight _ = false

isScrollIdle :: ScrollDirection -> Boolean
isScrollIdle ScrollIdle = true
isScrollIdle _ = false

-- | Is scrolling vertically?
isVerticalScroll :: ScrollDirection -> Boolean
isVerticalScroll ScrollUp = true
isVerticalScroll ScrollDown = true
isVerticalScroll _ = false

-- | Is scrolling horizontally?
isHorizontalScroll :: ScrollDirection -> Boolean
isHorizontalScroll ScrollLeft = true
isHorizontalScroll ScrollRight = true
isHorizontalScroll _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS scroll-behavior
data ScrollBehavior
  = SmoothScroll   -- ^ Animated scrolling
  | InstantScroll  -- ^ Jump immediately
  | AutoScroll     -- ^ Browser default

derive instance eqScrollBehavior :: Eq ScrollBehavior
derive instance ordScrollBehavior :: Ord ScrollBehavior

instance showScrollBehavior :: Show ScrollBehavior where
  show SmoothScroll = "smooth"
  show InstantScroll = "instant"
  show AutoScroll = "auto"

isSmooth :: ScrollBehavior -> Boolean
isSmooth SmoothScroll = true
isSmooth _ = false

isInstant :: ScrollBehavior -> Boolean
isInstant InstantScroll = true
isInstant _ = false

isAuto :: ScrollBehavior -> Boolean
isAuto AutoScroll = true
isAuto _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // overflow behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS overflow behavior
data OverflowBehavior
  = OverflowAuto     -- ^ Scrollbar when needed
  | OverflowScroll   -- ^ Always show scrollbar
  | OverflowHidden   -- ^ Clip content, no scrollbar
  | OverflowVisible  -- ^ Content overflows container

derive instance eqOverflowBehavior :: Eq OverflowBehavior
derive instance ordOverflowBehavior :: Ord OverflowBehavior

instance showOverflowBehavior :: Show OverflowBehavior where
  show OverflowAuto = "auto"
  show OverflowScroll = "scroll"
  show OverflowHidden = "hidden"
  show OverflowVisible = "visible"

isOverflowAuto :: OverflowBehavior -> Boolean
isOverflowAuto OverflowAuto = true
isOverflowAuto _ = false

isOverflowScroll :: OverflowBehavior -> Boolean
isOverflowScroll OverflowScroll = true
isOverflowScroll _ = false

isOverflowHidden :: OverflowBehavior -> Boolean
isOverflowHidden OverflowHidden = true
isOverflowHidden _ = false

isOverflowVisible :: OverflowBehavior -> Boolean
isOverflowVisible OverflowVisible = true
isOverflowVisible _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // over-scroll behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS overscroll-behavior
data OverscrollBehavior
  = OverscrollAuto    -- ^ Allow scroll chaining
  | OverscrollContain -- ^ Prevent scroll chaining, allow bounce
  | OverscrollNone    -- ^ Prevent chaining and bounce

derive instance eqOverscrollBehavior :: Eq OverscrollBehavior
derive instance ordOverscrollBehavior :: Ord OverscrollBehavior

instance showOverscrollBehavior :: Show OverscrollBehavior where
  show OverscrollAuto = "auto"
  show OverscrollContain = "contain"
  show OverscrollNone = "none"

isOverscrollAuto :: OverscrollBehavior -> Boolean
isOverscrollAuto OverscrollAuto = true
isOverscrollAuto _ = false

isOverscrollContain :: OverscrollBehavior -> Boolean
isOverscrollContain OverscrollContain = true
isOverscrollContain _ = false

isOverscrollNone :: OverscrollBehavior -> Boolean
isOverscrollNone OverscrollNone = true
isOverscrollNone _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // scroll position molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current scroll position
type ScrollPosition =
  { x :: Number    -- ^ Horizontal scroll offset
  , y :: Number    -- ^ Vertical scroll offset
  }

-- | Create scroll position
scrollPosition :: Number -> Number -> ScrollPosition
scrollPosition x y =
  { x: max 0.0 x
  , y: max 0.0 y
  }

-- | Origin scroll position (0, 0)
originScroll :: ScrollPosition
originScroll = scrollPosition 0.0 0.0

-- | Get horizontal scroll
scrollX :: ScrollPosition -> Number
scrollX sp = sp.x

-- | Get vertical scroll
scrollY :: ScrollPosition -> Number
scrollY sp = sp.y

-- | Alias for scrollY (common name)
scrollTop :: ScrollPosition -> Number
scrollTop = scrollY

-- | Alias for scrollX (common name)
scrollLeft :: ScrollPosition -> Number
scrollLeft = scrollX

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // scroll bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum scroll extents
type ScrollBounds =
  { maxX :: Number   -- ^ Maximum horizontal scroll
  , maxY :: Number   -- ^ Maximum vertical scroll
  }

-- | Create scroll bounds
scrollBounds :: Number -> Number -> ScrollBounds
scrollBounds maxX maxY =
  { maxX: max 0.0 maxX
  , maxY: max 0.0 maxY
  }

-- | Get max horizontal scroll
maxScrollX :: ScrollBounds -> Number
maxScrollX sb = sb.maxX

-- | Get max vertical scroll
maxScrollY :: ScrollBounds -> Number
maxScrollY sb = sb.maxY

-- | Can scroll horizontally?
canScrollX :: ScrollBounds -> Boolean
canScrollX sb = sb.maxX > 0.0

-- | Can scroll vertically?
canScrollY :: ScrollBounds -> Boolean
canScrollY sb = sb.maxY > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll progress (0.0 - 1.0)
type ScrollProgress =
  { x :: Number    -- ^ Horizontal progress (0-1)
  , y :: Number    -- ^ Vertical progress (0-1)
  }

-- | Create scroll progress from position and bounds
scrollProgress :: ScrollPosition -> ScrollBounds -> ScrollProgress
scrollProgress pos bounds =
  { x: if bounds.maxX <= 0.0 then 0.0 else clamp 0.0 1.0 (pos.x / bounds.maxX)
  , y: if bounds.maxY <= 0.0 then 0.0 else clamp 0.0 1.0 (pos.y / bounds.maxY)
  }
  where
  clamp :: Number -> Number -> Number -> Number
  clamp lo hi v = max lo (min hi v)

-- | Get horizontal progress
progressX :: ScrollProgress -> Number
progressX sp = sp.x

-- | Get vertical progress
progressY :: ScrollProgress -> Number
progressY sp = sp.y

-- | Is at start of scroll area?
isAtStart :: ScrollProgress -> Boolean
isAtStart sp = sp.y <= 0.01 && sp.x <= 0.01

-- | Is at end of scroll area?
isAtEnd :: ScrollProgress -> Boolean
isAtEnd sp = sp.y >= 0.99 || sp.x >= 0.99

-- | Is near end? (within 10% - for infinite scroll trigger)
isNearEnd :: ScrollProgress -> Boolean
isNearEnd sp = sp.y >= 0.9 || sp.x >= 0.9

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll velocity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll velocity in pixels per second
type ScrollVelocity =
  { vx :: Number   -- ^ Horizontal velocity
  , vy :: Number   -- ^ Vertical velocity
  }

-- | Create scroll velocity
scrollVelocity :: Number -> Number -> ScrollVelocity
scrollVelocity vx vy = { vx, vy }

-- | No velocity (stationary)
noVelocity :: ScrollVelocity
noVelocity = scrollVelocity 0.0 0.0

-- | Get horizontal velocity
velocityX :: ScrollVelocity -> Number
velocityX sv = sv.vx

-- | Get vertical velocity
velocityY :: ScrollVelocity -> Number
velocityY sv = sv.vy

-- | Is actively scrolling? (any velocity)
isScrolling :: ScrollVelocity -> Boolean
isScrolling sv = abs sv.vx > 1.0 || abs sv.vy > 1.0
  where
  abs :: Number -> Number
  abs n = if n < 0.0 then -n else n

-- | Is scrolling fast? (> 1000 px/s)
isFastScroll :: ScrollVelocity -> Boolean
isFastScroll sv = abs sv.vx > 1000.0 || abs sv.vy > 1000.0
  where
  abs :: Number -> Number
  abs n = if n < 0.0 then -n else n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // scroll snap
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS scroll-snap-type
data ScrollSnapType
  = SnapMandatory   -- ^ Must snap to point
  | SnapProximity   -- ^ Snap if close to point
  | SnapNone        -- ^ No snapping

derive instance eqScrollSnapType :: Eq ScrollSnapType
derive instance ordScrollSnapType :: Ord ScrollSnapType

instance showScrollSnapType :: Show ScrollSnapType where
  show SnapMandatory = "mandatory"
  show SnapProximity = "proximity"
  show SnapNone = "none"

isSnapMandatory :: ScrollSnapType -> Boolean
isSnapMandatory SnapMandatory = true
isSnapMandatory _ = false

isSnapProximity :: ScrollSnapType -> Boolean
isSnapProximity SnapProximity = true
isSnapProximity _ = false

isSnapNone :: ScrollSnapType -> Boolean
isSnapNone SnapNone = true
isSnapNone _ = false

-- | CSS scroll-snap-align
data ScrollSnapAlign
  = SnapAlignStart   -- ^ Snap to start edge
  | SnapAlignCenter  -- ^ Snap to center
  | SnapAlignEnd     -- ^ Snap to end edge

derive instance eqScrollSnapAlign :: Eq ScrollSnapAlign
derive instance ordScrollSnapAlign :: Ord ScrollSnapAlign

instance showScrollSnapAlign :: Show ScrollSnapAlign where
  show SnapAlignStart = "start"
  show SnapAlignCenter = "center"
  show SnapAlignEnd = "end"

isSnapStart :: ScrollSnapAlign -> Boolean
isSnapStart SnapAlignStart = true
isSnapStart _ = false

isSnapCenter :: ScrollSnapAlign -> Boolean
isSnapCenter SnapAlignCenter = true
isSnapCenter _ = false

isSnapEnd :: ScrollSnapAlign -> Boolean
isSnapEnd SnapAlignEnd = true
isSnapEnd _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // scroll state compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete scroll state
type ScrollState =
  { position :: ScrollPosition
  , bounds :: ScrollBounds
  , velocity :: ScrollVelocity
  , direction :: ScrollDirection
  , behavior :: ScrollBehavior
  , overflow :: OverflowBehavior
  , overscroll :: OverscrollBehavior
  , snapType :: ScrollSnapType
  , isLocked :: Boolean           -- ^ Scroll locked (e.g., modal open)
  }

-- | Create scroll state
scrollState :: ScrollPosition -> ScrollBounds -> ScrollState
scrollState position bounds =
  { position
  , bounds
  , velocity: noVelocity
  , direction: ScrollIdle
  , behavior: AutoScroll
  , overflow: OverflowAuto
  , overscroll: OverscrollAuto
  , snapType: SnapNone
  , isLocked: false
  }

-- | Initial scroll state (at origin, no bounds)
initialScrollState :: ScrollState
initialScrollState = scrollState originScroll (scrollBounds 0.0 0.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // state updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update scroll position and compute direction
updateScrollPosition :: ScrollPosition -> ScrollState -> ScrollState
updateScrollPosition newPos ss =
  let dx = newPos.x - ss.position.x
      dy = newPos.y - ss.position.y
      dir = computeDirection dx dy
  in ss { position = newPos, direction = dir }
  where
  computeDirection :: Number -> Number -> ScrollDirection
  computeDirection dx dy
    | abs dy > abs dx && dy < 0.0 = ScrollUp
    | abs dy > abs dx && dy > 0.0 = ScrollDown
    | abs dx > abs dy && dx < 0.0 = ScrollLeft
    | abs dx > abs dy && dx > 0.0 = ScrollRight
    | otherwise = ScrollIdle
  
  abs :: Number -> Number
  abs n = if n < 0.0 then -n else n

-- | Update scroll velocity
updateScrollVelocity :: ScrollVelocity -> ScrollState -> ScrollState
updateScrollVelocity vel ss = ss { velocity = vel }

-- | Set scroll behavior
setScrollBehavior :: ScrollBehavior -> ScrollState -> ScrollState
setScrollBehavior behavior ss = ss { behavior = behavior }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Should show scrollbar?
shouldShowScrollbar :: ScrollState -> Boolean
shouldShowScrollbar ss = 
  canScrollY ss.bounds && 
  not (isOverflowHidden ss.overflow)

-- | Should load more content? (infinite scroll trigger)
shouldLoadMore :: ScrollState -> Boolean
shouldLoadMore ss =
  let progress = scrollProgress ss.position ss.bounds
  in isNearEnd progress && not ss.isLocked

-- | Distance to end of scroll area (pixels)
distanceToEnd :: ScrollState -> Number
distanceToEnd ss = ss.bounds.maxY - ss.position.y

-- | Overall scroll percentage (vertical)
scrollPercentage :: ScrollState -> Number
scrollPercentage ss =
  let progress = scrollProgress ss.position ss.bounds
  in progress.y * 100.0
