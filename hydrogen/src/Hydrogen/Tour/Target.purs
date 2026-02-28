-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // tour // target
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Target Resolution for Product Tours
-- |
-- | This module provides target resolution — finding and tracking the DOM elements
-- | that tour steps highlight. Targets can be:
-- | - CSS selectors
-- | - Test IDs (data-testid)
-- | - ARIA roles
-- | - Element references
-- | - Viewport (no element)
-- | - Multiple elements
-- |
-- | ## Design Philosophy
-- |
-- | Target resolution is inherently effectful (DOM access), but we describe
-- | targets as pure data. The runtime performs actual resolution.
-- |
-- | Multi-element targeting supports tours that highlight groups of related
-- | elements (e.g., "These are all your notification settings").
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Target as Target
-- |
-- | -- Single element by selector
-- | target1 = Target.bySelector ".my-button"
-- |
-- | -- By test ID (preferred for stability)
-- | target2 = Target.byTestId "submit-btn"
-- |
-- | -- Multiple elements
-- | target3 = Target.multiSelector ".sidebar-item"
-- |
-- | -- Viewport-centered modal
-- | target4 = Target.viewport
-- | ```
module Hydrogen.Tour.Target
  ( -- * Extended Target ADT
    TargetSpec(..)
  , TargetPriority(..)
  , TargetFallback
    -- * Target Builders
  , bySelector
  , byTestId
  , byRole
  , byRef
  , viewport
  , multiSelector
  , multiTestId
  , withFallback
  , withPriority
    -- * Target Rect
  , TargetRect
  , emptyRect
  , rectFromBounds
  , rectCenter
  , rectExpand
  , rectsUnion
  , rectContains
  , rectIntersects
    -- * Resolution State
  , ResolutionState(..)
  , ResolutionError(..)
  , isResolved
  , isUnresolved
  , isPending
    -- * Mutation Observation
  , MutationConfig
  , defaultMutationConfig
  , withSubtree
  , withAttributes
  , withChildList
  , shouldReobserve
    -- * Viewport Awareness
  , ViewportPosition(..)
  , isInViewport
  , isPartiallyVisible
  , needsScroll
  , scrollDirection
    -- * Multi-Target
  , MultiTargetLayout(..)
  , computeMultiTargetRect
  , multiTargetBounds
  ) where

import Prelude

import Data.Array (filter, foldl, head, length)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Show.Generic (genericShow)
import Data.String (joinWith)
import Hydrogen.Tour.Types (AriaRole, Pixel(Pixel), Selector, TestId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // extended target
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extended target specification
-- |
-- | Extends the basic Target from Types with additional capabilities:
-- | - Multi-element targeting
-- | - Fallback chains
-- | - Priority ordering
-- | - Element references
data TargetSpec
  = SingleSelector Selector
    -- ^ Single CSS selector
  | SingleTestId TestId
    -- ^ Single data-testid
  | SingleRole AriaRole (Maybe String)
    -- ^ ARIA role with optional accessible name
  | SingleRef String
    -- ^ Reference to a registered element
  | ViewportTarget
    -- ^ Center of viewport (modal-style)
  | MultiSelector Selector
    -- ^ All elements matching selector
  | MultiTestId TestId
    -- ^ All elements with data-testid prefix
  | MultiRole AriaRole
    -- ^ All elements with ARIA role
  | FallbackTarget (Array TargetSpec)
    -- ^ Try targets in order until one resolves

derive instance eqTargetSpec :: Eq TargetSpec
derive instance genericTargetSpec :: Generic TargetSpec _

-- | Manual Show instance to handle recursive FallbackTarget
instance showTargetSpec :: Show TargetSpec where
  show = case _ of
    SingleSelector sel -> "(SingleSelector " <> show sel <> ")"
    SingleTestId tid -> "(SingleTestId " <> show tid <> ")"
    SingleRole role mName -> "(SingleRole " <> show role <> " " <> show mName <> ")"
    SingleRef ref -> "(SingleRef " <> show ref <> ")"
    ViewportTarget -> "ViewportTarget"
    MultiSelector sel -> "(MultiSelector " <> show sel <> ")"
    MultiTestId tid -> "(MultiTestId " <> show tid <> ")"
    MultiRole role -> "(MultiRole " <> show role <> ")"
    FallbackTarget specs -> "(FallbackTarget [" <> joinWith ", " (map show specs) <> "])"

-- | Target resolution priority
-- |
-- | When multiple elements match, priority determines which to use.
data TargetPriority
  = FirstMatch
    -- ^ Use first matching element (DOM order)
  | LastMatch
    -- ^ Use last matching element
  | NearestToCenter
    -- ^ Element closest to viewport center
  | LargestElement
    -- ^ Element with largest bounding rect
  | SmallestElement
    -- ^ Element with smallest bounding rect
  | HighestZIndex
    -- ^ Element with highest z-index (most visible)

derive instance eqTargetPriority :: Eq TargetPriority
derive instance ordTargetPriority :: Ord TargetPriority
derive instance genericTargetPriority :: Generic TargetPriority _

instance showTargetPriority :: Show TargetPriority where
  show = genericShow

-- | Fallback configuration
type TargetFallback =
  { targets :: Array TargetSpec
  , stopOnFirst :: Boolean
    -- ^ Stop as soon as one resolves
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // target builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Target by CSS selector
bySelector :: Selector -> TargetSpec
bySelector = SingleSelector

-- | Target by test ID
byTestId :: TestId -> TargetSpec
byTestId = SingleTestId

-- | Target by ARIA role
byRole :: AriaRole -> Maybe String -> TargetSpec
byRole role name = SingleRole role name

-- | Target by element reference
byRef :: String -> TargetSpec
byRef = SingleRef

-- | Viewport-centered target (no element)
viewport :: TargetSpec
viewport = ViewportTarget

-- | Multiple elements by CSS selector
multiSelector :: Selector -> TargetSpec
multiSelector = MultiSelector

-- | Multiple elements by test ID prefix
multiTestId :: TestId -> TargetSpec
multiTestId = MultiTestId

-- | Add fallback targets
withFallback :: TargetSpec -> Array TargetSpec -> TargetSpec
withFallback primary fallbacks = FallbackTarget ([primary] <> fallbacks)

-- | Apply priority to target resolution
-- |
-- | Note: Priority is applied at runtime; this returns the target unchanged.
-- | The priority is stored in step configuration.
withPriority :: TargetPriority -> TargetSpec -> TargetSpec
withPriority _ target = target  -- Priority is metadata, not part of spec

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // target rect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding rectangle for a target element
-- |
-- | Coordinates are relative to the viewport (like getBoundingClientRect).
type TargetRect =
  { x :: Number       -- Left edge
  , y :: Number       -- Top edge
  , width :: Number   -- Width
  , height :: Number  -- Height
  , top :: Number     -- Top edge (same as y)
  , right :: Number   -- Right edge (x + width)
  , bottom :: Number  -- Bottom edge (y + height)
  , left :: Number    -- Left edge (same as x)
  }

-- | Empty rectangle (no target)
emptyRect :: TargetRect
emptyRect =
  { x: 0.0, y: 0.0, width: 0.0, height: 0.0
  , top: 0.0, right: 0.0, bottom: 0.0, left: 0.0
  }

-- | Create rect from bounds
rectFromBounds :: { x :: Number, y :: Number, width :: Number, height :: Number } -> TargetRect
rectFromBounds { x, y, width, height } =
  { x, y, width, height
  , top: y
  , right: x + width
  , bottom: y + height
  , left: x
  }

-- | Get center point of rectangle
rectCenter :: TargetRect -> { x :: Number, y :: Number }
rectCenter rect =
  { x: rect.x + rect.width / 2.0
  , y: rect.y + rect.height / 2.0
  }

-- | Expand rectangle by padding
rectExpand :: Pixel -> TargetRect -> TargetRect
rectExpand (Pixel p) rect =
  let padding = toNumber p
  in rectFromBounds
      { x: rect.x - padding
      , y: rect.y - padding
      , width: rect.width + padding * 2.0
      , height: rect.height + padding * 2.0
      }

-- | Union of multiple rectangles (bounding box)
rectsUnion :: Array TargetRect -> TargetRect
rectsUnion rects = case head rects of
  Nothing -> emptyRect
  Just first -> foldl unionTwo first rects
  where
  unionTwo :: TargetRect -> TargetRect -> TargetRect
  unionTwo a b =
    let minX = min a.left b.left
        minY = min a.top b.top
        maxX = max a.right b.right
        maxY = max a.bottom b.bottom
    in rectFromBounds
        { x: minX
        , y: minY
        , width: maxX - minX
        , height: maxY - minY
        }

-- | Check if point is inside rectangle
rectContains :: { x :: Number, y :: Number } -> TargetRect -> Boolean
rectContains point rect =
  point.x >= rect.left &&
  point.x <= rect.right &&
  point.y >= rect.top &&
  point.y <= rect.bottom

-- | Check if two rectangles intersect
rectIntersects :: TargetRect -> TargetRect -> Boolean
rectIntersects a b =
  a.left < b.right &&
  a.right > b.left &&
  a.top < b.bottom &&
  a.bottom > b.top

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // resolution state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current state of target resolution
data ResolutionState
  = Unresolved
    -- ^ Not yet attempted
  | Pending
    -- ^ Resolution in progress
  | Resolved TargetRect
    -- ^ Successfully resolved with bounds
  | ResolvedMulti (Array TargetRect)
    -- ^ Multiple elements resolved
  | Failed ResolutionError
    -- ^ Resolution failed

derive instance eqResolutionState :: Eq ResolutionState
derive instance genericResolutionState :: Generic ResolutionState _

instance showResolutionState :: Show ResolutionState where
  show = genericShow

-- | Why target resolution failed
data ResolutionError
  = NotFound
    -- ^ No matching element in DOM
  | ElementHidden
    -- ^ Element exists but is hidden (display: none, etc.)
  | ElementOutsideViewport
    -- ^ Element is outside scrollable area
  | MultipleMatches Int
    -- ^ Expected single, found multiple (with count)
  | InvalidSelector String
    -- ^ Malformed selector string
  | RefNotRegistered String
    -- ^ Element reference not registered
  | Timeout
    -- ^ Resolution timed out waiting for element

derive instance eqResolutionError :: Eq ResolutionError
derive instance genericResolutionError :: Generic ResolutionError _

instance showResolutionError :: Show ResolutionError where
  show = genericShow

-- | Check if resolution succeeded
isResolved :: ResolutionState -> Boolean
isResolved = case _ of
  Resolved _ -> true
  ResolvedMulti _ -> true
  _ -> false

-- | Check if resolution not yet attempted
isUnresolved :: ResolutionState -> Boolean
isUnresolved = case _ of
  Unresolved -> true
  _ -> false

-- | Check if resolution is in progress
isPending :: ResolutionState -> Boolean
isPending = case _ of
  Pending -> true
  _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // mutation observation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for MutationObserver
-- |
-- | Determines what DOM changes trigger target re-resolution.
type MutationConfig =
  { childList :: Boolean
    -- ^ Watch for child element changes
  , attributes :: Boolean
    -- ^ Watch for attribute changes
  , attributeFilter :: Maybe (Array String)
    -- ^ Specific attributes to watch
  , subtree :: Boolean
    -- ^ Watch entire subtree
  , characterData :: Boolean
    -- ^ Watch text content changes
  }

-- | Default mutation config (watch for structural changes)
defaultMutationConfig :: MutationConfig
defaultMutationConfig =
  { childList: true
  , attributes: true
  , attributeFilter: Nothing
  , subtree: true
  , characterData: false
  }

-- | Enable subtree observation
withSubtree :: Boolean -> MutationConfig -> MutationConfig
withSubtree enabled cfg = cfg { subtree = enabled }

-- | Enable attribute observation
withAttributes :: Boolean -> MutationConfig -> MutationConfig
withAttributes enabled cfg = cfg { attributes = enabled }

-- | Enable child list observation
withChildList :: Boolean -> MutationConfig -> MutationConfig
withChildList enabled cfg = cfg { childList = enabled }

-- | Determine if mutation should trigger re-observation
-- |
-- | Some mutations require complete re-resolution; others can be ignored.
shouldReobserve :: TargetSpec -> MutationConfig -> Boolean
shouldReobserve target cfg = case target of
  SingleSelector _ -> cfg.subtree || cfg.childList
  SingleTestId _ -> cfg.subtree || cfg.childList || hasTestIdFilter cfg
  SingleRole _ _ -> cfg.subtree || cfg.childList || hasRoleFilter cfg
  SingleRef _ -> false  -- Refs are stable
  ViewportTarget -> false  -- No element to observe
  MultiSelector _ -> cfg.subtree || cfg.childList
  MultiTestId _ -> cfg.subtree || cfg.childList
  MultiRole _ -> cfg.subtree || cfg.childList
  FallbackTarget targets -> any (\t -> shouldReobserve t cfg) targets
  where
  hasTestIdFilter :: MutationConfig -> Boolean
  hasTestIdFilter c = case c.attributeFilter of
    Just attrs -> any (_ == "data-testid") attrs
    Nothing -> c.attributes
  
  hasRoleFilter :: MutationConfig -> Boolean
  hasRoleFilter c = case c.attributeFilter of
    Just attrs -> any (_ == "role") attrs
    Nothing -> c.attributes
  
  any :: forall a. (a -> Boolean) -> Array a -> Boolean
  any f arr = length (filter f arr) > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // viewport awareness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of element relative to viewport
data ViewportPosition
  = InViewport
    -- ^ Completely visible
  | AboveViewport
    -- ^ Above visible area
  | BelowViewport
    -- ^ Below visible area
  | LeftOfViewport
    -- ^ Left of visible area
  | RightOfViewport
    -- ^ Right of visible area
  | PartiallyVisible { visiblePercent :: Number }
    -- ^ Partially visible with percentage

derive instance eqViewportPosition :: Eq ViewportPosition
derive instance genericViewportPosition :: Generic ViewportPosition _

instance showViewportPosition :: Show ViewportPosition where
  show = genericShow

-- | Check if rect is completely in viewport
isInViewport :: TargetRect -> { width :: Number, height :: Number } -> Boolean
isInViewport rect viewport =
  rect.top >= 0.0 &&
  rect.left >= 0.0 &&
  rect.bottom <= viewport.height &&
  rect.right <= viewport.width

-- | Check if rect is at least partially visible
isPartiallyVisible :: TargetRect -> { width :: Number, height :: Number } -> Boolean
isPartiallyVisible rect viewport =
  rectIntersects rect (viewportRect viewport)
  where
  viewportRect :: { width :: Number, height :: Number } -> TargetRect
  viewportRect v = rectFromBounds { x: 0.0, y: 0.0, width: v.width, height: v.height }

-- | Check if scrolling is needed to see element
needsScroll :: TargetRect -> { width :: Number, height :: Number } -> Boolean
needsScroll rect viewport = not (isInViewport rect viewport)

-- | Determine scroll direction needed
scrollDirection :: TargetRect -> { width :: Number, height :: Number } -> Maybe { x :: Number, y :: Number }
scrollDirection rect viewport
  | isInViewport rect viewport = Nothing
  | otherwise = Just
      { x: if rect.left < 0.0 then rect.left
           else if rect.right > viewport.width then rect.right - viewport.width
           else 0.0
      , y: if rect.top < 0.0 then rect.top
           else if rect.bottom > viewport.height then rect.bottom - viewport.height
           else 0.0
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // multi-target
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout strategy for multiple target elements
data MultiTargetLayout
  = BoundingBox
    -- ^ Single spotlight around all elements
  | Individual
    -- ^ Separate spotlights for each element
  | Convex
    -- ^ Convex hull around elements
  | Connected
    -- ^ Connected regions with bridges

derive instance eqMultiTargetLayout :: Eq MultiTargetLayout
derive instance genericMultiTargetLayout :: Generic MultiTargetLayout _

instance showMultiTargetLayout :: Show MultiTargetLayout where
  show = genericShow

-- | Compute combined rect for multiple targets
computeMultiTargetRect :: MultiTargetLayout -> Array TargetRect -> TargetRect
computeMultiTargetRect layout rects = case layout of
  BoundingBox -> rectsUnion rects
  Individual -> fromMaybe emptyRect (head rects)  -- Runtime handles individually
  Convex -> rectsUnion rects  -- Approximation; true convex hull is complex
  Connected -> rectsUnion rects  -- Approximation

-- | Get bounds containing all target rects with padding
multiTargetBounds :: Pixel -> Array TargetRect -> TargetRect
multiTargetBounds padding rects = rectExpand padding (rectsUnion rects)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number
foreign import toNumber :: Int -> Number
