-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // tour // target
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Target — Element targeting strategies for tour steps.
-- |
-- | ## Architecture
-- |
-- | Steps can target elements via multiple strategies:
-- | - CSS selectors (most common)
-- | - Element references (React refs, Angular ViewChild)
-- | - Explicit coordinates (for canvas/WebGL)
-- | - Virtual targets (no real element)
-- | - Beacon/marker targets (floating indicators)
-- |
-- | ## Schema Mapping
-- |
-- | | Type            | Pillar    | Purpose                              |
-- | |-----------------|-----------|--------------------------------------|
-- | | TargetKind      | Identity  | How to locate the target element     |
-- | | TargetSelector  | Identity  | CSS selector string                  |
-- | | TargetRef       | Identity  | Framework element reference          |
-- | | TargetRect      | Geometry  | Explicit bounding rectangle          |
-- | | TargetAnchor    | Spatial   | Anchor point within target           |
-- | | WaitStrategy    | Temporal  | How to wait for target availability  |

module Hydrogen.Element.Compound.Tour.Target
  ( -- * Target Kind
    TargetKind
      ( TargetSelector
      , TargetRef
      , TargetRect
      , TargetVirtual
      , TargetBeacon
      , TargetViewport
      , TargetMultiple
      )
  
  -- * Target Selector
  , Selector
  , selector
  , unwrapSelector
  
  -- * Target Rect
  , TargetRect
  , targetRect
  , rectX
  , rectY
  , rectWidth
  , rectHeight
  
  -- * Target Anchor
  , TargetAnchor
      ( AnchorCenter
      , AnchorTopLeft
      , AnchorTopCenter
      , AnchorTopRight
      , AnchorMiddleLeft
      , AnchorMiddleRight
      , AnchorBottomLeft
      , AnchorBottomCenter
      , AnchorBottomRight
      )
  , anchorToOffset
  
  -- * Wait Strategy
  , WaitStrategy
      ( WaitImmediate
      , WaitVisible
      , WaitInViewport
      , WaitInteractive
      , WaitStable
      , WaitCustom
      )
  
  -- * Wait Timeout
  , WaitTimeout
  , waitTimeout
  , unwrapWaitTimeout
  , defaultWaitTimeout
  , noTimeout
  
  -- * Target Config
  , TargetConfig
  , defaultTargetConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , max
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // target kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to locate the target element for a tour step.
-- |
-- | Different applications need different targeting strategies:
-- | - Web apps: CSS selectors
-- | - React/Vue: Component refs
-- | - Canvas/WebGL: Explicit coordinates
-- | - Modals/Overlays: Virtual targets
data TargetKind
  = TargetSelector Selector          -- ^ CSS selector string
  | TargetRef String                 -- ^ Framework ref name (React, Vue, etc.)
  | TargetRect TargetRect            -- ^ Explicit coordinates
  | TargetVirtual TargetRect         -- ^ Virtual element (no real DOM node)
  | TargetBeacon String              -- ^ Beacon ID (floating marker)
  | TargetViewport                   -- ^ Center of viewport (no specific element)
  | TargetMultiple (Array Selector)  -- ^ Multiple elements (group highlight)

derive instance eqTargetKind :: Eq TargetKind

instance showTargetKind :: Show TargetKind where
  show (TargetSelector s) = "Selector(" <> unwrapSelector s <> ")"
  show (TargetRef r) = "Ref(" <> r <> ")"
  show (TargetRect r) = "Rect(" <> show r <> ")"
  show (TargetVirtual r) = "Virtual(" <> show r <> ")"
  show (TargetBeacon b) = "Beacon(" <> b <> ")"
  show TargetViewport = "Viewport"
  show (TargetMultiple _) = "Multiple(...)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // selector
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS selector string for targeting DOM elements.
-- |
-- | Supports any valid CSS selector:
-- | - ID: "#my-button"
-- | - Class: ".btn-primary"
-- | - Attribute: "[data-tour='step-1']"
-- | - Complex: "nav > ul > li:first-child a"
newtype Selector = Selector String

derive instance eqSelector :: Eq Selector
derive instance ordSelector :: Ord Selector

instance showSelector :: Show Selector where
  show (Selector s) = "Selector(" <> s <> ")"

-- | Create a CSS selector
selector :: String -> Selector
selector = Selector

-- | Extract the selector string
unwrapSelector :: Selector -> String
unwrapSelector (Selector s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // target rect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Explicit bounding rectangle for target.
-- |
-- | Used when targeting canvas elements, WebGL objects, or
-- | when you need precise control over highlight position.
-- | All values are in pixels relative to viewport.
type TargetRect =
  { x :: Number       -- ^ Left edge
  , y :: Number       -- ^ Top edge
  , width :: Number   -- ^ Width
  , height :: Number  -- ^ Height
  }

-- | Create a target rectangle
targetRect :: Number -> Number -> Number -> Number -> TargetRect
targetRect x y w h =
  { x: max 0.0 x
  , y: max 0.0 y
  , width: max 0.0 w
  , height: max 0.0 h
  }

-- | Get x coordinate
rectX :: TargetRect -> Number
rectX r = r.x

-- | Get y coordinate
rectY :: TargetRect -> Number
rectY r = r.y

-- | Get width
rectWidth :: TargetRect -> Number
rectWidth r = r.width

-- | Get height
rectHeight :: TargetRect -> Number
rectHeight r = r.height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // target anchor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anchor point within the target element.
-- |
-- | When the target is large, the anchor determines which part
-- | the tooltip points to. Useful for targeting specific areas
-- | of complex components.
data TargetAnchor
  = AnchorCenter        -- ^ Center of element (default)
  | AnchorTopLeft       -- ^ Top-left corner
  | AnchorTopCenter     -- ^ Top edge center
  | AnchorTopRight      -- ^ Top-right corner
  | AnchorMiddleLeft    -- ^ Left edge center
  | AnchorMiddleRight   -- ^ Right edge center
  | AnchorBottomLeft    -- ^ Bottom-left corner
  | AnchorBottomCenter  -- ^ Bottom edge center
  | AnchorBottomRight   -- ^ Bottom-right corner

derive instance eqTargetAnchor :: Eq TargetAnchor
derive instance ordTargetAnchor :: Ord TargetAnchor

instance showTargetAnchor :: Show TargetAnchor where
  show AnchorCenter = "center"
  show AnchorTopLeft = "top-left"
  show AnchorTopCenter = "top-center"
  show AnchorTopRight = "top-right"
  show AnchorMiddleLeft = "middle-left"
  show AnchorMiddleRight = "middle-right"
  show AnchorBottomLeft = "bottom-left"
  show AnchorBottomCenter = "bottom-center"
  show AnchorBottomRight = "bottom-right"

instance boundedTargetAnchor :: Bounded TargetAnchor where
  bottom = AnchorCenter
  top = AnchorBottomRight

-- | Convert anchor to percentage offset (0-1 range)
anchorToOffset :: TargetAnchor -> { x :: Number, y :: Number }
anchorToOffset = case _ of
  AnchorCenter -> { x: 0.5, y: 0.5 }
  AnchorTopLeft -> { x: 0.0, y: 0.0 }
  AnchorTopCenter -> { x: 0.5, y: 0.0 }
  AnchorTopRight -> { x: 1.0, y: 0.0 }
  AnchorMiddleLeft -> { x: 0.0, y: 0.5 }
  AnchorMiddleRight -> { x: 1.0, y: 0.5 }
  AnchorBottomLeft -> { x: 0.0, y: 1.0 }
  AnchorBottomCenter -> { x: 0.5, y: 1.0 }
  AnchorBottomRight -> { x: 1.0, y: 1.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // wait strategy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Strategy for waiting until target element is ready.
-- |
-- | Handles dynamic content, lazy loading, and async rendering.
data WaitStrategy
  = WaitImmediate    -- ^ Don't wait, fail if not found
  | WaitVisible      -- ^ Wait until element exists in DOM
  | WaitInViewport   -- ^ Wait until element is in viewport
  | WaitInteractive  -- ^ Wait until element is interactive (not disabled)
  | WaitStable       -- ^ Wait until element position is stable (no layout shifts)
  | WaitCustom Int   -- ^ Custom wait time in milliseconds

derive instance eqWaitStrategy :: Eq WaitStrategy
derive instance ordWaitStrategy :: Ord WaitStrategy

instance showWaitStrategy :: Show WaitStrategy where
  show WaitImmediate = "immediate"
  show WaitVisible = "visible"
  show WaitInViewport = "in-viewport"
  show WaitInteractive = "interactive"
  show WaitStable = "stable"
  show (WaitCustom ms) = "custom(" <> show ms <> "ms)"

instance boundedWaitStrategy :: Bounded WaitStrategy where
  bottom = WaitImmediate
  top = WaitCustom 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // wait timeout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum time to wait for target element (in milliseconds).
-- |
-- | After timeout, the step can either:
-- | - Skip to next step
-- | - Show error state
-- | - Show step without highlight
newtype WaitTimeout = WaitTimeout (Maybe Int)

derive instance eqWaitTimeout :: Eq WaitTimeout
derive instance ordWaitTimeout :: Ord WaitTimeout

instance showWaitTimeout :: Show WaitTimeout where
  show (WaitTimeout (Just ms)) = "Timeout(" <> show ms <> "ms)"
  show (WaitTimeout Nothing) = "NoTimeout"

-- | Create a wait timeout in milliseconds
waitTimeout :: Int -> WaitTimeout
waitTimeout ms = WaitTimeout (Just (max 0 ms))

-- | Extract timeout value
unwrapWaitTimeout :: WaitTimeout -> Maybe Int
unwrapWaitTimeout (WaitTimeout ms) = ms

-- | Default timeout (5 seconds)
defaultWaitTimeout :: WaitTimeout
defaultWaitTimeout = WaitTimeout (Just 5000)

-- | No timeout (wait forever)
noTimeout :: WaitTimeout
noTimeout = WaitTimeout Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // target config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete target configuration for a step.
-- |
-- | Combines targeting strategy with wait behavior and anchor.
type TargetConfig =
  { target :: TargetKind            -- ^ How to find the element
  , anchor :: TargetAnchor          -- ^ Which part of element to target
  , waitStrategy :: WaitStrategy    -- ^ How to wait for element
  , waitTimeout :: WaitTimeout      -- ^ Maximum wait time
  , scrollPadding :: Int            -- ^ Padding when scrolling into view (px)
  , highlightPadding :: Int         -- ^ Padding around highlight (px)
  , interactive :: Boolean          -- ^ Allow interaction with target
  }

-- | Default target configuration
defaultTargetConfig :: Selector -> TargetConfig
defaultTargetConfig sel =
  { target: TargetSelector sel
  , anchor: AnchorCenter
  , waitStrategy: WaitVisible
  , waitTimeout: defaultWaitTimeout
  , scrollPadding: 20
  , highlightPadding: 4
  , interactive: false
  }
