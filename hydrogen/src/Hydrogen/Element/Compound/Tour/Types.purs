-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // tour // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Types — Core atomic types for product tour component.
-- |
-- | ## Architecture
-- |
-- | This module defines the **atomic** building blocks for tours:
-- | - Identifiers (StepId, TourId)
-- | - Placement primitives
-- | - Scroll behavior
-- |
-- | Higher-level types are composed in sibling modules:
-- | - `Tour.Target` — Target selection strategies
-- | - `Tour.Highlight` — Spotlight and overlay styles
-- | - `Tour.Animation` — Transitions and timing
-- | - `Tour.Navigation` — UI controls
-- | - `Tour.Content` — Step content types
-- | - `Tour.Branching` — Flow control
-- | - `Tour.Accessibility` — A11y configuration
-- | - `Tour.Step` — Step molecule (composed atoms)
-- | - `Tour.Config` — TourConfig compound
-- | - `Tour.State` — Runtime state
-- | - `Tour.Msg` — Message ADT
-- |
-- | ## Schema Mapping
-- |
-- | | Type           | Pillar    | Purpose                              |
-- | |----------------|-----------|--------------------------------------|
-- | | StepId         | Identity  | Unique step identifier               |
-- | | TourId         | Identity  | Unique tour identifier               |
-- | | StepIndex      | Dimension | Bounded step position                |
-- | | Placement      | Spatial   | Tooltip position (12 positions)      |
-- | | PlacementAuto  | Spatial   | Auto-positioning strategy            |
-- | | Alignment      | Spatial   | Content alignment within tooltip     |
-- | | ScrollBehavior | Temporal  | Animation on step change             |
-- | | ScrollBlock    | Spatial   | Vertical scroll alignment            |
-- | | ScrollInline   | Spatial   | Horizontal scroll alignment          |

module Hydrogen.Element.Compound.Tour.Types
  ( -- * Identifiers
    StepId
  , stepId
  , unwrapStepId
  , TourId
  , tourId
  , unwrapTourId
  
  -- * Step Index
  , StepIndex
  , stepIndex
  , unwrapStepIndex
  , firstStepIndex
  , nextStepIndex
  , prevStepIndex
  
  -- * Side
  , Side
      ( SideTop
      , SideRight
      , SideBottom
      , SideLeft
      )
  , oppositeSide
  
  -- * Placement
  , Placement
      ( PlacementTop
      , PlacementTopStart
      , PlacementTopEnd
      , PlacementBottom
      , PlacementBottomStart
      , PlacementBottomEnd
      , PlacementLeft
      , PlacementLeftStart
      , PlacementLeftEnd
      , PlacementRight
      , PlacementRightStart
      , PlacementRightEnd
      )
  , placementToString
  , placementToSide
  , oppositePlacement
  
  -- * Placement Auto
  , PlacementAuto
      ( AutoBest
      , AutoVertical
      , AutoHorizontal
      , AutoClockwise
      , AutoCounterclockwise
      , AutoFlip
      , AutoFixed
      )
  
  -- * Alignment
  , Alignment
      ( AlignStart
      , AlignCenter
      , AlignEnd
      )
  
  -- * Scroll Behavior
  , ScrollBehavior
      ( ScrollSmooth
      , ScrollInstant
      , ScrollNone
      )
  , scrollBehaviorToString
  
  -- * Scroll Block (vertical alignment)
  , ScrollBlock
      ( BlockStart
      , BlockCenter
      , BlockEnd
      , BlockNearest
      )
  
  -- * Scroll Inline (horizontal alignment)
  , ScrollInline
      ( InlineStart
      , InlineCenter
      , InlineEnd
      , InlineNearest
      )
  
  ) where
  
-- NOTE: Legacy types (Step, StepConfig, TourProps, etc.) are in Tour.Compat.
-- This module (Types) contains only atomic primitives.
-- Compat imports FROM Types, so Types cannot re-export Compat (would create cycle).

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
  , (+)
  , (-)
  , (<>)
  )

-- NOTE: Compat import removed to break cycle.
-- Legacy types (Step, StepConfig, etc.) should be imported from Tour.Compat directly.
-- This module is the leaf — it contains only atomic primitives with no Tour dependencies.

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // identifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a tour step.
-- |
-- | StepIds enable:
-- | - Stable references across re-renders
-- | - Bookmark/deep-link to specific steps
-- | - Analytics tracking per step
-- | - Conditional branching targets
newtype StepId = StepId String

derive instance eqStepId :: Eq StepId
derive instance ordStepId :: Ord StepId

instance showStepId :: Show StepId where
  show (StepId s) = "StepId(" <> s <> ")"

-- | Create a step ID from a string
stepId :: String -> StepId
stepId = StepId

-- | Extract the string value from a StepId
unwrapStepId :: StepId -> String
unwrapStepId (StepId s) = s

-- | Unique identifier for a tour.
-- |
-- | TourIds enable:
-- | - Multiple concurrent tours
-- | - Tour versioning for persistence
-- | - A/B testing different tour variants
newtype TourId = TourId String

derive instance eqTourId :: Eq TourId
derive instance ordTourId :: Ord TourId

instance showTourId :: Show TourId where
  show (TourId s) = "TourId(" <> s <> ")"

-- | Create a tour ID from a string
tourId :: String -> TourId
tourId = TourId

-- | Extract the string value from a TourId
unwrapTourId :: TourId -> String
unwrapTourId (TourId s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // step index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounded step index (0 to n-1 where n is step count).
-- |
-- | Always non-negative. Navigation functions handle bounds checking
-- | based on total step count in the tour.
newtype StepIndex = StepIndex Int

derive instance eqStepIndex :: Eq StepIndex
derive instance ordStepIndex :: Ord StepIndex

instance showStepIndex :: Show StepIndex where
  show (StepIndex i) = "Step[" <> show i <> "]"

-- | Create a step index, clamped to non-negative
stepIndex :: Int -> StepIndex
stepIndex i = StepIndex (max 0 i)

-- | Extract the integer value from a StepIndex
unwrapStepIndex :: StepIndex -> Int
unwrapStepIndex (StepIndex i) = i

-- | First step (index 0)
firstStepIndex :: StepIndex
firstStepIndex = StepIndex 0

-- | Next step index (caller must handle bounds)
nextStepIndex :: StepIndex -> StepIndex
nextStepIndex (StepIndex i) = StepIndex (i + 1)

-- | Previous step index (floors at 0)
prevStepIndex :: StepIndex -> StepIndex
prevStepIndex (StepIndex i) = StepIndex (max 0 (i - 1))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // side
-- ═════════════════════════════════════════════════════════════════════════════

-- | Side of the target element for tooltip placement.
-- |
-- | Represents the primary direction from the target where the tooltip appears.
data Side
  = SideTop
  | SideRight
  | SideBottom
  | SideLeft

derive instance eqSide :: Eq Side
derive instance ordSide :: Ord Side

instance showSide :: Show Side where
  show SideTop = "top"
  show SideRight = "right"
  show SideBottom = "bottom"
  show SideLeft = "left"

instance boundedSide :: Bounded Side where
  bottom = SideTop
  top = SideLeft

-- | Get the opposite side (for flip fallback).
oppositeSide :: Side -> Side
oppositeSide = case _ of
  SideTop -> SideBottom
  SideBottom -> SideTop
  SideLeft -> SideRight
  SideRight -> SideLeft

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // placement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tooltip placement relative to target element.
-- |
-- | 12 positions following CSS logical positioning with start/end modifiers.
-- | These are explicit placements; for auto-positioning see PlacementAuto.
data Placement
  = PlacementTop            -- ^ Centered above target
  | PlacementTopStart       -- ^ Above, aligned to start edge
  | PlacementTopEnd         -- ^ Above, aligned to end edge
  | PlacementBottom         -- ^ Centered below target
  | PlacementBottomStart    -- ^ Below, aligned to start edge
  | PlacementBottomEnd      -- ^ Below, aligned to end edge
  | PlacementLeft           -- ^ Centered to left of target
  | PlacementLeftStart      -- ^ Left, aligned to top edge
  | PlacementLeftEnd        -- ^ Left, aligned to bottom edge
  | PlacementRight          -- ^ Centered to right of target
  | PlacementRightStart     -- ^ Right, aligned to top edge
  | PlacementRightEnd       -- ^ Right, aligned to bottom edge

derive instance eqPlacement :: Eq Placement
derive instance ordPlacement :: Ord Placement

instance showPlacement :: Show Placement where
  show = placementToString

instance boundedPlacement :: Bounded Placement where
  bottom = PlacementTop
  top = PlacementRightEnd

-- | Get the opposite placement (for flip fallback)
oppositePlacement :: Placement -> Placement
oppositePlacement = case _ of
  PlacementTop -> PlacementBottom
  PlacementTopStart -> PlacementBottomStart
  PlacementTopEnd -> PlacementBottomEnd
  PlacementBottom -> PlacementTop
  PlacementBottomStart -> PlacementTopStart
  PlacementBottomEnd -> PlacementTopEnd
  PlacementLeft -> PlacementRight
  PlacementLeftStart -> PlacementRightStart
  PlacementLeftEnd -> PlacementRightEnd
  PlacementRight -> PlacementLeft
  PlacementRightStart -> PlacementLeftStart
  PlacementRightEnd -> PlacementLeftEnd

-- | Extract the primary side from a placement.
-- |
-- | Used by animation system to determine entry/exit directions.
placementToSide :: Placement -> Side
placementToSide = case _ of
  PlacementTop -> SideTop
  PlacementTopStart -> SideTop
  PlacementTopEnd -> SideTop
  PlacementBottom -> SideBottom
  PlacementBottomStart -> SideBottom
  PlacementBottomEnd -> SideBottom
  PlacementLeft -> SideLeft
  PlacementLeftStart -> SideLeft
  PlacementLeftEnd -> SideLeft
  PlacementRight -> SideRight
  PlacementRightStart -> SideRight
  PlacementRightEnd -> SideRight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // placement auto
-- ═════════════════════════════════════════════════════════════════════════════

-- | Auto-positioning strategy when preferred placement doesn't fit.
-- |
-- | The runtime uses these strategies to find optimal tooltip position
-- | based on available viewport space.
data PlacementAuto
  = AutoBest               -- ^ Choose position with most available space
  | AutoVertical           -- ^ Try top, then bottom
  | AutoHorizontal         -- ^ Try left, then right
  | AutoClockwise          -- ^ Rotate clockwise through positions
  | AutoCounterclockwise   -- ^ Rotate counter-clockwise
  | AutoFlip               -- ^ Try opposite placement only
  | AutoFixed              -- ^ Never reposition (may overflow)

derive instance eqPlacementAuto :: Eq PlacementAuto
derive instance ordPlacementAuto :: Ord PlacementAuto

instance showPlacementAuto :: Show PlacementAuto where
  show AutoBest = "best"
  show AutoVertical = "vertical"
  show AutoHorizontal = "horizontal"
  show AutoClockwise = "clockwise"
  show AutoCounterclockwise = "counterclockwise"
  show AutoFlip = "flip"
  show AutoFixed = "fixed"

instance boundedPlacementAuto :: Bounded PlacementAuto where
  bottom = AutoBest
  top = AutoFixed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content alignment within tooltip or step container.
-- |
-- | Used for text alignment, button alignment, media alignment.
data Alignment
  = AlignStart    -- ^ Left in LTR, right in RTL
  | AlignCenter   -- ^ Centered
  | AlignEnd      -- ^ Right in LTR, left in RTL

derive instance eqAlignment :: Eq Alignment
derive instance ordAlignment :: Ord Alignment

instance showAlignment :: Show Alignment where
  show AlignStart = "start"
  show AlignCenter = "center"
  show AlignEnd = "end"

instance boundedAlignment :: Bounded Alignment where
  bottom = AlignStart
  top = AlignEnd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll animation behavior when navigating to a step.
data ScrollBehavior
  = ScrollSmooth   -- ^ Animated scroll with easing
  | ScrollInstant  -- ^ Jump immediately without animation
  | ScrollNone     -- ^ Don't scroll (target may be off-screen)

derive instance eqScrollBehavior :: Eq ScrollBehavior
derive instance ordScrollBehavior :: Ord ScrollBehavior

instance showScrollBehavior :: Show ScrollBehavior where
  show = scrollBehaviorToString

instance boundedScrollBehavior :: Bounded ScrollBehavior where
  bottom = ScrollSmooth
  top = ScrollNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // scroll block
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertical scroll alignment (scrollIntoView block parameter).
-- |
-- | Controls where the target element is positioned vertically
-- | in the viewport after scrolling.
data ScrollBlock
  = BlockStart    -- ^ Align to top of viewport
  | BlockCenter   -- ^ Center in viewport
  | BlockEnd      -- ^ Align to bottom of viewport
  | BlockNearest  -- ^ Minimum scroll to make visible

derive instance eqScrollBlock :: Eq ScrollBlock
derive instance ordScrollBlock :: Ord ScrollBlock

instance showScrollBlock :: Show ScrollBlock where
  show BlockStart = "start"
  show BlockCenter = "center"
  show BlockEnd = "end"
  show BlockNearest = "nearest"

instance boundedScrollBlock :: Bounded ScrollBlock where
  bottom = BlockStart
  top = BlockNearest

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // scroll inline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Horizontal scroll alignment (scrollIntoView inline parameter).
-- |
-- | Controls where the target element is positioned horizontally
-- | in the viewport after scrolling.
data ScrollInline
  = InlineStart   -- ^ Align to left edge (start in LTR)
  | InlineCenter  -- ^ Center horizontally
  | InlineEnd     -- ^ Align to right edge (end in LTR)
  | InlineNearest -- ^ Minimum scroll to make visible

derive instance eqScrollInline :: Eq ScrollInline
derive instance ordScrollInline :: Ord ScrollInline

instance showScrollInline :: Show ScrollInline where
  show InlineStart = "start"
  show InlineCenter = "center"
  show InlineEnd = "end"
  show InlineNearest = "nearest"

instance boundedScrollInline :: Bounded ScrollInline where
  bottom = InlineStart
  top = InlineNearest

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert placement to CSS class suffix.
placementToString :: Placement -> String
placementToString = case _ of
  PlacementTop -> "top"
  PlacementTopStart -> "top-start"
  PlacementTopEnd -> "top-end"
  PlacementBottom -> "bottom"
  PlacementBottomStart -> "bottom-start"
  PlacementBottomEnd -> "bottom-end"
  PlacementLeft -> "left"
  PlacementLeftStart -> "left-start"
  PlacementLeftEnd -> "left-end"
  PlacementRight -> "right"
  PlacementRightStart -> "right-start"
  PlacementRightEnd -> "right-end"

-- | Convert scroll behavior to string for data attribute.
scrollBehaviorToString :: ScrollBehavior -> String
scrollBehaviorToString = case _ of
  ScrollSmooth -> "smooth"
  ScrollInstant -> "instant"
  ScrollNone -> "none"
