-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // tour // step
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Step configuration for Product Tours
-- |
-- | This module provides the Step type and related configuration for defining
-- | individual tour steps. Each step specifies:
-- | - What element to highlight (target)
-- | - What content to display (title, body, buttons)
-- | - Where to position the tooltip (placement)
-- | - How the step behaves (highlight style, wait conditions)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Step as Step
-- | import Hydrogen.Tour.Types as T
-- |
-- | welcomeStep :: Step.Step MyMsg
-- | welcomeStep = Step.step (T.mkStepId "welcome")
-- |   [ Step.target (T.ByTestId (T.mkTestId "welcome-button"))
-- |   , Step.title "Welcome to the app"
-- |   , Step.body "Let's take a quick tour of the main features."
-- |   , Step.placement T.Bottom T.Center
-- |   , Step.buttons
-- |       [ Step.nextButton "Get Started"
-- |       , Step.skipButton "Skip Tour"
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Tour.Step
  ( -- * Step Type
    Step
  , PlacementConfig
  , defaultPlacementConfig
  , step
  , stepId
    -- * Step Configuration
  , StepProp
  , target
  , title
  , body
  , placement
  , placementWithOffset
  , buttons
  , arrow
  , noArrow
  , highlight
  , scrollIntoView
  , noScroll
    -- * Button Configuration
  , Button
  , ButtonAction(..)
  , ButtonVariant(..)
  , button
  , nextButton
  , prevButton
  , skipButton
  , completeButton
  , customButton
    -- * Highlight Configuration
  , HighlightConfig
  , defaultHighlight
  , highlightPadding
  , highlightRadius
    -- * Scroll Configuration
  , ScrollConfig
  , defaultScroll
  , scrollBehavior
  , ScrollBehavior(..)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Tour.Types (Alignment, Milliseconds(Milliseconds), Pixel(Pixel), Placement, Side, StepId, Target(NoTarget), defaultPlacement, mkPlacement)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // step type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single step in a product tour
-- |
-- | Steps are the atomic units of a tour. Each step defines what to show
-- | the user and how they can proceed.
type Step msg =
  { id :: StepId
    -- ^ Unique identifier for this step
  , target :: Target
    -- ^ Element to highlight (or NoTarget for modal)
  , title :: Maybe String
    -- ^ Step heading
  , body :: Maybe String
    -- ^ Step body text
  , placement :: PlacementConfig
    -- ^ Tooltip positioning
  , buttons :: Array (Button msg)
    -- ^ Action buttons
  , showArrow :: Boolean
    -- ^ Whether to show pointer arrow
  , highlight :: HighlightConfig
    -- ^ Spotlight/highlight configuration
  , scroll :: Maybe ScrollConfig
    -- ^ Auto-scroll configuration
  }

-- | Placement configuration with offset
type PlacementConfig =
  { preferred :: Placement
  , offsetMain :: Pixel
    -- ^ Distance from target (perpendicular to edge)
  , offsetCross :: Pixel
    -- ^ Offset along the edge
  }

-- | Create a step with the given ID and configuration
step :: forall msg. StepId -> Array (StepProp msg) -> Step msg
step id props = foldl (\s f -> f s) defaultStep props
  where
  defaultStep :: Step msg
  defaultStep =
    { id
    , target: NoTarget
    , title: Nothing
    , body: Nothing
    , placement: defaultPlacementConfig
    , buttons: []
    , showArrow: true
    , highlight: defaultHighlight
    , scroll: Just defaultScroll
    }

-- | Extract the step ID
stepId :: forall msg. Step msg -> StepId
stepId s = s.id

-- | Default placement configuration
defaultPlacementConfig :: PlacementConfig
defaultPlacementConfig =
  { preferred: defaultPlacement
  , offsetMain: Pixel 12
  , offsetCross: Pixel 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // step configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Step property modifier
type StepProp msg = Step msg -> Step msg

-- | Set the target element
target :: forall msg. Target -> StepProp msg
target t s = s { target = t }

-- | Set the step title
title :: forall msg. String -> StepProp msg
title t s = s { title = Just t }

-- | Set the step body text
body :: forall msg. String -> StepProp msg
body b s = s { body = Just b }

-- | Set tooltip placement
placement :: forall msg. Side -> Alignment -> StepProp msg
placement side align s = s { placement = s.placement { preferred = mkPlacement side align } }

-- | Set placement with offset
placementWithOffset :: forall msg. Side -> Alignment -> Pixel -> Pixel -> StepProp msg
placementWithOffset side align main cross s = s
  { placement =
      { preferred: mkPlacement side align
      , offsetMain: main
      , offsetCross: cross
      }
  }

-- | Set the buttons for this step
buttons :: forall msg. Array (Button msg) -> StepProp msg
buttons bs s = s { buttons = bs }

-- | Show arrow pointer (default)
arrow :: forall msg. StepProp msg
arrow s = s { showArrow = true }

-- | Hide arrow pointer
noArrow :: forall msg. StepProp msg
noArrow s = s { showArrow = false }

-- | Set highlight configuration
highlight :: forall msg. HighlightConfig -> StepProp msg
highlight h s = s { highlight = h }

-- | Enable scroll into view (default)
scrollIntoView :: forall msg. ScrollConfig -> StepProp msg
scrollIntoView cfg s = s { scroll = Just cfg }

-- | Disable auto-scroll
noScroll :: forall msg. StepProp msg
noScroll s = s { scroll = Nothing }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // button configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button in a tour step
type Button msg =
  { label :: String
  , action :: ButtonAction msg
  , variant :: ButtonVariant
  }

-- | What happens when a button is clicked
data ButtonAction msg
  = ActionNext
    -- ^ Advance to next step
  | ActionPrev
    -- ^ Go to previous step
  | ActionSkip
    -- ^ Skip/dismiss the tour
  | ActionComplete
    -- ^ Complete the tour (from any step)
  | ActionGoTo StepId
    -- ^ Jump to a specific step
  | ActionCustom msg
    -- ^ Emit a custom message

derive instance functorButtonAction :: Functor ButtonAction

-- | Visual style of a button
data ButtonVariant
  = Primary
    -- ^ Prominent action (usually "Next")
  | Secondary
    -- ^ Less prominent action
  | Text
    -- ^ Text-only, minimal style (e.g., "Skip")

derive instance eqButtonVariant :: Eq ButtonVariant

-- | Create a button with full configuration
button :: forall msg. String -> ButtonAction msg -> ButtonVariant -> Button msg
button label action variant = { label, action, variant }

-- | Create a "Next" button
nextButton :: forall msg. String -> Button msg
nextButton label = button label ActionNext Primary

-- | Create a "Previous" button
prevButton :: forall msg. String -> Button msg
prevButton label = button label ActionPrev Secondary

-- | Create a "Skip" button
skipButton :: forall msg. String -> Button msg
skipButton label = button label ActionSkip Text

-- | Create a "Complete" / "Done" button
completeButton :: forall msg. String -> Button msg
completeButton label = button label ActionComplete Primary

-- | Create a button that emits a custom message
customButton :: forall msg. String -> msg -> ButtonVariant -> Button msg
customButton label msg variant = button label (ActionCustom msg) variant

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // highlight configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for element highlighting (spotlight)
type HighlightConfig =
  { padding :: Pixel
    -- ^ Space between element and cutout edge
  , borderRadius :: Pixel
    -- ^ Corner radius of the cutout
  , transitionDuration :: Milliseconds
    -- ^ Duration for morph transitions
  }

-- | Default highlight configuration
defaultHighlight :: HighlightConfig
defaultHighlight =
  { padding: Pixel 8
  , borderRadius: Pixel 4
  , transitionDuration: Milliseconds 300
  }

-- | Set highlight padding
highlightPadding :: Pixel -> HighlightConfig -> HighlightConfig
highlightPadding p cfg = cfg { padding = p }

-- | Set highlight border radius
highlightRadius :: Pixel -> HighlightConfig -> HighlightConfig
highlightRadius r cfg = cfg { borderRadius = r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // scroll configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Auto-scroll behavior
data ScrollBehavior
  = Smooth
    -- ^ Animated smooth scroll
  | Instant
    -- ^ Immediate jump

derive instance eqScrollBehavior :: Eq ScrollBehavior

-- | Configuration for scrolling target into view
type ScrollConfig =
  { behavior :: ScrollBehavior
  , block :: String
    -- ^ Vertical alignment: "start", "center", "end", "nearest"
  , inline :: String
    -- ^ Horizontal alignment: "start", "center", "end", "nearest"
  }

-- | Default scroll configuration (smooth, center)
defaultScroll :: ScrollConfig
defaultScroll =
  { behavior: Smooth
  , block: "center"
  , inline: "nearest"
  }

-- | Set scroll behavior
scrollBehavior :: ScrollBehavior -> ScrollConfig -> ScrollConfig
scrollBehavior b cfg = cfg { behavior = b }
