-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // tour // builders
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour prop builder functions.
-- |
-- | Provides a fluent API for configuring tour properties.

module Hydrogen.Element.Compound.Tour.Builders
  ( -- * Step Navigation
    steps
  , currentStepIndex
  , currentStepIndexRaw
  , pushHistory
  , goToNextStep
  , goToPrevStep
  , goToStep
  , isActive
  
  -- * Event Handlers
  , onNext
  , onPrev
  , onSkip
  , onClose
  , onComplete
  , onStepChange
  , onStepChangeRaw
  , onKeyboardEvent
  , onProgressDotClick
  
  -- * Display Options
  , showProgress
  , showOverlay
  , showNavigation
  , placement
  
  -- * Behavior
  , scrollBehavior
  , keyboardEnabled
  , closeOnOverlayClick
  , closeOnEscape
  
  -- * Persistence
  , persistKey
  
  -- * Accessibility
  , ariaLabel
  , announceSteps
  
  -- * Styling
  , className
  , overlayOpacity
  , spotlightPadding
  
  -- * Target Builders
  , noTarget
  , bySelector
  , byTestId
  , byId
  , byMultiple
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (<>)
  , (<<<)
  )

import Data.Array (snoc) as Array
import Data.Maybe (Maybe(Just))

import Hydrogen.Element.Compound.Tour.Props
  ( TourProps
  , TourProp
  , Step
  )

import Hydrogen.Element.Compound.Tour.Types
  ( StepIndex
  , stepIndex
  , unwrapStepIndex
  , nextStepIndex
  , prevStepIndex
  , Placement
  , ScrollBehavior
  )

import Hydrogen.Element.Compound.Tour.Target
  ( TargetKind(TargetSelector, TargetViewport, TargetMultiple)
  , Selector
  , selector
  )

import Hydrogen.Element.Compound.Tour.Highlight
  ( Opacity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // step builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set tour steps.
steps :: forall msg. Array Step -> TourProp msg
steps s props = props { steps = s }

-- | Set current step index (bounded).
currentStepIndex :: forall msg. StepIndex -> TourProp msg
currentStepIndex idx props = props { currentStepIndex = idx }

-- | Set current step index from raw Int (validates to non-negative).
currentStepIndexRaw :: forall msg. Int -> TourProp msg
currentStepIndexRaw idx props = props { currentStepIndex = stepIndex idx }

-- | Add a step to navigation history (for back button support).
pushHistory :: forall msg. StepIndex -> TourProp msg
pushHistory idx props = props { history = Array.snoc props.history idx }

-- | Set active state.
isActive :: forall msg. Boolean -> TourProp msg
isActive a props = props { isActive = a }

-- | Advance to next step, recording current in history.
goToNextStep :: forall msg. TourProp msg
goToNextStep props = props 
  { currentStepIndex = nextStepIndex props.currentStepIndex
  , history = Array.snoc props.history props.currentStepIndex
  }

-- | Go to previous step using history if available.
goToPrevStep :: forall msg. TourProp msg
goToPrevStep props = props
  { currentStepIndex = prevStepIndex props.currentStepIndex
  }

-- | Jump to specific step.
goToStep :: forall msg. StepIndex -> TourProp msg
goToStep idx props = props
  { currentStepIndex = idx
  , history = Array.snoc props.history props.currentStepIndex
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // event handlers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set next step handler.
onNext :: forall msg. msg -> TourProp msg
onNext m props = props { onNext = Just m }

-- | Set previous step handler.
onPrev :: forall msg. msg -> TourProp msg
onPrev m props = props { onPrev = Just m }

-- | Set skip handler.
onSkip :: forall msg. msg -> TourProp msg
onSkip m props = props { onSkip = Just m }

-- | Set close handler.
onClose :: forall msg. msg -> TourProp msg
onClose m props = props { onClose = Just m }

-- | Set completion handler.
onComplete :: forall msg. msg -> TourProp msg
onComplete m props = props { onComplete = Just m }

-- | Set step change handler (receives bounded StepIndex).
onStepChange :: forall msg. (StepIndex -> msg) -> TourProp msg
onStepChange f props = props { onStepChange = Just f }

-- | Set step change handler from raw Int (validates to non-negative).
onStepChangeRaw :: forall msg. (Int -> msg) -> TourProp msg
onStepChangeRaw f props = props { onStepChange = Just (f <<< unwrapStepIndex) }

-- | Set keyboard event handler.
onKeyboardEvent :: forall msg. (String -> msg) -> TourProp msg
onKeyboardEvent f props = props { onKeyboardEvent = Just f }

-- | Set progress dot click handler for direct step navigation.
onProgressDotClick :: forall msg. (StepIndex -> msg) -> TourProp msg
onProgressDotClick f props = props { onProgressDotClick = Just f }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // display options
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show/hide progress indicator.
showProgress :: forall msg. Boolean -> TourProp msg
showProgress s props = props { showProgress = s }

-- | Show/hide overlay.
showOverlay :: forall msg. Boolean -> TourProp msg
showOverlay s props = props { showOverlay = s }

-- | Show/hide navigation buttons.
showNavigation :: forall msg. Boolean -> TourProp msg
showNavigation s props = props { showNavigation = s }

-- | Set tooltip placement.
placement :: forall msg. Placement -> TourProp msg
placement p props = props { placement = p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set scroll behavior.
scrollBehavior :: forall msg. ScrollBehavior -> TourProp msg
scrollBehavior s props = props { scrollBehavior = s }

-- | Enable/disable keyboard navigation.
keyboardEnabled :: forall msg. Boolean -> TourProp msg
keyboardEnabled k props = props { keyboardEnabled = k }

-- | Close tour on overlay click.
closeOnOverlayClick :: forall msg. Boolean -> TourProp msg
closeOnOverlayClick c props = props { closeOnOverlayClick = c }

-- | Close tour on Escape key.
closeOnEscape :: forall msg. Boolean -> TourProp msg
closeOnEscape c props = props { closeOnEscape = c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // persistence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set localStorage key for persistence.
persistKey :: forall msg. String -> TourProp msg
persistKey k props = props { persistKey = Just k }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set accessible label.
ariaLabel :: forall msg. String -> TourProp msg
ariaLabel l props = props { ariaLabel = l }

-- | Announce step changes to screen readers.
announceSteps :: forall msg. Boolean -> TourProp msg
announceSteps a props = props { announceSteps = a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add custom CSS class.
className :: forall msg. String -> TourProp msg
className c props = props { className = props.className <> " " <> c }

-- | Set overlay opacity.
overlayOpacity :: forall msg. Opacity -> TourProp msg
overlayOpacity o props = props { overlayOpacity = o }

-- | Set spotlight padding.
spotlightPadding :: forall msg. Int -> TourProp msg
spotlightPadding p props = props { spotlightPadding = p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // target builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | No target (centered modal).
noTarget :: TargetKind
noTarget = TargetViewport

-- | Target by CSS selector.
bySelector :: String -> TargetKind
bySelector s = TargetSelector (selector s)

-- | Target by data-testid attribute.
byTestId :: String -> TargetKind
byTestId tid = TargetSelector (selector ("[data-testid=\"" <> tid <> "\"]"))

-- | Target by element ID.
byId :: String -> TargetKind
byId eid = TargetSelector (selector ("#" <> eid))

-- | Target multiple elements.
byMultiple :: Array String -> TargetKind
byMultiple sels = TargetMultiple (map selector sels)
