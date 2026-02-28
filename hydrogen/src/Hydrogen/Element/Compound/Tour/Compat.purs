-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // tour // compat
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Compat — Legacy types for backward compatibility.
-- |
-- | ## DEPRECATED
-- |
-- | This module provides backward compatibility with the original Tour API.
-- | New code should use the atomic types from:
-- | - `Tour.Types` — Core atoms
-- | - `Tour.Target` — Targeting
-- | - `Tour.Highlight` — Highlighting
-- | - `Tour.Animation` — Animations
-- | - `Tour.Navigation` — Navigation
-- | - `Tour.Content` — Content
-- | - `Tour.Msg` — Messages
-- |
-- | ## Migration
-- |
-- | Old: `Tour.step { target, title, content }`
-- | New: Use the new Step type from Tour.Step module (when implemented)

module Hydrogen.Element.Compound.Tour.Compat
  ( -- * Legacy Types
    Step
  , StepConfig
  , TourProps
  , TourProp
  , TooltipProps
  , TooltipProp
  , defaultProps
  , defaultTooltipProps
  
  -- * Legacy Step Builder
  , step
  , withPlacement
  , withOffset
  , withArrow
  , withHighlightPadding
  , withScrollMargin
  
  -- * Legacy Prop Builders - Tour
  , steps
  , currentStep
  , isActive
  , showProgress
  , showOverlay
  , overlayOpacity
  , allowClickThrough
  , scrollBehavior
  , persistKey
  , onStart
  , onStep
  , onComplete
  , onSkip
  , onStepChange
  , className
  
  -- * Legacy Prop Builders - Tooltip
  , placement
  , offset
  , tooltipClassName
  
  -- * Helpers
  , getStepAt
  , stepCount
  , isFirstStep
  , isLastStep
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  , (==)
  , (>=)
  , (-)
  )

import Data.Array (index, length) as Array
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Element.Compound.Tour.Types
  ( Placement
      ( PlacementBottom
      )
  , ScrollBehavior
      ( ScrollSmooth
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // legacy types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Step configuration — describes a single tour step.
-- |
-- | **DEPRECATED**: Use the new Step type from Tour.Step module.
type StepConfig =
  { target :: String          -- CSS selector for target element
  , title :: String           -- Step title
  , content :: String         -- Step description
  , placement :: Placement    -- Tooltip position
  , offset :: Int             -- Pixel offset from target
  , showArrow :: Boolean      -- Show tooltip arrow
  , highlightPadding :: Int   -- Padding around highlight
  , scrollMargin :: Int       -- Margin when scrolling into view
  }

-- | Tour step with configuration.
-- |
-- | **DEPRECATED**: Use the new Step type from Tour.Step module.
type Step = { config :: StepConfig }

-- | Tour properties.
-- |
-- | **DEPRECATED**: Use TourConfig from Tour.Config module.
type TourProps msg =
  { steps :: Array Step
  , currentStep :: Int
  , isActive :: Boolean
  , showProgress :: Boolean
  , showOverlay :: Boolean
  , overlayOpacity :: Number
  , allowClickThrough :: Boolean
  , scrollBehavior :: ScrollBehavior
  , persistKey :: Maybe String
  , onStart :: Maybe msg
  , onStep :: Maybe (Int -> msg)
  , onComplete :: Maybe msg
  , onSkip :: Maybe msg
  , onStepChange :: Maybe (Int -> msg)
  , className :: String
  }

-- | Tour property modifier.
type TourProp msg = TourProps msg -> TourProps msg

-- | Default tour properties.
defaultProps :: forall msg. TourProps msg
defaultProps =
  { steps: []
  , currentStep: 0
  , isActive: true
  , showProgress: true
  , showOverlay: true
  , overlayOpacity: 0.5
  , allowClickThrough: false
  , scrollBehavior: ScrollSmooth
  , persistKey: Nothing
  , onStart: Nothing
  , onStep: Nothing
  , onComplete: Nothing
  , onSkip: Nothing
  , onStepChange: Nothing
  , className: ""
  }

-- | Tooltip properties.
type TooltipProps =
  { placement :: Placement
  , offset :: Int
  , showArrow :: Boolean
  , className :: String
  }

-- | Tooltip property modifier.
type TooltipProp = TooltipProps -> TooltipProps

-- | Default tooltip properties.
defaultTooltipProps :: TooltipProps
defaultTooltipProps =
  { placement: PlacementBottom
  , offset: 8
  , showArrow: true
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // step builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a tour step with required fields.
-- |
-- | **DEPRECATED**: Use the new step builders from Tour.Step module.
step :: { target :: String, title :: String, content :: String } -> Step
step cfg =
  { config:
      { target: cfg.target
      , title: cfg.title
      , content: cfg.content
      , placement: PlacementBottom
      , offset: 8
      , showArrow: true
      , highlightPadding: 4
      , scrollMargin: 20
      }
  }

-- | Set step placement.
withPlacement :: Placement -> Step -> Step
withPlacement p s = s { config = s.config { placement = p } }

-- | Set step offset.
withOffset :: Int -> Step -> Step
withOffset o s = s { config = s.config { offset = o } }

-- | Set whether to show arrow.
withArrow :: Boolean -> Step -> Step
withArrow a s = s { config = s.config { showArrow = a } }

-- | Set highlight padding.
withHighlightPadding :: Int -> Step -> Step
withHighlightPadding p s = s { config = s.config { highlightPadding = p } }

-- | Set scroll margin.
withScrollMargin :: Int -> Step -> Step
withScrollMargin m s = s { config = s.config { scrollMargin = m } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders - tour
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set tour steps.
steps :: forall msg. Array Step -> TourProp msg
steps s props = props { steps = s }

-- | Set current step index.
currentStep :: forall msg. Int -> TourProp msg
currentStep s props = props { currentStep = s }

-- | Set active state.
isActive :: forall msg. Boolean -> TourProp msg
isActive a props = props { isActive = a }

-- | Show progress indicator.
showProgress :: forall msg. Boolean -> TourProp msg
showProgress s props = props { showProgress = s }

-- | Show backdrop overlay.
showOverlay :: forall msg. Boolean -> TourProp msg
showOverlay s props = props { showOverlay = s }

-- | Set overlay opacity (0.0 to 1.0).
overlayOpacity :: forall msg. Number -> TourProp msg
overlayOpacity o props = props { overlayOpacity = o }

-- | Allow clicking through overlay to underlying content.
allowClickThrough :: forall msg. Boolean -> TourProp msg
allowClickThrough a props = props { allowClickThrough = a }

-- | Set scroll behavior when navigating steps.
scrollBehavior :: forall msg. ScrollBehavior -> TourProp msg
scrollBehavior s props = props { scrollBehavior = s }

-- | Set localStorage key for persisting progress.
persistKey :: forall msg. String -> TourProp msg
persistKey k props = props { persistKey = Just k }

-- | Set handler for tour start.
onStart :: forall msg. msg -> TourProp msg
onStart handler props = props { onStart = Just handler }

-- | Set handler for step changes (receives step index).
onStep :: forall msg. (Int -> msg) -> TourProp msg
onStep handler props = props { onStep = Just handler }

-- | Set handler for tour completion.
onComplete :: forall msg. msg -> TourProp msg
onComplete handler props = props { onComplete = Just handler }

-- | Set handler for tour skip.
onSkip :: forall msg. msg -> TourProp msg
onSkip handler props = props { onSkip = Just handler }

-- | Set handler for step navigation (receives target step index).
onStepChange :: forall msg. (Int -> msg) -> TourProp msg
onStepChange handler props = props { onStepChange = Just handler }

-- | Add custom CSS class.
className :: forall msg. String -> TourProp msg
className c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders - tooltip
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set tooltip placement.
placement :: Placement -> TooltipProp
placement p props = props { placement = p }

-- | Set tooltip offset.
offset :: Int -> TooltipProp
offset o props = props { offset = o }

-- | Add custom class to tooltip.
tooltipClassName :: String -> TooltipProp
tooltipClassName c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get step at index.
getStepAt :: Int -> Array Step -> Maybe Step
getStepAt idx arr = Array.index arr idx

-- | Get total step count.
stepCount :: Array Step -> Int
stepCount = Array.length

-- | Check if at first step.
isFirstStep :: Int -> Boolean
isFirstStep idx = idx == 0

-- | Check if at last step.
isLastStep :: Int -> Array Step -> Boolean
isLastStep idx stps = idx >= Array.length stps - 1
