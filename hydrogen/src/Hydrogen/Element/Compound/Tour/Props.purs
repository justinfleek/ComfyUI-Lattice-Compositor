-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // tour // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour property types and builders.
-- |
-- | Separates props configuration from rendering logic for modularity.

module Hydrogen.Element.Compound.Tour.Props
  ( -- * Types
    TourProps
  , TourProp
  , StepConfig
  , Step
  , defaultTourProps
  , defaultStepConfig
  , step
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Element.Compound.Tour.Types
  ( StepId
  , stepId
  , StepIndex
  , firstStepIndex
  , Placement(PlacementBottom)
  , ScrollBehavior(ScrollSmooth)
  )

import Hydrogen.Element.Compound.Tour.Target
  ( TargetKind(TargetViewport)
  )

import Hydrogen.Element.Compound.Tour.Highlight
  ( Opacity
  , semiTransparent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Step configuration for a single tour step.
type StepConfig =
  { id :: StepId
  , target :: TargetKind
  , title :: String
  , content :: String
  , placement :: Placement
  , spotlightPadding :: Int
  }

-- | Tour step.
type Step = { config :: StepConfig }

-- | Default step configuration.
defaultStepConfig :: StepConfig
defaultStepConfig =
  { id: stepId "step"
  , target: TargetViewport
  , title: ""
  , content: ""
  , placement: PlacementBottom
  , spotlightPadding: 8
  }

-- | Create a step from partial config.
step :: { id :: StepId, target :: TargetKind, title :: String, content :: String } -> Step
step cfg =
  { config:
      { id: cfg.id
      , target: cfg.target
      , title: cfg.title
      , content: cfg.content
      , placement: PlacementBottom
      , spotlightPadding: 8
      }
  }

-- | Tour properties.
-- |
-- | Uses bounded `StepIndex` instead of raw `Int` to prevent invalid states.
-- | Tracks `history` for back navigation support.
type TourProps msg =
  { steps :: Array Step
  , currentStepIndex :: StepIndex
  , history :: Array StepIndex
  , isActive :: Boolean
  
  -- Navigation handlers
  , onNext :: Maybe msg
  , onPrev :: Maybe msg
  , onSkip :: Maybe msg
  , onClose :: Maybe msg
  , onComplete :: Maybe msg
  , onStepChange :: Maybe (StepIndex -> msg)
  
  -- Keyboard handler
  , onKeyboardEvent :: Maybe (String -> msg)
  
  -- Progress dot click handler
  , onProgressDotClick :: Maybe (StepIndex -> msg)
  
  -- Display
  , showProgress :: Boolean
  , showOverlay :: Boolean
  , showNavigation :: Boolean
  , placement :: Placement
  
  -- Behavior
  , scrollBehavior :: ScrollBehavior
  , keyboardEnabled :: Boolean
  , closeOnOverlayClick :: Boolean
  , closeOnEscape :: Boolean
  
  -- Persistence
  , persistKey :: Maybe String
  
  -- Accessibility
  , ariaLabel :: String
  , announceSteps :: Boolean
  
  -- Styling
  , className :: String
  , overlayOpacity :: Opacity
  , spotlightPadding :: Int
  }

-- | Tour property modifier.
type TourProp msg = TourProps msg -> TourProps msg

-- | Default tour properties.
defaultTourProps :: forall msg. TourProps msg
defaultTourProps =
  { steps: []
  , currentStepIndex: firstStepIndex
  , history: []
  , isActive: true
  
  , onNext: Nothing
  , onPrev: Nothing
  , onSkip: Nothing
  , onClose: Nothing
  , onComplete: Nothing
  , onStepChange: Nothing
  , onKeyboardEvent: Nothing
  , onProgressDotClick: Nothing
  
  , showProgress: true
  , showOverlay: true
  , showNavigation: true
  , placement: PlacementBottom
  
  , scrollBehavior: ScrollSmooth
  , keyboardEnabled: true
  , closeOnOverlayClick: false
  , closeOnEscape: true
  
  , persistKey: Nothing
  
  , ariaLabel: "Product tour"
  , announceSteps: true
  
  , className: ""
  , overlayOpacity: semiTransparent
  , spotlightPadding: 8
  }
