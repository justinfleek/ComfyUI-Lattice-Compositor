-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // element // tour
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour — The ULTIMATE product tour component.
-- |
-- | ## Overview
-- |
-- | A pure Element tour system with:
-- | - 50+ message types for complete control
-- | - Spring physics and morph animations
-- | - Multi-target spotlight with shape morphing
-- | - Branching paths with merge points
-- | - Accessibility-first design (WCAG 2.1 AA)
-- | - Reduced motion respect
-- | - Persistence (localStorage/sessionStorage)
-- | - Analytics events
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Tour as Tour
-- |
-- | myTour :: forall msg. (Tour.TourMsg -> msg) -> Tour.Element msg
-- | myTour wrapMsg =
-- |   Tour.tour
-- |     [ Tour.steps
-- |         [ Tour.step
-- |             { id: Tour.stepId "welcome"
-- |             , target: Tour.noTarget
-- |             , title: "Welcome!"
-- |             , content: "Let's get you started."
-- |             }
-- |         , Tour.step
-- |             { id: Tour.stepId "sidebar"
-- |             , target: Tour.bySelector ".sidebar"
-- |             , title: "Navigation"
-- |             , content: "Use the sidebar to navigate."
-- |             }
-- |         ]
-- |     , Tour.onNext (wrapMsg Tour.NextStep)
-- |     , Tour.onPrev (wrapMsg Tour.PrevStep)
-- |     , Tour.onSkip (wrapMsg Tour.SkipTour)
-- |     ]
-- | ```
-- |
-- | ## Architecture
-- |
-- | Tours are pure data. The component produces `Element msg` which runtime
-- | targets interpret. State changes flow through `TourMsg` messages.
-- |
-- | ```
-- | TourConfig → Element msg
-- |     ↓
-- | Runtime (DOM/Canvas/WebGL)
-- |     ↓
-- | User Interaction → TourMsg → State Update
-- | ```
-- |
-- | ## Modules
-- |
-- | | Module           | Purpose                                |
-- | |------------------|----------------------------------------|
-- | | Tour.Types       | Core atoms (StepId, Placement, etc.)   |
-- | | Tour.Target      | Target selection strategies            |
-- | | Tour.Highlight   | Spotlight and overlay styles           |
-- | | Tour.Animation   | Transitions, easing, spring physics    |
-- | | Tour.Navigation  | Progress indicators and buttons        |
-- | | Tour.Content     | Step content types                     |
-- | | Tour.Msg         | Complete message algebra               |
-- | | Tour.Motion      | Motion design presets                  |
-- |
-- | ## CSS Custom Properties
-- |
-- | ```css
-- | /* Overlay */
-- | --tour-overlay-color: rgba(0, 0, 0, 0.5);
-- | --tour-overlay-blur: 0px;
-- |
-- | /* Tooltip */
-- | --tour-tooltip-bg: var(--popover);
-- | --tour-tooltip-fg: var(--popover-foreground);
-- | --tour-tooltip-border: var(--border);
-- | --tour-tooltip-shadow: 0 4px 12px rgba(0, 0, 0, 0.15);
-- | --tour-tooltip-radius: 8px;
-- | --tour-tooltip-max-width: 320px;
-- |
-- | /* Spotlight */
-- | --tour-spotlight-padding: 4px;
-- | --tour-spotlight-radius: 4px;
-- |
-- | /* Progress */
-- | --tour-progress-color: var(--primary);
-- | --tour-progress-bg: var(--muted);
-- |
-- | /* Animation */
-- | --tour-duration: 300ms;
-- | --tour-easing: cubic-bezier(0.22, 1.0, 0.36, 1.0);
-- | ```
-- |
-- | ## Keyboard Shortcuts
-- |
-- | | Key       | Action          |
-- | |-----------|-----------------|
-- | | Escape    | Close tour      |
-- | | ArrowRight| Next step       |
-- | | ArrowLeft | Previous step   |
-- | | Enter     | Confirm/Next    |
-- | | Tab       | Focus trap      |

module Hydrogen.Element.Compound.Tour
  ( -- * Component (defined in this module)
    tour
  , debugTourState
  
  -- * Re-exports: Types
  , module ReexportTypes
  
  -- * Re-exports: Target
  , module ReexportTarget
  
  -- * Re-exports: Highlight
  , module ReexportHighlight
  
  -- * Re-exports: Animation
  , module ReexportAnimation
  
  -- * Re-exports: Navigation
  , module ReexportNavigation
  
  -- * Re-exports: Content
  , module ReexportContent
  
  -- * Re-exports: Msg
  , module ReexportMsg
  
  -- * Re-exports: Motion
  , module ReexportMotion
  
  -- * Re-exports: Props (types and defaults)
  , module ReexportProps
  
  -- * Re-exports: Builders (prop builders and target builders)
  , module ReexportBuilders
  
  -- * Re-exports: Render (tourWithState)
  , module ReexportRender
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude (class Show, show, (<>))

import Data.Array (foldl, length) as Array

import Hydrogen.Render.Element as E

-- Submodules for re-export
import Hydrogen.Element.Compound.Tour.Types
  ( StepId
  , stepId
  , unwrapStepId
  , TourId
  , tourId
  , unwrapTourId
  , StepIndex
  , stepIndex
  , unwrapStepIndex
  , firstStepIndex
  , nextStepIndex
  , prevStepIndex
  , Side
      ( SideTop
      , SideRight
      , SideBottom
      , SideLeft
      )
  , oppositeSide
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
  , PlacementAuto
      ( AutoBest
      , AutoVertical
      , AutoHorizontal
      , AutoClockwise
      , AutoCounterclockwise
      , AutoFlip
      , AutoFixed
      )
  , Alignment
      ( AlignStart
      , AlignCenter
      , AlignEnd
      )
  , ScrollBehavior
      ( ScrollSmooth
      , ScrollInstant
      , ScrollNone
      )
  , scrollBehaviorToString
  , ScrollBlock
      ( BlockStart
      , BlockCenter
      , BlockEnd
      , BlockNearest
      )
  , ScrollInline
      ( InlineStart
      , InlineCenter
      , InlineEnd
      , InlineNearest
      )
  ) as ReexportTypes

import Hydrogen.Element.Compound.Tour.Target
  ( TargetKind
      ( TargetSelector
      , TargetRef
      , TargetRect
      , TargetVirtual
      , TargetBeacon
      , TargetViewport
      , TargetMultiple
      )
  , Selector
  , selector
  , unwrapSelector
  , TargetRect
  , targetRect
  , rectX
  , rectY
  , rectWidth
  , rectHeight
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
  , WaitStrategy
      ( WaitImmediate
      , WaitVisible
      , WaitInViewport
      , WaitInteractive
      , WaitStable
      , WaitCustom
      )
  , WaitTimeout
  , waitTimeout
  , unwrapWaitTimeout
  , defaultWaitTimeout
  , noTimeout
  , TargetConfig
  , defaultTargetConfig
  ) as ReexportTarget

import Hydrogen.Element.Compound.Tour.Highlight
  ( HighlightKind
      ( HighlightSpotlight
      , HighlightOutline
      , HighlightGlow
      , HighlightOverlay
      , HighlightNone
      )
  , SpotlightShape
      ( ShapeRect
      , ShapeRoundedRect
      , ShapeCircle
      , ShapeEllipse
      , ShapePill
      , ShapeInset
      , ShapeCustomPath
      )
  , OverlayStyle
      ( OverlaySolid
      , OverlayBlur
      , OverlayGradient
      , OverlayPattern
      , OverlayNone
      )
  , PulseAnimation
      ( PulseNone
      , PulseRing
      , PulseGlow
      , PulseScale
      , PulseBounce
      , PulseShake
      , PulseBreathing
      )
  , GlowStyle
      ( GlowNone
      , GlowSoft
      , GlowStrong
      , GlowNeon
      , GlowPulsing
      )
  , BorderStyle
      ( BorderNone
      , BorderSolid
      , BorderDashed
      , BorderDotted
      , BorderAnimated
      , BorderGradient
      )
  , Opacity
  , opacity
  , unwrapOpacity
  , opaque
  , transparent
  , semiTransparent
  , CornerRadius
  , cornerRadius
  , unwrapCornerRadius
  , sharpCorners
  , roundedCorners
  , pillCorners
  , HighlightConfig
  , defaultHighlightConfig
  , spotlightConfig
  , outlineConfig
  , glowConfig
  , noHighlightConfig
  ) as ReexportHighlight

import Hydrogen.Element.Compound.Tour.Animation
  ( TransitionKind
      ( TransitionNone
      , TransitionFade
      , TransitionSlide
      , TransitionZoom
      , TransitionFlip
      , TransitionMorph
      , TransitionCrossfade
      )
  , EasingCurve
      ( EaseLinear
      , EaseIn
      , EaseOut
      , EaseInOut
      , EaseInQuad
      , EaseOutQuad
      , EaseInOutQuad
      , EaseInCubic
      , EaseOutCubic
      , EaseInOutCubic
      , EaseInQuart
      , EaseOutQuart
      , EaseInOutQuart
      , EaseInExpo
      , EaseOutExpo
      , EaseInOutExpo
      , EaseInBack
      , EaseOutBack
      , EaseInOutBack
      , EaseInBounce
      , EaseOutBounce
      , EaseInOutBounce
      , EaseSpring
      , EaseCustom
      )
  , easingToCss
  , EntranceKind
      ( EnterFade
      , EnterSlideUp
      , EnterSlideDown
      , EnterSlideLeft
      , EnterSlideRight
      , EnterZoomIn
      , EnterFlipX
      , EnterFlipY
      , EnterPop
      , EnterNone
      )
  , ExitKind
      ( ExitFade
      , ExitSlideUp
      , ExitSlideDown
      , ExitSlideLeft
      , ExitSlideRight
      , ExitZoomOut
      , ExitFlipX
      , ExitFlipY
      , ExitPop
      , ExitNone
      )
  , Duration
  , duration
  , unwrapDuration
  , instant
  , fast
  , normal
  , slow
  , verySlow
  , Delay
  , delay
  , unwrapDelay
  , noDelay
  , shortDelay
  , mediumDelay
  , longDelay
  , SpringConfig
  , springConfig
  , defaultSpring
  , bouncySpring
  , stiffSpring
  , gentleSpring
  , AnimationConfig
  , defaultAnimationConfig
  , fastAnimationConfig
  , slowAnimationConfig
  , noAnimationConfig
  ) as ReexportAnimation

import Hydrogen.Element.Compound.Tour.Navigation
  ( NavigationStyle
      ( NavMinimal
      , NavStandard
      , NavExpanded
      , NavCompact
      , NavFloating
      , NavDocked
      , NavHidden
      )
  , ProgressStyle
      ( ProgressNone
      , ProgressDots
      , ProgressBar
      , ProgressNumbers
      , ProgressFraction
      , ProgressSteps
      , ProgressCircle
      )
  , ButtonPosition
      ( ButtonInTooltip
      , ButtonBelowTooltip
      , ButtonFooter
      , ButtonFloating
      , ButtonInline
      )
  , ButtonVariant
      ( VariantPrimary
      , VariantSecondary
      , VariantGhost
      , VariantLink
      , VariantOutline
      , VariantIcon
      )
  , CloseMode
      ( CloseButton
      , CloseOverlayClick
      , CloseEscape
      , CloseAny
      , CloseNone
      )
  , SkipMode
      ( SkipAlways
      , SkipAfterSteps
      , SkipNever
      , SkipOnlyLast
      )
  , KeyboardKey
      ( KeyArrowRight
      , KeyArrowLeft
      , KeyArrowUp
      , KeyArrowDown
      , KeyEnter
      , KeySpace
      , KeyEscape
      , KeyTab
      , KeyHome
      , KeyEnd
      , KeyN
      , KeyP
      )
  , NavigationLabels
  , defaultLabels
  , minimalLabels
  , KeyboardConfig
  , defaultKeyboardConfig
  , arrowKeyConfig
  , vimKeyConfig
  , disabledKeyboardConfig
  , NavigationConfig
  , defaultNavigationConfig
  , minimalNavigationConfig
  , expandedNavigationConfig
  ) as ReexportNavigation

import Hydrogen.Element.Compound.Tour.Content
  ( ContentKind
      ( ContentText
      , ContentRichText
      , ContentMedia
      , ContentInteractive
      , ContentChecklist
      , ContentVideo
      , ContentCode
      , ContentCustom
      )
  , MediaType
      ( MediaImage
      , MediaGif
      , MediaVideo
      , MediaLottie
      , MediaRive
      , MediaSvg
      )
  , InteractiveKind
      ( InteractiveClick
      , InteractiveInput
      , InteractiveSelect
      , InteractiveToggle
      , InteractiveHotspot
      , InteractiveTask
      )
  , TooltipSize
      ( SizeAuto
      , SizeSmall
      , SizeMedium
      , SizeLarge
      , SizeFullWidth
      , SizeCustom
      )
  , sizeToMaxWidth
  -- Note: ContentAlign is NOT re-exported to avoid conflict with Types.Alignment
  -- Use Tour.Content.AlignLeft/AlignCenter/AlignRight directly
  , TextContent
  , textContent
  , withSubtitle
  , withDescription
  , MediaContent
  , imageContent
  , videoContent
  , gifContent
  , ChecklistItem
  , checklistItem
  , requiredItem
  , optionalItem
  , ContentConfig
  , defaultContentConfig
  , mediaContentConfig
  , interactiveContentConfig
  ) as ReexportContent

import Hydrogen.Element.Compound.Tour.Msg
  ( TourMsg
      ( NextStep
      , PrevStep
      , GoToStep
      , FirstStep
      , LastStep
      , SkipTour
      , SkipToEnd
      , StartTour
      , PauseTour
      , ResumeTour
      , CompleteTour
      , RestartTour
      , ResetTour
      , TargetFound
      , TargetLost
      , TargetReady
      , TargetTimeout
      , ScrollStart
      , ScrollComplete
      , ScrollError
      , HighlightShow
      , HighlightHide
      , HighlightClick
      , OverlayClick
      , TooltipShow
      , TooltipHide
      , TooltipFocus
      , TooltipBlur
      , TaskComplete
      , ChecklistItemToggle
      , InputChange
      , HotspotClick
      , KeyDown
      , FocusTrap
      , SwipeLeft
      , SwipeRight
      , PinchZoom
      , ProgressLoaded
      , ProgressSaved
      , ProgressCleared
      , TrackView
      , TrackInteraction
      , TrackComplete
      , TourError
      , Recover
      )
  ) as ReexportMsg

import Hydrogen.Element.Compound.Tour.Motion
  ( -- Spotlight Morphing
    MorphConfig
  , defaultMorphConfig
  , snappyMorphConfig
  , elasticMorphConfig
  , MorphPath(PathDirect, PathArc, PathBezier, PathAvoid, PathFollow)
  , MorphInterpolation(InterpolateDirect, InterpolateSmooth, InterpolateSuperellipse, InterpolateCorners)
  , ShapeInterpolation
  , interpolateRect
  , interpolateCircle
  , interpolatePill
  , computeMorphPath
  
  -- Tooltip Choreography
  , TooltipChoreography
  , MicroInteractionConfig
  , ChoreographyPhase(PhaseIdle, PhaseEntering, PhaseVisible, PhaseExiting, PhaseFollowing)
  , defaultChoreography
  , minimalChoreography
  , dramaticChoreography
  , defaultMicroInteractions
  , computeEntryAnimation
  , computeExitAnimation
  , computeFollowBehavior
  
  -- Progress Animations
  -- Note: ProgressAnimationStyle is NOT re-exported to avoid conflict with Navigation.ProgressStyle
  -- Use Tour.Motion.ProgressAnimationStyle directly for advanced animation configs
  , DotProgressConfig
  , BarProgressConfig
  , BarFillStyle(FillLinear, FillLiquid, FillElastic, FillGradient)
  , CircularProgressConfig
  , FlipCounterConfig
  , defaultDotProgress
  , liquidBarProgress
  , strokeCircularProgress
  , flipCounterConfig
  
  -- Attention Grabbers
  , AttentionPattern(AttentionPulse, AttentionBeacon, AttentionMagnetic, AttentionCelebration, AttentionNone)
  , PulseConfig
  , BeaconConfig
  , MagneticConfig
  , CelebrationConfig
  , gentlePulse
  , subtleBeacon
  , magneticPull
  , celebrationBurst
  
  -- Responsive Motion
  , MotionScale(MotionFull, MotionReduced, MotionMinimal, MotionNone)
  , ReducedMotionFallback
  , PerformanceTier(TierHigh, TierMedium, TierLow, TierMinimal)
  , computeMotionScale
  , reducedMotionFallbacks
  , performanceAdaptations
  
  -- Spring Physics
  -- Note: SpringParams and spring presets from Motion are NOT re-exported 
  -- to avoid conflict with Animation.SpringConfig
  -- Use Tour.Motion for advanced spring physics (SpringPreset, SpringParams)
  -- Use Tour.Animation for basic springs (SpringConfig, bouncySpring, etc.)
  , SpringPreset(Snappy, Bouncy, Smooth, Precise, Critical)
  , springToCss
  , springDuration
  
  -- Timing Curves
  , TimingCurve
  , organicEase
  , morphEase
  , tooltipEntryEase
  , tooltipExitEase
  , progressEase
  , attentionEase
  ) as ReexportMotion

-- Internal imports for debugTourState (ReexportX aliases don't provide unqualified access)
import Hydrogen.Element.Compound.Tour.Types (placementToString, unwrapStepIndex)

-- Import from split modules for re-export
import Hydrogen.Element.Compound.Tour.Props
  ( TourProps
  , TourProp
  , StepConfig
  , Step
  , defaultTourProps
  , defaultStepConfig
  , step
  ) as ReexportProps

import Hydrogen.Element.Compound.Tour.Builders
  ( steps
  , currentStepIndex
  , currentStepIndexRaw
  , pushHistory
  , goToNextStep
  , goToPrevStep
  , goToStep
  , isActive
  , onNext
  , onPrev
  , onSkip
  , onClose
  , onComplete
  , onStepChange
  , onStepChangeRaw
  , onKeyboardEvent
  , onProgressDotClick
  , showProgress
  , showOverlay
  , showNavigation
  , placement
  , scrollBehavior
  , keyboardEnabled
  , closeOnOverlayClick
  , closeOnEscape
  , persistKey
  , ariaLabel
  , announceSteps
  , className
  , overlayOpacity
  , spotlightPadding
  , noTarget
  , bySelector
  , byTestId
  , byId
  , byMultiple
  ) as ReexportBuilders

import Hydrogen.Element.Compound.Tour.Render
  ( tourWithState
  ) as ReexportRender

-- Internal imports for tour and debugTourState functions
-- (The ReexportX aliases are for module re-exports only)
import Hydrogen.Element.Compound.Tour.Props (TourProps, TourProp, defaultTourProps)
import Hydrogen.Element.Compound.Tour.Render (tourWithState)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Main tour component.
-- |
-- | Renders a complete tour with overlay, spotlight, tooltip, and navigation.
-- | Uses prop builders from Tour.Builders to configure behavior.
-- |
-- | Example:
-- | ```purescript
-- | tour
-- |   [ steps mySteps
-- |   , onNext (wrapMsg NextStep)
-- |   , onPrev (wrapMsg PrevStep)
-- |   , showProgress true
-- |   ]
-- | ```
tour :: forall msg. Array (TourProp msg) -> E.Element msg
tour propMods =
  let
    props = Array.foldl (\p f -> f p) defaultTourProps propMods
  in
    tourWithState props

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // debug
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debug representation of tour state.
-- |
-- | Uses Show instances to produce human-readable debug output.
-- | This is a debugging feature, not for production display.
debugTourState :: forall msg. Show msg => TourProps msg -> String
debugTourState props =
  "Tour { "
    <> "step: " <> show (unwrapStepIndex props.currentStepIndex)
    <> "/" <> show (Array.length props.steps)
    <> ", active: " <> show props.isActive
    <> ", history: " <> show (Array.length props.history) <> " steps"
    <> ", placement: " <> placementToString props.placement
    <> " }"

-- Note: Types, prop builders, target builders, and rendering logic have been
-- extracted to submodules for maintainability:
--   - Tour.Props: TourProps, TourProp, Step, StepConfig, defaults
--   - Tour.Builders: all prop builder functions, target builders
--   - Tour.Render: tourWithState and all rendering helpers
-- These are re-exported above via module re-exports.
