-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // tour // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour rendering components.
-- |
-- | Separates rendering logic from props configuration for modularity.
-- | All functions produce pure Element values.

module Hydrogen.Element.Compound.Tour.Render
  ( -- * Main Component
    tourWithState
  
  -- * Sub-components
  , tourOverlay
  , tourSpotlight
  , tourTooltip
  , tourArrow
  , tourProgress
  , progressDot
  , tourNavigation
  , tourAnnouncement
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , Unit
  , show
  , unit
  , (<>)
  , (+)
  , (-)
  , (==)
  , (>=)
  )

import Data.Array (length, index, mapWithIndex, cons) as Array
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.Tour.Props
  ( TourProps
  , Step
  )

import Hydrogen.Element.Compound.Tour.Types
  ( StepIndex
  , stepIndex
  , unwrapStepIndex
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
  , scrollBehaviorToString
  )

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
  , unwrapSelector
  )

import Hydrogen.Element.Compound.Tour.Highlight
  ( unwrapOpacity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tour component with explicit props.
tourWithState :: forall msg. TourProps msg -> E.Element msg
tourWithState props =
  let
    stepCount = Array.length props.steps
    currentInt = unwrapStepIndex props.currentStepIndex
    currentStep = Array.index props.steps currentInt
    isFirst = currentInt == 0
    isLast = currentInt >= stepCount - 1
    
    -- Keyboard handler (pure data — rendering target interprets)
    keyboardHandler = case props.onKeyboardEvent of
      Just handler -> [ E.onKeyDown handler ]
      Nothing -> []
  in
    if props.isActive then
      E.div_
        ( [ E.class_ ("tour-container fixed inset-0 z-50" <> props.className)
          , E.role "dialog"
          , E.ariaLabel props.ariaLabel
          , E.tabIndex 0
          , E.dataAttr "tour-active" "true"
          , E.dataAttr "tour-step" (show currentInt)
          , E.dataAttr "tour-total" (show stepCount)
          , E.dataAttr "keyboard-enabled" (show props.keyboardEnabled)
          , E.dataAttr "scroll-behavior" (scrollBehaviorToString props.scrollBehavior)
          ] <> keyboardHandler
        )
        [ -- Overlay
          if props.showOverlay then
            tourOverlay props
          else
            E.empty
        
        -- Spotlight (for targeted steps)
        , case currentStep of
            Just s -> tourSpotlight props s
            Nothing -> E.empty
        
        -- Tooltip
        , case currentStep of
            Just s -> tourTooltip props s isFirst isLast stepCount
            Nothing -> E.empty
        
        -- Screen reader announcements
        , if props.announceSteps then
            case currentStep of
              Just s -> tourAnnouncement props s stepCount
              Nothing -> E.empty
          else
            E.empty
        ]
    else
      E.empty

-- | Overlay backdrop.
tourOverlay :: forall msg. TourProps msg -> E.Element msg
tourOverlay props =
  let
    opacityValue = unwrapOpacity props.overlayOpacity
    clickHandler = case props.closeOnOverlayClick of
      true -> case props.onClose of
        Just handler -> [ E.onClick handler ]
        Nothing -> []
      false -> []
  in
    E.div_
      ( [ E.class_ "tour-overlay fixed inset-0 bg-black transition-opacity"
        , E.style "opacity" (show opacityValue)
        , E.ariaHidden true
        , E.dataAttr "tour-overlay" "true"
        ] <> clickHandler
      )
      []

-- | Spotlight cutout around target.
tourSpotlight :: forall msg. TourProps msg -> Step -> E.Element msg
tourSpotlight props s =
  let
    targetAttr = case s.config.target of
      TargetSelector sel -> E.dataAttr "target-selector" (unwrapSelector sel)
      TargetRef refName -> E.dataAttr "target-ref" refName
      TargetRect _ -> E.dataAttr "target-rect" "true"
      TargetVirtual _ -> E.dataAttr "target-virtual" "true"
      TargetBeacon beaconId -> E.dataAttr "target-beacon" beaconId
      TargetViewport -> E.dataAttr "target-viewport" "true"
      TargetMultiple _ -> E.dataAttr "target-multiple" "true"
  in
    E.div_
      [ E.class_ "tour-spotlight fixed pointer-events-none z-[55] transition-all"
      , targetAttr
      , E.dataAttr "spotlight-padding" (show props.spotlightPadding)
      , E.ariaHidden true
      ]
      []

-- | Tooltip with step content.
tourTooltip :: forall msg. TourProps msg -> Step -> Boolean -> Boolean -> Int -> E.Element msg
tourTooltip props s isFirst isLast stepCount =
  let
    placementClass = "tour-tooltip-" <> placementToString s.config.placement
  in
    E.div_
      [ E.class_ ("tour-tooltip fixed bg-popover text-popover-foreground rounded-lg shadow-lg border p-4 max-w-sm z-[60] " <> placementClass)
      , E.role "tooltip"
      , E.dataAttr "placement" (placementToString s.config.placement)
      ]
      [ -- Arrow
        tourArrow s.config.placement
      
      -- Title
      , E.h4_
          [ E.class_ "tour-tooltip-title font-semibold text-lg mb-2" ]
          [ E.text s.config.title ]
      
      -- Content
      , E.p_
          [ E.class_ "tour-tooltip-description text-sm text-muted-foreground mb-4" ]
          [ E.text s.config.content ]
      
      -- Progress
      , if props.showProgress then
          tourProgress props stepCount
        else
          E.empty
      
      -- Navigation
      , if props.showNavigation then
          tourNavigation props isFirst isLast
        else
          E.empty
      ]

-- | Tooltip arrow.
tourArrow :: forall msg. Placement -> E.Element msg
tourArrow p =
  let
    arrowClass = case p of
      PlacementTop -> "bottom-0 left-1/2 -translate-x-1/2 translate-y-1/2 rotate-45"
      PlacementTopStart -> "bottom-0 left-4 translate-y-1/2 rotate-45"
      PlacementTopEnd -> "bottom-0 right-4 translate-y-1/2 rotate-45"
      PlacementBottom -> "top-0 left-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45"
      PlacementBottomStart -> "top-0 left-4 -translate-y-1/2 rotate-45"
      PlacementBottomEnd -> "top-0 right-4 -translate-y-1/2 rotate-45"
      PlacementLeft -> "right-0 top-1/2 translate-x-1/2 -translate-y-1/2 rotate-45"
      PlacementLeftStart -> "right-0 top-4 translate-x-1/2 rotate-45"
      PlacementLeftEnd -> "right-0 bottom-4 translate-x-1/2 rotate-45"
      PlacementRight -> "left-0 top-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45"
      PlacementRightStart -> "left-0 top-4 -translate-x-1/2 rotate-45"
      PlacementRightEnd -> "left-0 bottom-4 -translate-x-1/2 rotate-45"
  in
    E.div_
      [ E.class_ ("tour-tooltip-arrow absolute w-3 h-3 bg-popover border-r border-b " <> arrowClass) ]
      []

-- | Progress indicator.
tourProgress :: forall msg. TourProps msg -> Int -> E.Element msg
tourProgress props total =
  let
    currentInt = unwrapStepIndex props.currentStepIndex
  in
    E.div_
      [ E.class_ "tour-progress flex items-center gap-1 mb-3"
      , E.ariaLabel ("Step " <> show (currentInt + 1) <> " of " <> show total)
      ]
      (Array.mapWithIndex (progressDot props currentInt) (replicate total))

-- | Single progress dot.
progressDot :: forall msg. TourProps msg -> Int -> Int -> Unit -> E.Element msg
progressDot props currentInt idx _ =
  let
    isActiveStep = idx == currentInt
    activeClass = if isActiveStep then "bg-primary w-3" else "bg-muted-foreground/50 w-2"
    
    clickHandler = case props.onProgressDotClick of
      Just handler -> 
        [ E.onClick (handler (stepIndex idx))
        , E.class_ "cursor-pointer"
        , E.role "button"
        , E.ariaLabel ("Go to step " <> show (idx + 1))
        ]
      Nothing -> []
  in
    E.div_
      ( [ E.class_ ("tour-progress-dot h-2 rounded-full transition-all " <> activeClass)
        , E.dataAttr "step-index" (show idx)
        ] <> clickHandler
      )
      []

-- | Navigation buttons.
tourNavigation :: forall msg. TourProps msg -> Boolean -> Boolean -> E.Element msg
tourNavigation props isFirst isLast =
  E.div_
    [ E.class_ "tour-navigation flex items-center justify-between gap-2" ]
    [ -- Skip button
      case props.onSkip of
        Just handler ->
          E.button_
            [ E.class_ "tour-skip px-3 py-1.5 text-sm text-muted-foreground hover:text-foreground transition-colors"
            , E.type_ "button"
            , E.onClick handler
            ]
            [ E.text "Skip" ]
        Nothing -> E.empty
    
    -- Spacer
    , E.div_ [ E.class_ "flex-1" ] []
    
    -- Previous button
    , if isFirst then
        E.empty
      else
        case props.onPrev of
          Just handler ->
            E.button_
              [ E.class_ "tour-prev px-3 py-1.5 text-sm rounded-md border border-input bg-background hover:bg-accent transition-colors"
              , E.type_ "button"
              , E.onClick handler
              ]
              [ E.text "Previous" ]
          Nothing -> E.empty
    
    -- Next/Complete button
    , if isLast then
        case props.onComplete of
          Just h ->
            E.button_
              [ E.class_ "tour-next px-3 py-1.5 text-sm rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
              , E.type_ "button"
              , E.onClick h
              ]
              [ E.text "Complete" ]
          Nothing -> E.empty
      else
        case props.onNext of
          Just h ->
            E.button_
              [ E.class_ "tour-next px-3 py-1.5 text-sm rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
              , E.type_ "button"
              , E.onClick h
              ]
              [ E.text "Next" ]
          Nothing -> E.empty
    ]

-- | Screen reader announcement.
tourAnnouncement :: forall msg. TourProps msg -> Step -> Int -> E.Element msg
tourAnnouncement props s total =
  let
    stepNum = show (unwrapStepIndex props.currentStepIndex + 1)
    totalStr = show total
  in
    E.div_
      [ E.class_ "sr-only"
      , E.role "status"
      , E.ariaLive "polite"
      , E.ariaAtomic "true"
      ]
      [ E.text ("Step " <> stepNum <> " of " <> totalStr <> ": " <> s.config.title <> ". " <> s.config.content) ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an array of units for mapping.
replicate :: Int -> Array Unit
replicate n = go n []
  where
    go 0 acc = acc
    go i acc = go (i - 1) (Array.cons unit acc)
