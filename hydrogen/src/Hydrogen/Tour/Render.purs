-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // tour // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Element Render Functions for Product Tours
-- |
-- | This module provides pure render functions that output Hydrogen Elements.
-- | These are framework-agnostic and can be interpreted to any rendering target:
-- |
-- | - DOM (browser)
-- | - Static HTML (SSG)
-- | - Test harness
-- |
-- | ## Design Philosophy
-- |
-- | All render functions are pure functions producing Element values.
-- | No effects, no framework dependencies. Just data describing UI.
-- |
-- | Data attributes encode runtime behavior that the interpreter handles:
-- | - `data-tour-overlay` — Overlay identification
-- | - `data-tour-spotlight` — Spotlight positioning
-- | - `data-tour-tooltip` — Tooltip behavior
-- | - `data-reduced-motion` — Motion preference awareness
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Render as Render
-- |
-- | myOverlay :: Element TourMsg
-- | myOverlay = Render.tourOverlay
-- |   { closeOnClick: true
-- |   , blurBackground: true
-- |   , onClose: DismissTour ClickedOverlay
-- |   }
-- | ```
module Hydrogen.Tour.Render
  ( -- * Configuration Types
    OverlayConfig
  , SpotlightConfig
  , TooltipConfig
  , NavigationConfig
  , ProgressStyle(..)
  , ClickBehavior(..)
    -- * Render Functions
  , tourOverlay
  , tourSpotlight
  , tourTooltip
  , tourProgress
  , tourNavigation
  , tourArrow
    -- * Helper Functions
  , placementToClass
  , sideToRotation
  ) where

import Prelude
  ( class Eq
  , class Show
  , Unit
  , show
  , unit
  , map
  , otherwise
  , (<>)
  , (==)
  , (-)
  , (+)
  , (*)
  , (/)
  , (>)
  )

import Data.Array (mapWithIndex)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))
import Hydrogen.Render.Element
  ( Attribute
  , Element
  , ariaHidden
  , ariaLabel
  , class_
  , classes
  , dataAttr
  , disabled
  , div_
  , empty
  , g_
  , onClick
  , path_
  , role
  , span_
  , attr
  , style
  , svg_
  , button_
  , tabIndex
  , text
  )
import Hydrogen.Tour.Step (Button, ButtonAction(ActionComplete, ActionCustom, ActionGoTo, ActionNext, ActionPrev, ActionSkip), ButtonVariant(Primary, Secondary, Text))
import Hydrogen.Tour.Types (Alignment(Center, End, Start), Pixel(Pixel), Placement, Progress, Side(Bottom, Left, Right, Top), StepId, progressCurrent, progressTotal)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // configuration types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overlay click behavior
data ClickBehavior msg
  = AdvanceOnClick msg
    -- ^ Clicking advances to next step
  | CloseOnClick msg
    -- ^ Clicking closes the tour
  | BlockClick
    -- ^ Clicking does nothing (modal behavior)

derive instance eqClickBehavior :: Eq msg => Eq (ClickBehavior msg)

-- | Configuration for the overlay backdrop
type OverlayConfig msg =
  { clickBehavior :: ClickBehavior msg
    -- ^ What happens when overlay is clicked
  , blurBackground :: Boolean
    -- ^ Whether to apply blur effect
  , reducedMotion :: Boolean
    -- ^ Respect prefers-reduced-motion
  , overlayOpacity :: Number
    -- ^ Opacity of the overlay (0.0 to 1.0)
  }

-- | Configuration for the spotlight cutout
type SpotlightConfig =
  { targetRect :: { x :: Int, y :: Int, width :: Int, height :: Int }
    -- ^ Bounding box of the target element
  , padding :: Pixel
    -- ^ Extra space around the target
  , borderRadius :: Pixel
    -- ^ Corner radius of the cutout
  , pulseAnimation :: Boolean
    -- ^ Whether to show pulse effect
  , transitionDuration :: Int
    -- ^ Milliseconds for morph transition
  }

-- | Configuration for the tooltip
type TooltipConfig msg =
  { title :: Maybe String
    -- ^ Tooltip heading
  , body :: Maybe String
    -- ^ Tooltip body text
  , placement :: Placement
    -- ^ Positioning relative to target
  , showArrow :: Boolean
    -- ^ Whether to show pointing arrow
  , progress :: Maybe Progress
    -- ^ Progress through tour
  , progressStyle :: ProgressStyle
    -- ^ How to display progress
  , buttons :: Array (Button msg)
    -- ^ Navigation buttons
  , onClose :: msg
    -- ^ Message when close button clicked
  , onNext :: msg
    -- ^ Message for next step
  , onPrev :: msg
    -- ^ Message for previous step
  , onSkip :: msg
    -- ^ Message for skip tour
  , onComplete :: msg
    -- ^ Message for complete tour
  , onGoTo :: StepId -> msg
    -- ^ Message for go-to step
  , isFirstStep :: Boolean
    -- ^ Whether this is the first step
  , isLastStep :: Boolean
    -- ^ Whether this is the last step
  }

-- | Style for progress indicator
data ProgressStyle
  = ProgressDots
    -- ^ Dot indicators
  | ProgressBar
    -- ^ Horizontal bar
  | ProgressFraction
    -- ^ Text "2 of 5"
  | ProgressHidden
    -- ^ No progress shown

derive instance eqProgressStyle :: Eq ProgressStyle

instance showProgressStyle :: Show ProgressStyle where
  show ProgressDots = "ProgressDots"
  show ProgressBar = "ProgressBar"
  show ProgressFraction = "ProgressFraction"
  show ProgressHidden = "ProgressHidden"

-- | Configuration for navigation buttons
type NavigationConfig msg =
  { buttons :: Array (Button msg)
    -- ^ Buttons to render
  , showKeyboardHints :: Boolean
    -- ^ Show keyboard shortcut hints
  , isFirstStep :: Boolean
    -- ^ Disable prev on first step
  , isLastStep :: Boolean
    -- ^ Change next to complete on last step
  , onNext :: msg
    -- ^ Message for next action
  , onPrev :: msg
    -- ^ Message for prev action
  , onSkip :: msg
    -- ^ Message for skip action
  , onComplete :: msg
    -- ^ Message for complete action
  , onGoTo :: StepId -> msg
    -- ^ Message for go-to action
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semi-transparent backdrop overlay
-- |
-- | The overlay provides visual focus on the tour by dimming the background.
-- | Supports:
-- | - Click handling (advance, close, or blocked)
-- | - Blur effect via data attribute
-- | - Reduced motion awareness
tourOverlay :: forall msg. OverlayConfig msg -> Element msg
tourOverlay config =
  div_
    ( [ classes
          [ "fixed"
          , "inset-0"
          , "z-40"
          , "transition-opacity"
          , if config.reducedMotion then "" else "duration-300"
          ]
      , dataAttr "tour-overlay" "true"
      , dataAttr "blur-background" (if config.blurBackground then "true" else "false")
      , dataAttr "reduced-motion" (if config.reducedMotion then "true" else "false")
      , style "background-color" ("rgba(0, 0, 0, " <> show config.overlayOpacity <> ")")
      , ariaHidden true
      ] <> clickHandler config.clickBehavior
    )
    []
  where
  clickHandler :: ClickBehavior msg -> Array (Attribute msg)
  clickHandler = case _ of
    AdvanceOnClick msg -> [ onClick msg ]
    CloseOnClick msg -> [ onClick msg ]
    BlockClick -> []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // spotlight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spotlight cutout around the target element
-- |
-- | Creates a visual highlight by using a large box-shadow to create the
-- | overlay effect with a transparent cutout. The position is controlled
-- | via inline styles based on the target element's bounding box.
tourSpotlight :: forall msg. SpotlightConfig -> Element msg
tourSpotlight config =
  let
    Pixel padding = config.padding
    Pixel radius = config.borderRadius
    
    -- Calculate position with padding
    left = config.targetRect.x - padding
    top = config.targetRect.y - padding
    width = config.targetRect.width + (padding * 2)
    height = config.targetRect.height + (padding * 2)
    
    -- Box shadow creates the overlay effect with cutout
    boxShadowValue = 
      "0 0 0 9999px rgba(0, 0, 0, 0.75), " <>
      "inset 0 0 0 2px rgba(255, 255, 255, 0.1)"
  in
    div_
      [ classes
          [ "fixed"
          , "pointer-events-none"
          , "z-50"
          , "transition-all"
          , if config.transitionDuration > 0 then "ease-out" else ""
          ]
      , dataAttr "tour-spotlight" "true"
      , dataAttr "padding" (show padding)
      , dataAttr "radius" (show radius)
      , dataAttr "pulse" (if config.pulseAnimation then "true" else "false")
      , style "left" (show left <> "px")
      , style "top" (show top <> "px")
      , style "width" (show width <> "px")
      , style "height" (show height <> "px")
      , style "border-radius" (show radius <> "px")
      , style "box-shadow" boxShadowValue
      , style "transition-duration" (show config.transitionDuration <> "ms")
      ]
      [ -- Pulse animation ring (if enabled)
        if config.pulseAnimation
        then pulseRing radius
        else empty
      ]

-- | Pulse animation ring for spotlight
pulseRing :: forall msg. Int -> Element msg
pulseRing radius =
  div_
    [ classes
        [ "absolute"
        , "inset-0"
        , "animate-pulse"
        , "pointer-events-none"
        ]
    , style "border-radius" (show radius <> "px")
    , style "box-shadow" "0 0 0 4px rgba(59, 130, 246, 0.5)"
    , dataAttr "spotlight-pulse" "true"
    ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // tooltip
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete tooltip component
-- |
-- | Renders the tour step content including:
-- | - Title and body sections
-- | - Arrow pointing to target
-- | - Progress indicator
-- | - Navigation buttons
tourTooltip :: forall msg. TooltipConfig msg -> Element msg
tourTooltip config =
  div_
    [ classes
        [ "absolute"
        , "z-50"
        , "w-80"
        , "max-w-sm"
        , "rounded-lg"
        , "border"
        , "bg-popover"
        , "p-4"
        , "text-popover-foreground"
        , "shadow-lg"
        , "animate-in"
        , "fade-in-0"
        , "zoom-in-95"
        , "duration-200"
        , placementToClass config.placement
        ]
    , role "tooltip"
    , dataAttr "tour-tooltip" "true"
    , dataAttr "placement" (sideToString config.placement.side)
    , tabIndex 0
    , ariaLabel "Tour step"
    ]
    [ -- Arrow (if enabled)
      if config.showArrow
      then tourArrow config.placement
      else empty
    , -- Header section
      tooltipHeader config
    , -- Body section
      tooltipBody config.body
    , -- Footer with progress and navigation
      tooltipFooter config
    ]

-- | Tooltip header with title and close button
tooltipHeader :: forall msg. TooltipConfig msg -> Element msg
tooltipHeader config =
  div_
    [ class_ "flex items-start justify-between gap-2 mb-2" ]
    [ case config.title of
        Just t -> 
          div_
            [ class_ "font-semibold leading-none tracking-tight text-sm" ]
            [ text t ]
        Nothing -> empty
    , closeButton config.onClose
    ]

-- | Tooltip body text
tooltipBody :: forall msg. Maybe String -> Element msg
tooltipBody = case _ of
  Just b ->
    div_
      [ class_ "text-sm text-muted-foreground mb-4" ]
      [ text b ]
  Nothing -> empty

-- | Tooltip footer with progress and navigation
tooltipFooter :: forall msg. TooltipConfig msg -> Element msg
tooltipFooter config =
  div_
    [ class_ "flex items-center justify-between gap-2" ]
    [ -- Progress indicator
      case config.progress of
        Just p -> tourProgress (progressCurrent p) (progressTotal p) config.progressStyle
        Nothing -> empty
    , -- Navigation buttons
      tourNavigation
        { buttons: config.buttons
        , showKeyboardHints: false
        , isFirstStep: config.isFirstStep
        , isLastStep: config.isLastStep
        , onNext: config.onNext
        , onPrev: config.onPrev
        , onSkip: config.onSkip
        , onComplete: config.onComplete
        , onGoTo: config.onGoTo
        }
    ]

-- | Close button (X icon)
closeButton :: forall msg. msg -> Element msg
closeButton onClose =
  button_
    [ classes
        [ "rounded-sm"
        , "opacity-70"
        , "ring-offset-background"
        , "transition-opacity"
        , "hover:opacity-100"
        , "focus:outline-none"
        , "focus:ring-2"
        , "focus:ring-ring"
        , "focus:ring-offset-2"
        ]
    , attr "type" "button"
    , onClick onClose
    , ariaLabel "Close tour"
    ]
    [ closeIcon ]

-- | X icon for close button (SVG)
closeIcon :: forall msg. Element msg
closeIcon =
  svg_
    [ class_ "h-4 w-4"
    , attr "viewBox" "0 0 24 24"
    , attr "fill" "none"
    , attr "stroke" "currentColor"
    , attr "stroke-width" "2"
    , attr "stroke-linecap" "round"
    , attr "stroke-linejoin" "round"
    ]
    [ path_ [ attr "d" "M18 6L6 18" ]
    , path_ [ attr "d" "M6 6L18 18" ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress indicator
-- |
-- | Displays tour progress in one of three styles:
-- | - Dots: Visual dots for each step
-- | - Bar: Horizontal progress bar
-- | - Fraction: Text "2 of 5"
tourProgress :: forall msg. Int -> Int -> ProgressStyle -> Element msg
tourProgress current total progressStyle = case progressStyle of
  ProgressDots -> progressDots current total
  ProgressBar -> progressBar current total
  ProgressFraction -> progressFraction current total
  ProgressHidden -> empty

-- | Dot-style progress indicator
progressDots :: forall msg. Int -> Int -> Element msg
progressDots current total =
  div_
    [ class_ "flex items-center gap-1.5"
    , ariaLabel ("Step " <> show current <> " of " <> show total)
    , dataAttr "progress-style" "dots"
    ]
    (mapWithIndex renderDot (makeArray total))
  where
  renderDot :: Int -> Unit -> Element msg
  renderDot idx _ =
    div_
      [ classes
          [ "w-1.5"
          , "h-1.5"
          , "rounded-full"
          , "transition-colors"
          , if (idx + 1) == current then "bg-primary" else "bg-muted"
          ]
      , dataAttr "dot-index" (show idx)
      , dataAttr "dot-active" (if (idx + 1) == current then "true" else "false")
      ]
      []
  
  makeArray :: Int -> Array Unit
  makeArray n = map (\_ -> unit) (range 0 (n - 1))

-- | Bar-style progress indicator
progressBar :: forall msg. Int -> Int -> Element msg
progressBar current total =
  let
    percent = if total > 0 then (current * 100) / total else 0
  in
    div_
      [ class_ "flex-1 h-1.5 bg-muted rounded-full overflow-hidden"
      , ariaLabel ("Step " <> show current <> " of " <> show total)
      , dataAttr "progress-style" "bar"
      ]
      [ div_
          [ classes
              [ "h-full"
              , "bg-primary"
              , "transition-all"
              , "duration-300"
              , "ease-out"
              ]
          , style "width" (show percent <> "%")
          , dataAttr "progress-percent" (show percent)
          ]
          []
      ]

-- | Fraction-style progress indicator
progressFraction :: forall msg. Int -> Int -> Element msg
progressFraction current total =
  span_
    [ class_ "text-xs text-muted-foreground"
    , dataAttr "progress-style" "fraction"
    ]
    [ text (show current <> " of " <> show total) ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // navigation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Navigation buttons
-- |
-- | Renders the navigation button row with:
-- | - Back/Next/Skip/Close buttons
-- | - Optional keyboard shortcut hints
-- | - Disabled state handling for first/last steps
tourNavigation :: forall msg. NavigationConfig msg -> Element msg
tourNavigation config =
  div_
    [ class_ "flex items-center gap-2"
    , dataAttr "tour-navigation" "true"
    ]
    (map (renderButton config) config.buttons)

-- | Render a single navigation button
renderButton :: forall msg. NavigationConfig msg -> Button msg -> Element msg
renderButton config btn =
  let
    isDisabled = case btn.action of
      ActionPrev -> config.isFirstStep
      _ -> false
    
    keyboardHint = if config.showKeyboardHints
      then case btn.action of
        ActionNext -> Just "→"
        ActionPrev -> Just "←"
        ActionSkip -> Just "Esc"
        _ -> Nothing
      else Nothing
    
    msg = resolveAction config btn.action
  in
    button_
      [ classes (buttonClasses btn.variant <> [ if isDisabled then "opacity-50 cursor-not-allowed" else "" ])
      , attr "type" "button"
      , onClick msg
      , disabled isDisabled
      , dataAttr "button-action" (actionToString btn.action)
      ]
      [ text btn.label
      , case keyboardHint of
          Just hint -> 
            span_
              [ class_ "ml-1 text-xs opacity-60" ]
              [ text ("(" <> hint <> ")") ]
          Nothing -> empty
      ]

-- | Resolve button action to message using config handlers
resolveAction :: forall msg. NavigationConfig msg -> ButtonAction msg -> msg
resolveAction config = case _ of
  ActionNext -> config.onNext
  ActionPrev -> config.onPrev
  ActionSkip -> config.onSkip
  ActionComplete -> config.onComplete
  ActionGoTo sid -> config.onGoTo sid
  ActionCustom m -> m

-- | Convert action to string for data attribute
actionToString :: forall msg. ButtonAction msg -> String
actionToString = case _ of
  ActionNext -> "next"
  ActionPrev -> "prev"
  ActionSkip -> "skip"
  ActionComplete -> "complete"
  ActionGoTo _ -> "goto"
  ActionCustom _ -> "custom"

-- | CSS classes for button variants
buttonClasses :: ButtonVariant -> Array String
buttonClasses = case _ of
  Primary ->
    [ "inline-flex"
    , "items-center"
    , "justify-center"
    , "rounded-md"
    , "text-sm"
    , "font-medium"
    , "bg-primary"
    , "text-primary-foreground"
    , "hover:bg-primary/90"
    , "h-8"
    , "px-3"
    , "py-1"
    , "transition-colors"
    , "focus:outline-none"
    , "focus:ring-2"
    , "focus:ring-ring"
    , "focus:ring-offset-2"
    ]
  Secondary ->
    [ "inline-flex"
    , "items-center"
    , "justify-center"
    , "rounded-md"
    , "text-sm"
    , "font-medium"
    , "bg-secondary"
    , "text-secondary-foreground"
    , "hover:bg-secondary/80"
    , "h-8"
    , "px-3"
    , "py-1"
    , "transition-colors"
    , "focus:outline-none"
    , "focus:ring-2"
    , "focus:ring-ring"
    , "focus:ring-offset-2"
    ]
  Text ->
    [ "inline-flex"
    , "items-center"
    , "justify-center"
    , "rounded-md"
    , "text-sm"
    , "font-medium"
    , "text-muted-foreground"
    , "hover:text-foreground"
    , "hover:bg-accent"
    , "h-8"
    , "px-2"
    , "py-1"
    , "transition-colors"
    , "focus:outline-none"
    , "focus:ring-2"
    , "focus:ring-ring"
    , "focus:ring-offset-2"
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // arrow
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG arrow pointing toward target
-- |
-- | The arrow is rotated based on placement to always point toward
-- | the target element. Uses an SVG triangle.
tourArrow :: forall msg. Placement -> Element msg
tourArrow placement =
  let
    rotation = sideToRotation placement.side
    positionClasses = arrowPositionClasses placement
  in
    div_
      [ classes
          ([ "absolute"
          , "w-3"
          , "h-3"
          , "pointer-events-none"
          ] <> positionClasses)
      , dataAttr "tour-arrow" "true"
      , dataAttr "placement" (sideToString placement.side)
      ]
      [ svg_
          [ class_ "w-full h-full"
          , attr "viewBox" "0 0 12 12"
          , style "transform" ("rotate(" <> show rotation <> "deg)")
          ]
          [ -- Triangle path pointing up by default
            g_
              []
              [ path_
                  [ attr "d" "M6 0L12 12H0L6 0Z"
                  , attr "fill" "currentColor"
                  , class_ "text-popover"
                  ]
              , -- Border stroke
                path_
                  [ attr "d" "M6 1L11 11H1L6 1Z"
                  , attr "fill" "none"
                  , attr "stroke" "currentColor"
                  , attr "stroke-width" "1"
                  , class_ "text-border"
                  ]
              ]
          ]
      ]

-- | Get rotation degrees for arrow based on tooltip side
-- |
-- | Arrow points toward the target, so:
-- | - Tooltip on top → arrow points down (180°)
-- | - Tooltip on bottom → arrow points up (0°)
-- | - Tooltip on left → arrow points right (90°)
-- | - Tooltip on right → arrow points left (270°)
sideToRotation :: Side -> Int
sideToRotation = case _ of
  Top -> 180     -- Arrow points down
  Bottom -> 0   -- Arrow points up
  Left -> 90    -- Arrow points right
  Right -> 270  -- Arrow points left

-- | Position classes for arrow based on placement
arrowPositionClasses :: Placement -> Array String
arrowPositionClasses placement = case placement.side of
  Top -> 
    [ "bottom-0"
    , "translate-y-full"
    , "-mb-px"
    ] <> alignmentClasses placement.align "horizontal"
  Bottom ->
    [ "top-0"
    , "-translate-y-full"
    , "-mt-px"
    ] <> alignmentClasses placement.align "horizontal"
  Left ->
    [ "right-0"
    , "translate-x-full"
    , "-mr-px"
    ] <> alignmentClasses placement.align "vertical"
  Right ->
    [ "left-0"
    , "-translate-x-full"
    , "-ml-px"
    ] <> alignmentClasses placement.align "vertical"

-- | Alignment classes for arrow positioning
alignmentClasses :: Alignment -> String -> Array String
alignmentClasses align axis = case Tuple align axis of
  Tuple Start "horizontal" -> [ "left-4" ]
  Tuple Center "horizontal" -> [ "left-1/2", "-translate-x-1/2" ]
  Tuple End "horizontal" -> [ "right-4" ]
  Tuple Start "vertical" -> [ "top-4" ]
  Tuple Center "vertical" -> [ "top-1/2", "-translate-y-1/2" ]
  Tuple End "vertical" -> [ "bottom-4" ]
  _ -> []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert placement to positioning class
placementToClass :: Placement -> String
placementToClass placement = case placement.side of
  Top -> "bottom-full mb-3"
  Right -> "left-full ml-3"
  Bottom -> "top-full mt-3"
  Left -> "right-full mr-3"

-- | Convert side to string
sideToString :: Side -> String
sideToString = case _ of
  Top -> "top"
  Right -> "right"
  Bottom -> "bottom"
  Left -> "left"

-- | Generate a range of integers
range :: Int -> Int -> Array Int
range start end
  | start > end = []
  | otherwise = [ start ] <> range (start + 1) end
