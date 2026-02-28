-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // element // stepper
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Stepper Component
-- |
-- | Multi-step wizard/stepper component for step indicators and navigation.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Stepper as Stepper
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic stepper
-- | Stepper.stepper
-- |   [ Stepper.steps
-- |       [ Stepper.step { label: "Account", description: "Create your account" }
-- |       , Stepper.step { label: "Profile", description: "Add your details" }
-- |       , Stepper.step { label: "Confirm", description: "Review and submit" }
-- |       ]
-- |   , Stepper.currentStep 1
-- |   ]
-- |
-- | -- Vertical stepper
-- | Stepper.stepper
-- |   [ Stepper.orientation Stepper.Vertical
-- |   , Stepper.steps mySteps
-- |   , Stepper.currentStep 2
-- |   ]
-- |
-- | -- With navigation and clickable steps
-- | Stepper.stepperWithNav
-- |   [ Stepper.steps mySteps
-- |   , Stepper.currentStep current
-- |   , Stepper.onStepClick HandleStepClick
-- |   , Stepper.onNext HandleNext
-- |   , Stepper.onPrevious HandlePrevious
-- |   ]
-- |   stepContent
-- | ```
module Hydrogen.Element.Compound.Stepper
  ( -- * Stepper Components
    stepper
  , stepperWithNav
  , stepIndicator
  , stepConnector
  , stepNavigation
    -- * Step Types
  , Step
  , StepStatus(Completed, Current, Upcoming, Error)
  , step
  , stepWithIcon
    -- * Props
  , StepperProps
  , StepperProp
  , defaultProps
    -- * Prop Builders
  , steps
  , currentStep
  , orientation
  , linear
  , showNumbers
  , clickable
  , className
  , onStepClick
  , onNext
  , onPrevious
  , onComplete
  , nextLabel
  , previousLabel
  , completeLabel
    -- * Types
  , Orientation(Horizontal, Vertical)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , show
  , (<>)
  , (==)
  , (<)
  , (>=)
  , (-)
  , (+)
  , (&&)
  , (||)
  , not
  , otherwise
  )

import Data.Array (foldl, length, mapWithIndex, index)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stepper orientation
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

-- | Step status
data StepStatus
  = Completed
  | Current
  | Upcoming
  | Error

derive instance eqStepStatus :: Eq StepStatus
derive instance ordStepStatus :: Ord StepStatus

-- | Step definition
type Step =
  { label :: String
  , description :: Maybe String
  , icon :: Maybe String
  , optional :: Boolean
  }

-- | Create a simple step
step :: { label :: String, description :: String } -> Step
step cfg =
  { label: cfg.label
  , description: Just cfg.description
  , icon: Nothing
  , optional: false
  }

-- | Create a step with custom icon
stepWithIcon :: { label :: String, description :: String, icon :: String } -> Step
stepWithIcon cfg =
  { label: cfg.label
  , description: Just cfg.description
  , icon: Just cfg.icon
  , optional: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

type StepperProps msg =
  { steps :: Array Step
  , currentStep :: Int
  , orientation :: Orientation
  , linear :: Boolean
  , showNumbers :: Boolean
  , clickable :: Boolean
  , className :: String
  , onStepClick :: Maybe (Int -> msg)
  , onNext :: Maybe msg
  , onPrevious :: Maybe msg
  , onComplete :: Maybe msg
  , nextLabel :: String
  , previousLabel :: String
  , completeLabel :: String
  }

type StepperProp msg = StepperProps msg -> StepperProps msg

defaultProps :: forall msg. StepperProps msg
defaultProps =
  { steps: []
  , currentStep: 0
  , orientation: Horizontal
  , linear: true
  , showNumbers: true
  , clickable: true
  , className: ""
  , onStepClick: Nothing
  , onNext: Nothing
  , onPrevious: Nothing
  , onComplete: Nothing
  , nextLabel: "Next"
  , previousLabel: "Previous"
  , completeLabel: "Complete"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set steps
steps :: forall msg. Array Step -> StepperProp msg
steps s props = props { steps = s }

-- | Set current step (0-indexed)
currentStep :: forall msg. Int -> StepperProp msg
currentStep s props = props { currentStep = s }

-- | Set orientation
orientation :: forall msg. Orientation -> StepperProp msg
orientation o props = props { orientation = o }

-- | Set linear mode (must complete steps in order)
linear :: forall msg. Boolean -> StepperProp msg
linear l props = props { linear = l }

-- | Show step numbers
showNumbers :: forall msg. Boolean -> StepperProp msg
showNumbers s props = props { showNumbers = s }

-- | Allow clicking on steps to navigate
clickable :: forall msg. Boolean -> StepperProp msg
clickable c props = props { clickable = c }

-- | Add custom class
className :: forall msg. String -> StepperProp msg
className c props = props { className = props.className <> " " <> c }

-- | Handle step click
onStepClick :: forall msg. (Int -> msg) -> StepperProp msg
onStepClick handler props = props { onStepClick = Just handler }

-- | Handle next button click
onNext :: forall msg. msg -> StepperProp msg
onNext handler props = props { onNext = Just handler }

-- | Handle previous button click
onPrevious :: forall msg. msg -> StepperProp msg
onPrevious handler props = props { onPrevious = Just handler }

-- | Handle complete button click
onComplete :: forall msg. msg -> StepperProp msg
onComplete handler props = props { onComplete = Just handler }

-- | Set next button label
nextLabel :: forall msg. String -> StepperProp msg
nextLabel l props = props { nextLabel = l }

-- | Set previous button label
previousLabel :: forall msg. String -> StepperProp msg
previousLabel l props = props { previousLabel = l }

-- | Set complete button label
completeLabel :: forall msg. String -> StepperProp msg
completeLabel l props = props { completeLabel = l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get status-based classes for indicator
statusClasses :: StepStatus -> String
statusClasses = case _ of
  Completed -> "bg-primary text-primary-foreground border-primary"
  Current -> "bg-primary text-primary-foreground border-primary ring-2 ring-primary ring-offset-2"
  Upcoming -> "bg-background text-muted-foreground border-muted"
  Error -> "bg-destructive text-destructive-foreground border-destructive"

-- | Get status-based classes for label
labelClasses :: StepStatus -> String
labelClasses = case _ of
  Completed -> "text-primary font-medium"
  Current -> "text-primary font-semibold"
  Upcoming -> "text-muted-foreground"
  Error -> "text-destructive font-medium"

-- | Get connector classes based on completion
connectorClasses :: Boolean -> String
connectorClasses completed =
  if completed
    then "bg-primary"
    else "bg-muted"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Determine step status based on current step
getStepStatus :: Int -> Int -> StepStatus
getStepStatus idx currentIdx
  | idx < currentIdx = Completed
  | idx == currentIdx = Current
  | otherwise = Upcoming

-- | Main stepper component (indicators only)
-- |
-- | Displays step indicators with connectors.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
stepper :: forall msg. Array (StepperProp msg) -> E.Element msg
stepper propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    totalSteps = length props.steps
    
    containerClasses = case props.orientation of
      Horizontal -> "flex items-start w-full"
      Vertical -> "flex flex-col"
  in
    E.div_
      [ E.classes [ containerClasses, props.className ]
      , E.role "list"
      , E.ariaLabel "Progress steps"
      ]
      ( mapWithIndex (renderStepWithConnector props totalSteps) props.steps )

-- | Stepper with navigation buttons
-- |
-- | Displays step indicators with content area and prev/next buttons.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
stepperWithNav :: forall msg. Array (StepperProp msg) -> Array (E.Element msg) -> E.Element msg
stepperWithNav propMods content =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    totalSteps = length props.steps
    currentContent = index content props.currentStep
  in
    E.div_
      [ E.classes [ "flex flex-col gap-6", props.className ] ]
      [ stepper propMods
      , case currentContent of
          Just c -> 
            E.div_
              [ E.class_ "min-h-[200px]" ]
              [ c ]
          Nothing -> E.text ""
      , stepNavigation props totalSteps
      ]

-- | Render step with connector
renderStepWithConnector :: forall msg. StepperProps msg -> Int -> Int -> Step -> E.Element msg
renderStepWithConnector props totalSteps idx stepDef =
  let
    status = getStepStatus idx props.currentStep
    isLast = idx == totalSteps - 1
    canClick = props.clickable && (not props.linear || idx < props.currentStep + 1)
    
    clickHandler = 
      if canClick
        then case props.onStepClick of
          Just handler -> [ E.onClick (handler idx) ]
          Nothing -> []
        else []
    
    ariaCurrent = if status == Current 
      then [ E.attr "aria-current" "step" ] 
      else []
  in
    case props.orientation of
      Horizontal ->
        E.div_
          [ E.classes [ "flex items-center", if isLast then "" else "flex-1" ] ]
          [ E.div_
              [ E.class_ "flex flex-col items-center gap-2" ]
              [ E.button_
                  ( [ E.classes 
                        [ "flex items-center justify-center w-10 h-10 rounded-full border-2 transition-all"
                        , statusClasses status
                        , if canClick then "cursor-pointer hover:opacity-80" else "cursor-default"
                        ]
                    , E.disabled (not canClick)
                    , E.role "listitem"
                    ] <> ariaCurrent <> clickHandler
                  )
                  [ stepIndicatorContent props idx stepDef status ]
              , E.div_
                  [ E.class_ "text-center" ]
                  [ E.div_
                      [ E.classes [ "text-sm", labelClasses status ] ]
                      [ E.text stepDef.label ]
                  , case stepDef.description of
                      Just desc ->
                        E.div_
                          [ E.class_ "text-xs text-muted-foreground mt-0.5" ]
                          [ E.text desc ]
                      Nothing -> E.text ""
                  ]
              ]
          , if isLast
              then E.text ""
              else stepConnector props.orientation (idx < props.currentStep)
          ]
      Vertical ->
        E.div_
          [ E.class_ "flex gap-4" ]
          [ E.div_
              [ E.class_ "flex flex-col items-center" ]
              [ E.button_
                  ( [ E.classes 
                        [ "flex items-center justify-center w-10 h-10 rounded-full border-2 transition-all"
                        , statusClasses status
                        , if canClick then "cursor-pointer hover:opacity-80" else "cursor-default"
                        ]
                    , E.disabled (not canClick)
                    , E.role "listitem"
                    ] <> ariaCurrent <> clickHandler
                  )
                  [ stepIndicatorContent props idx stepDef status ]
              , if isLast
                  then E.text ""
                  else stepConnector props.orientation (idx < props.currentStep)
              ]
          , E.div_
              [ E.class_ "flex-1 pb-8" ]
              [ E.div_
                  [ E.classes [ "text-sm font-medium", labelClasses status ] ]
                  [ E.text stepDef.label ]
              , case stepDef.description of
                  Just desc ->
                    E.div_
                      [ E.class_ "text-xs text-muted-foreground mt-1" ]
                      [ E.text desc ]
                  Nothing -> E.text ""
              , if stepDef.optional
                  then 
                    E.div_
                      [ E.class_ "text-xs text-muted-foreground italic mt-1" ]
                      [ E.text "Optional" ]
                  else E.text ""
              ]
          ]

-- | Step indicator content (number, icon, or check)
stepIndicatorContent :: forall msg. StepperProps msg -> Int -> Step -> StepStatus -> E.Element msg
stepIndicatorContent props idx stepDef status =
  case status of
    Completed -> checkIcon
    Error -> errorIcon
    _ ->
      case stepDef.icon of
        Just ic -> E.span_ [] [ E.text ic ]
        Nothing ->
          if props.showNumbers
            then E.span_ [] [ E.text (show (idx + 1)) ]
            else E.span_ [ E.class_ "w-2 h-2 rounded-full bg-current" ] []

-- | Step indicator circle
-- |
-- | A standalone step indicator for custom layouts.
stepIndicator :: forall msg. Int -> StepStatus -> Boolean -> E.Element msg
stepIndicator idx status showNumber =
  E.div_
    [ E.classes 
        [ "flex items-center justify-center w-10 h-10 rounded-full border-2"
        , statusClasses status
        ]
    ]
    [ case status of
        Completed -> checkIcon
        Error -> errorIcon
        _ ->
          if showNumber
            then E.span_ [] [ E.text (show (idx + 1)) ]
            else E.span_ [ E.class_ "w-2 h-2 rounded-full bg-current" ] []
    ]

-- | Step connector line
-- |
-- | A connector between step indicators.
stepConnector :: forall msg. Orientation -> Boolean -> E.Element msg
stepConnector orient completed =
  case orient of
    Horizontal ->
      E.div_
        [ E.classes [ "flex-1 h-0.5 mx-2 transition-colors", connectorClasses completed ] ]
        []
    Vertical ->
      E.div_
        [ E.classes [ "w-0.5 flex-1 min-h-[2rem] transition-colors", connectorClasses completed ] ]
        []

-- | Step navigation buttons
-- |
-- | Previous/Next/Complete buttons for navigating the stepper.
stepNavigation :: forall msg. StepperProps msg -> Int -> E.Element msg
stepNavigation props totalSteps =
  let
    isFirst = props.currentStep == 0
    isLast = props.currentStep >= totalSteps - 1
    
    prevButton =
      E.button_
        ( [ E.classes 
              [ "inline-flex items-center justify-center rounded-md text-sm font-medium h-10 px-4 py-2"
              , "border border-input bg-background hover:bg-accent hover:text-accent-foreground"
              , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
              , if isFirst then "opacity-50 cursor-not-allowed" else ""
              ]
          , E.disabled isFirst
          ] <> case props.onPrevious of
            Just handler -> if isFirst then [] else [ E.onClick handler ]
            Nothing -> []
        )
        [ E.text props.previousLabel ]
    
    nextButton =
      E.button_
        ( [ E.classes 
              [ "inline-flex items-center justify-center rounded-md text-sm font-medium h-10 px-4 py-2"
              , "bg-primary text-primary-foreground hover:bg-primary/90"
              , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
              ]
          ] <> case props.onNext of
            Just handler -> [ E.onClick handler ]
            Nothing -> []
        )
        [ E.text props.nextLabel ]
    
    completeButton =
      E.button_
        ( [ E.classes 
              [ "inline-flex items-center justify-center rounded-md text-sm font-medium h-10 px-4 py-2"
              , "bg-primary text-primary-foreground hover:bg-primary/90"
              , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
              ]
          ] <> case props.onComplete of
            Just handler -> [ E.onClick handler ]
            Nothing -> []
        )
        [ E.text props.completeLabel ]
  in
    E.div_
      [ E.class_ "flex justify-between pt-4" ]
      [ prevButton
      , if isLast then completeButton else nextButton
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check icon for completed steps
checkIcon :: forall msg. E.Element msg
checkIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "3"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.polyline_ [ E.attr "points" "20 6 9 17 4 12" ] ]

-- | Error icon for error steps
errorIcon :: forall msg. E.Element msg
errorIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "3"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.line_ [ E.attr "x1" "18", E.attr "y1" "6", E.attr "x2" "6", E.attr "y2" "18" ]
    , E.line_ [ E.attr "x1" "6", E.attr "y1" "6", E.attr "x2" "18", E.attr "y2" "18" ]
    ]
