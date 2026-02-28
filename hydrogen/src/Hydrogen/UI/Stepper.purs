-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // ui // stepper
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stepper Component — Pure Element Version
-- |
-- | Multi-step progress indicators.
module Hydrogen.UI.Stepper
  ( stepper
  , stepperItem
  , StepStatus(Complete, Current, Upcoming)
  , Orientation(Horizontal, Vertical)
  , orientation
  , className
  ) where

import Prelude (class Eq, (<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

data StepStatus = Complete | Current | Upcoming

derive instance eqStepStatus :: Eq StepStatus

data Orientation = Horizontal | Vertical

derive instance eqOrientation :: Eq Orientation

statusClasses :: StepStatus -> { circle :: String, text :: String }
statusClasses = case _ of
  Complete -> 
    { circle: "bg-primary text-primary-foreground"
    , text: "text-foreground"
    }
  Current -> 
    { circle: "border-2 border-primary bg-background text-primary"
    , text: "text-foreground font-medium"
    }
  Upcoming -> 
    { circle: "border-2 border-muted bg-background text-muted-foreground"
    , text: "text-muted-foreground"
    }

type StepperConfig = { orientation :: Orientation, className :: String }
type ConfigMod = StepperConfig -> StepperConfig

defaultConfig :: StepperConfig
defaultConfig = { orientation: Horizontal, className: "" }

orientation :: Orientation -> ConfigMod
orientation o config = config { orientation = o }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

-- | Stepper container
stepper :: forall msg. Array ConfigMod -> Array (E.Element msg) -> E.Element msg
stepper mods children =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    orientationClasses = case config.orientation of
      Horizontal -> "flex items-center justify-between"
      Vertical -> "flex flex-col space-y-4"
    allClasses = orientationClasses <> " " <> config.className
  in
    E.div_ [ E.class_ allClasses ] children

-- | Single step item
stepperItem :: forall msg. StepStatus -> String -> String -> E.Element msg
stepperItem status stepNumber label =
  let
    classes = statusClasses status
    checkmark = "✓"
  in
    E.div_
      [ E.class_ "flex items-center gap-3" ]
      [ E.div_
          [ E.class_ ("flex h-8 w-8 shrink-0 items-center justify-center rounded-full text-sm " <> classes.circle) ]
          [ E.text (case status of
              Complete -> checkmark
              _ -> stepNumber)
          ]
      , E.span_
          [ E.class_ ("text-sm " <> classes.text) ]
          [ E.text label ]
      ]
