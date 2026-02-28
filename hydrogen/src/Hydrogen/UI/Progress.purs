-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // ui // progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress Component — Pure Element Version
-- |
-- | Progress bars and indicators.
module Hydrogen.UI.Progress
  ( progress
  , ProgressVariant(Default, Success, Warning, Danger)
  , variant
  , className
  ) where

import Prelude (class Eq, max, min, show, (<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

data ProgressVariant = Default | Success | Warning | Danger

derive instance eqProgressVariant :: Eq ProgressVariant

variantClasses :: ProgressVariant -> String
variantClasses = case _ of
  Default -> "bg-primary"
  Success -> "bg-green-500"
  Warning -> "bg-yellow-500"
  Danger -> "bg-red-500"

type ProgressConfig = { variant :: ProgressVariant, className :: String }
type ConfigMod = ProgressConfig -> ProgressConfig

defaultConfig :: ProgressConfig
defaultConfig = { variant: Default, className: "" }

variant :: ProgressVariant -> ConfigMod
variant v config = config { variant = v }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

-- | Progress bar
-- |
-- | `value` should be 0-100
progress :: forall msg. Array ConfigMod -> Int -> E.Element msg
progress mods value =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    barClasses = "h-full transition-all " <> variantClasses config.variant
    containerClasses = "relative h-4 w-full overflow-hidden rounded-full bg-secondary " <> config.className
    clampedValue = min 100 (max 0 value)
    widthStyle = "width: " <> show clampedValue <> "%"
  in
    E.div_
      [ E.class_ containerClasses
      , E.role "progressbar"
      , E.attr "aria-valuenow" (show value)
      , E.attr "aria-valuemin" "0"
      , E.attr "aria-valuemax" "100"
      ]
      [ E.div_ 
          [ E.class_ barClasses
          , E.attr "style" widthStyle
          ] 
          []
      ]
