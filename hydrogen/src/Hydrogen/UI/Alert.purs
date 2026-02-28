-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // ui // alert
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Alert Component — Pure Element Version
-- |
-- | Alert banners for important messages.
module Hydrogen.UI.Alert
  ( alert
  , alertTitle
  , alertDescription
  , AlertVariant(Default, Info, Success, Warning, Destructive)
  , variant
  , className
  ) where

import Prelude (class Eq, (<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

data AlertVariant = Default | Info | Success | Warning | Destructive

derive instance eqAlertVariant :: Eq AlertVariant

variantClasses :: AlertVariant -> String
variantClasses = case _ of
  Default -> "bg-background text-foreground"
  Info -> "border-blue-500/50 text-blue-600 bg-blue-50 dark:bg-blue-950"
  Success -> "border-green-500/50 text-green-600 bg-green-50 dark:bg-green-950"
  Warning -> "border-yellow-500/50 text-yellow-600 bg-yellow-50 dark:bg-yellow-950"
  Destructive -> "border-destructive/50 text-destructive bg-destructive/10"

type AlertConfig = { variant :: AlertVariant, className :: String }
type ConfigMod = AlertConfig -> AlertConfig

defaultConfig :: AlertConfig
defaultConfig = { variant: Default, className: "" }

variant :: AlertVariant -> ConfigMod
variant v config = config { variant = v }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

baseClasses :: String
baseClasses = "relative w-full rounded-lg border p-4 [&>svg~*]:pl-7 [&>svg+div]:translate-y-[-3px] [&>svg]:absolute [&>svg]:left-4 [&>svg]:top-4 [&>svg]:text-foreground"

alert :: forall msg. Array ConfigMod -> Array (E.Element msg) -> E.Element msg
alert mods children =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = baseClasses <> " " <> variantClasses config.variant <> " " <> config.className
  in
    E.div_ 
      [ E.class_ allClasses
      , E.role "alert"
      ] 
      children

alertTitle :: forall msg. String -> E.Element msg
alertTitle text =
  E.h5_
    [ E.class_ "mb-1 font-medium leading-none tracking-tight" ]
    [ E.text text ]

alertDescription :: forall msg. String -> E.Element msg
alertDescription text =
  E.div_
    [ E.class_ "text-sm [&_p]:leading-relaxed" ]
    [ E.text text ]
