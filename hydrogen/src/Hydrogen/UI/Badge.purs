-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // ui // badge
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Badge Component — Pure Element Version
-- |
-- | Small status indicators using the pure Element abstraction.
module Hydrogen.UI.Badge
  ( badge
  , BadgeVariant(Default, Secondary, Destructive, Outline, Success, Warning)
  , variant
  , className
  ) where

import Prelude (class Eq, (<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

-- | Badge variants
data BadgeVariant
  = Default
  | Secondary
  | Destructive
  | Outline
  | Success
  | Warning

derive instance eqBadgeVariant :: Eq BadgeVariant

variantClasses :: BadgeVariant -> String
variantClasses = case _ of
  Default -> "border-transparent bg-primary text-primary-foreground hover:bg-primary/80"
  Secondary -> "border-transparent bg-secondary text-secondary-foreground hover:bg-secondary/80"
  Destructive -> "border-transparent bg-destructive text-destructive-foreground hover:bg-destructive/80"
  Outline -> "text-foreground"
  Success -> "border-transparent bg-green-500 text-white hover:bg-green-600"
  Warning -> "border-transparent bg-yellow-500 text-white hover:bg-yellow-600"

type BadgeConfig = { variant :: BadgeVariant, className :: String }
type ConfigMod = BadgeConfig -> BadgeConfig

defaultConfig :: BadgeConfig
defaultConfig = { variant: Default, className: "" }

variant :: BadgeVariant -> ConfigMod
variant v config = config { variant = v }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

baseClasses :: String
baseClasses = "inline-flex items-center rounded-full border px-2.5 py-0.5 text-xs font-semibold transition-colors focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"

badge :: forall msg. Array ConfigMod -> Array (E.Element msg) -> E.Element msg
badge mods children =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = baseClasses <> " " <> variantClasses config.variant <> " " <> config.className
  in
    E.div_ [ E.class_ allClasses ] children
