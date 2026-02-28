-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // ui // toggle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toggle Component — Pure Element Version
-- |
-- | Toggle buttons for binary choices.
module Hydrogen.UI.Toggle
  ( toggle
  , ToggleVariant(..)
  , ToggleSize(..)
  , variant
  , size
  , pressed
  , disabled
  , onToggle
  , className
  ) where

import Prelude (class Eq, not, (<>))

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

data ToggleVariant = Default | Outline

derive instance eqToggleVariant :: Eq ToggleVariant

data ToggleSize = Sm | Md | Lg

derive instance eqToggleSize :: Eq ToggleSize

variantClasses :: ToggleVariant -> Boolean -> String
variantClasses v isPressed = case v of
  Default -> if isPressed 
    then "bg-accent text-accent-foreground" 
    else "bg-transparent hover:bg-muted hover:text-muted-foreground"
  Outline -> if isPressed 
    then "bg-accent text-accent-foreground border-accent" 
    else "border border-input bg-transparent hover:bg-accent hover:text-accent-foreground"

sizeClasses :: ToggleSize -> String
sizeClasses = case _ of
  Sm -> "h-9 px-2.5"
  Md -> "h-10 px-3"
  Lg -> "h-11 px-5"

type ToggleConfig msg =
  { variant :: ToggleVariant
  , size :: ToggleSize
  , pressed :: Boolean
  , disabled :: Boolean
  , onToggle :: Maybe (Boolean -> msg)
  , className :: String
  }

type ConfigMod msg = ToggleConfig msg -> ToggleConfig msg

defaultConfig :: forall msg. ToggleConfig msg
defaultConfig = 
  { variant: Default
  , size: Md
  , pressed: false
  , disabled: false
  , onToggle: Nothing
  , className: ""
  }

variant :: forall msg. ToggleVariant -> ConfigMod msg
variant v config = config { variant = v }

size :: forall msg. ToggleSize -> ConfigMod msg
size s config = config { size = s }

pressed :: forall msg. Boolean -> ConfigMod msg
pressed p config = config { pressed = p }

disabled :: forall msg. Boolean -> ConfigMod msg
disabled d config = config { disabled = d }

onToggle :: forall msg. (Boolean -> msg) -> ConfigMod msg
onToggle f config = config { onToggle = Just f }

className :: forall msg. String -> ConfigMod msg
className c config = config { className = config.className <> " " <> c }

baseClasses :: String
baseClasses = "inline-flex items-center justify-center rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"

toggle :: forall msg. Array (ConfigMod msg) -> Array (E.Element msg) -> E.Element msg
toggle mods children =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = baseClasses 
      <> " " <> variantClasses config.variant config.pressed 
      <> " " <> sizeClasses config.size 
      <> " " <> config.className
    
    clickAttr = case config.onToggle of
      Just f -> [ E.onClick (f (not config.pressed)) ]
      Nothing -> []
  in
    E.button_
      ([ E.class_ allClasses
       , E.attr "aria-pressed" (if config.pressed then "true" else "false")
       , E.disabled config.disabled
       ] <> clickAttr)
      children
