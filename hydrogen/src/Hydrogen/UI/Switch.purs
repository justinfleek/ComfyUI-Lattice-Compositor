-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // ui // switch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Switch Component — Pure Element Version
-- |
-- | Toggle switches for boolean settings.
module Hydrogen.UI.Switch
  ( switch
  , checked
  , disabled
  , onToggle
  , className
  ) where

import Prelude (not, (<>))

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

type SwitchConfig msg =
  { checked :: Boolean
  , disabled :: Boolean
  , onToggle :: Maybe (Boolean -> msg)
  , className :: String
  }

type ConfigMod msg = SwitchConfig msg -> SwitchConfig msg

defaultConfig :: forall msg. SwitchConfig msg
defaultConfig = 
  { checked: false
  , disabled: false
  , onToggle: Nothing
  , className: ""
  }

checked :: forall msg. Boolean -> ConfigMod msg
checked c config = config { checked = c }

disabled :: forall msg. Boolean -> ConfigMod msg
disabled d config = config { disabled = d }

onToggle :: forall msg. (Boolean -> msg) -> ConfigMod msg
onToggle f config = config { onToggle = Just f }

className :: forall msg. String -> ConfigMod msg
className c config = config { className = config.className <> " " <> c }

switch :: forall msg. Array (ConfigMod msg) -> E.Element msg
switch mods =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    checkedClasses = if config.checked 
      then "bg-primary" 
      else "bg-input"
    disabledClasses = if config.disabled 
      then "cursor-not-allowed opacity-50" 
      else "cursor-pointer"
    thumbTranslate = if config.checked 
      then "translate-x-5" 
      else "translate-x-0"
    containerClasses = "peer inline-flex h-6 w-11 shrink-0 items-center rounded-full border-2 border-transparent transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 focus-visible:ring-offset-background " 
      <> checkedClasses <> " " <> disabledClasses <> " " <> config.className
    thumbClasses = "pointer-events-none block h-5 w-5 rounded-full bg-background shadow-lg ring-0 transition-transform " <> thumbTranslate
    
    clickAttr = case config.onToggle of
      Just f -> [ E.onClick (f (not config.checked)) ]
      Nothing -> []
  in
    E.button_
      ([ E.class_ containerClasses
       , E.role "switch"
       , E.attr "aria-checked" (if config.checked then "true" else "false")
       , E.disabled config.disabled
       ] <> clickAttr)
      [ E.span_ [ E.class_ thumbClasses ] [] ]
