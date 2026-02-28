-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // ui // check-box
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Checkbox Component — Pure Element Version
-- |
-- | Checkboxes for boolean selections.
module Hydrogen.UI.Checkbox
  ( checkbox
  , checkboxWithLabel
  , checked
  , disabled
  , onToggle
  , className
  ) where

import Prelude (not, (<>))

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

type CheckboxConfig msg =
  { checked :: Boolean
  , disabled :: Boolean
  , onToggle :: Maybe (Boolean -> msg)
  , className :: String
  }

type ConfigMod msg = CheckboxConfig msg -> CheckboxConfig msg

defaultConfig :: forall msg. CheckboxConfig msg
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

baseClasses :: String
baseClasses = "peer h-4 w-4 shrink-0 rounded-sm border border-primary ring-offset-background focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

checkbox :: forall msg. Array (ConfigMod msg) -> E.Element msg
checkbox mods =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    checkedClasses = if config.checked 
      then "bg-primary text-primary-foreground" 
      else "bg-background"
    allClasses = baseClasses <> " " <> checkedClasses <> " " <> config.className
    
    clickAttr = case config.onToggle of
      Just f -> [ E.onClick (f (not config.checked)) ]
      Nothing -> []
    
    checkIcon = if config.checked
      then [ E.span_ [ E.class_ "flex items-center justify-center text-current" ] 
             [ E.text "✓" ] ]
      else []
  in
    E.button_
      ([ E.class_ allClasses
       , E.role "checkbox"
       , E.attr "aria-checked" (if config.checked then "true" else "false")
       , E.disabled config.disabled
       ] <> clickAttr)
      checkIcon

-- | Checkbox with label
checkboxWithLabel :: forall msg. Array (ConfigMod msg) -> String -> E.Element msg
checkboxWithLabel mods label =
  E.label_
    [ E.class_ "flex items-center space-x-2 cursor-pointer" ]
    [ checkbox mods
    , E.span_ 
        [ E.class_ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ] 
        [ E.text label ]
    ]
