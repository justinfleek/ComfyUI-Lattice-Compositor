-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // ui // radio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Radio Component — Pure Element Version
-- |
-- | Radio button groups for single selection.
module Hydrogen.UI.Radio
  ( radioGroup
  , radioItem
  , radioItemWithLabel
  , RadioConfig
  , defaultConfig
  , selected
  , disabled
  , onSelect
  , className
  ) where

import Prelude (class Eq, (<>), (==))

import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

type RadioConfig a msg =
  { selected :: Maybe a
  , disabled :: Boolean
  , onSelect :: Maybe (a -> msg)
  , className :: String
  }

type ConfigMod a msg = RadioConfig a msg -> RadioConfig a msg

defaultConfig :: forall a msg. RadioConfig a msg
defaultConfig = 
  { selected: Nothing
  , disabled: false
  , onSelect: Nothing
  , className: ""
  }

selected :: forall a msg. a -> ConfigMod a msg
selected v config = config { selected = Just v }

disabled :: forall a msg. Boolean -> ConfigMod a msg
disabled d config = config { disabled = d }

onSelect :: forall a msg. (a -> msg) -> ConfigMod a msg
onSelect f config = config { onSelect = Just f }

className :: forall a msg. String -> ConfigMod a msg
className c config = config { className = config.className <> " " <> c }

-- | Radio group container
radioGroup :: forall msg. Array (E.Element msg) -> E.Element msg
radioGroup children =
  E.div_ [ E.class_ "grid gap-2", E.role "radiogroup" ] children

-- | Single radio item
radioItem :: forall a msg. Eq a => RadioConfig a msg -> a -> E.Element msg
radioItem config value =
  let
    isSelected = case config.selected of
      Just s -> s == value
      Nothing -> false
    baseClasses = "aspect-square h-4 w-4 rounded-full border border-primary text-primary ring-offset-background focus:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"
    selectedClasses = if isSelected then "bg-primary" else ""
    allClasses = baseClasses <> " " <> selectedClasses <> " " <> config.className
    
    clickAttr = case config.onSelect of
      Just f -> [ E.onClick (f value) ]
      Nothing -> []
  in
    E.button_
      ([ E.class_ allClasses
       , E.role "radio"
       , E.attr "aria-checked" (if isSelected then "true" else "false")
       , E.disabled config.disabled
       ] <> clickAttr)
      [ if isSelected 
          then E.span_ [ E.class_ "flex items-center justify-center" ] 
                 [ E.div_ [ E.class_ "h-2 w-2 rounded-full bg-background" ] [] ]
          else E.empty
      ]

-- | Radio item with label
radioItemWithLabel :: forall a msg. Eq a => RadioConfig a msg -> a -> String -> E.Element msg
radioItemWithLabel config value label =
  E.label_
    [ E.class_ "flex items-center space-x-2 cursor-pointer" ]
    [ radioItem config value
    , E.span_ 
        [ E.class_ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ] 
        [ E.text label ]
    ]
