-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // ui // input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input Component — Pure Element Version
-- |
-- | Form input components built using the pure Element abstraction.
-- | Includes text inputs, textareas, and form field wrappers.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.UI.Input as Input
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Simple text input
-- | Input.input
-- |   [ Input.value state.email
-- |   , Input.onInput UpdateEmail
-- |   , Input.placeholder "you@example.com"
-- |   ]
-- |
-- | -- With label wrapper
-- | Input.field "Email" $
-- |   Input.input [ Input.value state.email, Input.onInput UpdateEmail ]
-- |
-- | -- Textarea
-- | Input.textarea
-- |   [ Input.value state.message
-- |   , Input.onInput UpdateMessage
-- |   , Input.rows 4
-- |   ]
-- | ```
module Hydrogen.UI.Input
  ( -- * Input Components
    input
  , textarea
  
  -- * Form Field Wrapper
  , field
  , fieldWithError
  
  -- * Configuration
  , InputConfig
  , defaultConfig
  
  -- * Config Modifiers
  , value
  , placeholder
  , onInput
  , onChange
  , onFocus
  , onBlur
  , disabled
  , readonly
  , required
  , autofocus
  , className
  , id_
  , name
  , inputType
  , rows
  , cols
  
  -- * Input Types
  , InputType(Text, Password, Email, Number, Tel, Url, Search, Date, Time, DateTimeLocal, Month, Week, Color, File, Hidden)
  ) where

import Prelude
  ( show
  , (<>)
  , (||)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTML input types
data InputType
  = Text
  | Password
  | Email
  | Number
  | Tel
  | Url
  | Search
  | Date
  | Time
  | DateTimeLocal
  | Month
  | Week
  | Color
  | File
  | Hidden

-- | Convert InputType to string
inputTypeStr :: InputType -> String
inputTypeStr = case _ of
  Text -> "text"
  Password -> "password"
  Email -> "email"
  Number -> "number"
  Tel -> "tel"
  Url -> "url"
  Search -> "search"
  Date -> "date"
  Time -> "time"
  DateTimeLocal -> "datetime-local"
  Month -> "month"
  Week -> "week"
  Color -> "color"
  File -> "file"
  Hidden -> "hidden"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input configuration
type InputConfig msg =
  { value :: Maybe String
  , placeholder :: Maybe String
  , onInput :: Maybe (String -> msg)
  , onChange :: Maybe (String -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  , disabled :: Boolean
  , readonly :: Boolean
  , required :: Boolean
  , autofocus :: Boolean
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , inputType :: InputType
  , rows :: Maybe Int
  , cols :: Maybe Int
  }

-- | Default input configuration
defaultConfig :: forall msg. InputConfig msg
defaultConfig =
  { value: Nothing
  , placeholder: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , disabled: false
  , readonly: false
  , required: false
  , autofocus: false
  , className: ""
  , id: Nothing
  , name: Nothing
  , inputType: Text
  , rows: Nothing
  , cols: Nothing
  }

-- | Configuration modifier type
type ConfigMod msg = InputConfig msg -> InputConfig msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // config // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input value
value :: forall msg. String -> ConfigMod msg
value v config = config { value = Just v }

-- | Set placeholder text
placeholder :: forall msg. String -> ConfigMod msg
placeholder p config = config { placeholder = Just p }

-- | Set input handler (fires on each keystroke)
onInput :: forall msg. (String -> msg) -> ConfigMod msg
onInput f config = config { onInput = Just f }

-- | Set change handler (fires on blur after change)
onChange :: forall msg. (String -> msg) -> ConfigMod msg
onChange f config = config { onChange = Just f }

-- | Set focus handler
onFocus :: forall msg. msg -> ConfigMod msg
onFocus msg config = config { onFocus = Just msg }

-- | Set blur handler
onBlur :: forall msg. msg -> ConfigMod msg
onBlur msg config = config { onBlur = Just msg }

-- | Set disabled state
disabled :: forall msg. Boolean -> ConfigMod msg
disabled d config = config { disabled = d }

-- | Set readonly state
readonly :: forall msg. Boolean -> ConfigMod msg
readonly r config = config { readonly = r }

-- | Set required state
required :: forall msg. Boolean -> ConfigMod msg
required r config = config { required = r }

-- | Set autofocus
autofocus :: forall msg. Boolean -> ConfigMod msg
autofocus a config = config { autofocus = a }

-- | Add custom CSS class
className :: forall msg. String -> ConfigMod msg
className c config = config { className = config.className <> " " <> c }

-- | Set input id
id_ :: forall msg. String -> ConfigMod msg
id_ i config = config { id = Just i }

-- | Set input name
name :: forall msg. String -> ConfigMod msg
name n config = config { name = Just n }

-- | Set input type
inputType :: forall msg. InputType -> ConfigMod msg
inputType t config = config { inputType = t }

-- | Set textarea rows
rows :: forall msg. Int -> ConfigMod msg
rows r config = config { rows = Just r }

-- | Set textarea cols
cols :: forall msg. Int -> ConfigMod msg
cols c config = config { cols = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base input classes (Tailwind)
baseClasses :: String
baseClasses = 
  "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background file:border-0 file:bg-transparent file:text-sm file:font-medium placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Build attributes from config
buildAttrs :: forall msg. InputConfig msg -> Array (E.Attribute msg)
buildAttrs config = 
  [ E.class_ (baseClasses <> " " <> config.className)
  , E.disabled (config.disabled || config.readonly)
  ]
  <> maybeAttr E.id_ config.id
  <> maybeAttr E.name config.name
  <> maybeAttr E.value config.value
  <> maybeAttr E.placeholder config.placeholder
  <> maybeHandler E.onInput config.onInput
  <> maybeHandler E.onChange config.onChange
  <> maybeMsg E.onFocus config.onFocus
  <> maybeMsg E.onBlur config.onBlur
  <> conditionalAttr config.required (E.required true)
  <> conditionalAttr config.readonly (E.readonly true)
  <> conditionalAttr config.autofocus (E.autofocus true)

-- | Input element
-- |
-- | A styled text input with various configuration options.
input :: forall msg. Array (ConfigMod msg) -> E.Element msg
input mods =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    attrs = buildAttrs config <> [ E.type_ (inputTypeStr config.inputType) ]
  in
    E.input_ attrs

-- | Textarea element
-- |
-- | A multi-line text input.
textarea :: forall msg. Array (ConfigMod msg) -> E.Element msg
textarea mods =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    baseAttrs = buildAttrs config
    rowsAttr = case config.rows of
      Just r -> [ E.attr "rows" (show r) ]
      Nothing -> []
    colsAttr = case config.cols of
      Just c -> [ E.attr "cols" (show c) ]
      Nothing -> []
    -- Textarea has different height class
    textareaClass = "min-h-20 h-auto"
    allAttrs = baseAttrs <> rowsAttr <> colsAttr <> [ E.class_ textareaClass ]
  in
    E.textarea_ allAttrs []

-- | Form field wrapper with label
-- |
-- | Wraps an input with a label for accessibility.
field :: forall msg. String -> E.Element msg -> E.Element msg
field label inputEl =
  E.div_
    [ E.class_ "space-y-2" ]
    [ E.label_
        [ E.class_ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]
        [ E.text label ]
    , inputEl
    ]

-- | Form field with label and error message
-- |
-- | Shows an error message below the input when present.
fieldWithError :: forall msg. String -> Maybe String -> E.Element msg -> E.Element msg
fieldWithError label maybeError inputEl =
  E.div_
    [ E.class_ "space-y-2" ]
    [ E.label_
        [ E.class_ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]
        [ E.text label ]
    , inputEl
    , case maybeError of
        Just err -> E.p_ [ E.class_ "text-sm text-destructive" ] [ E.text err ]
        Nothing -> E.empty
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Maybe String to attribute array
maybeAttr :: forall msg. (String -> E.Attribute msg) -> Maybe String -> Array (E.Attribute msg)
maybeAttr f = case _ of
  Just v -> [ f v ]
  Nothing -> []

-- | Convert Maybe handler to attribute array
maybeHandler :: forall msg. ((String -> msg) -> E.Attribute msg) -> Maybe (String -> msg) -> Array (E.Attribute msg)
maybeHandler f = case _ of
  Just h -> [ f h ]
  Nothing -> []

-- | Convert Maybe msg to attribute array
maybeMsg :: forall msg. (msg -> E.Attribute msg) -> Maybe msg -> Array (E.Attribute msg)
maybeMsg f = case _ of
  Just m -> [ f m ]
  Nothing -> []

-- | Include attribute only if condition is true
conditionalAttr :: forall msg. Boolean -> E.Attribute msg -> Array (E.Attribute msg)
conditionalAttr enabled attr = if enabled then [ attr ] else []


