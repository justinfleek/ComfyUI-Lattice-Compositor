-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // ui // text-area
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Textarea Component — Pure Element Version
-- |
-- | Enhanced textarea with auto-resize, character counting, and validation.
-- | Renders using the pure Element abstraction for target-agnostic UI.
-- |
-- | ## Features
-- |
-- | - Auto-resize to content
-- | - Character counting with limit
-- | - Validation states (error, required)
-- | - Disabled and read-only modes
-- | - Label and field variants
-- |
-- | ## Usage with Halogen
-- |
-- | ```purescript
-- | import Hydrogen.UI.Textarea as Textarea
-- | import Hydrogen.Target.Halogen as TH
-- |
-- | myTextarea :: Textarea.Element Action
-- | myTextarea = Textarea.textarea
-- |   [ Textarea.value state.message
-- |   , Textarea.placeholder "Enter message..."
-- |   , Textarea.onInput HandleInput
-- |   , Textarea.maxLength 500
-- |   ]
-- |
-- | render :: State -> H.ComponentHTML Action Slots m
-- | render state = TH.toHalogen myTextarea
-- | ```
-- |
-- | ## Usage for Static Rendering
-- |
-- | ```purescript
-- | import Hydrogen.UI.Textarea as Textarea
-- | import Hydrogen.Target.Static as TS
-- |
-- | html :: String
-- | html = TS.render (Textarea.textarea [ Textarea.placeholder "Comments..." ])
-- | ```
module Hydrogen.UI.Textarea
  ( -- * Textarea Components
    textarea
  , textareaWithLabel
  , textareaWithCounter
  , textareaField
  
  -- * Configuration
  , TextareaConfig
  , defaultConfig
  
  -- * Config Modifiers
  , value
  , placeholder
  , disabled
  , readOnly
  , required
  , autoResize
  , minRows
  , maxRows
  , maxLength
  , error
  , errorMessage
  , className
  , id
  , name
  , onInput
  , onChange
  , onFocus
  , onBlur
  ) where

import Prelude
  ( (<>)
  , (>)
  , (/=)
  , (&&)
  , show
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Data.String (length) as String
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Textarea configuration
type TextareaConfig msg =
  { value :: String
  , placeholder :: String
  , disabled :: Boolean
  , readOnly :: Boolean
  , required :: Boolean
  , autoResize :: Boolean
  , minRows :: Int
  , maxRows :: Int
  , maxLength :: Maybe Int
  , error :: Boolean
  , errorMessage :: String
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , onInput :: Maybe (String -> msg)
  , onChange :: Maybe (String -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  }

-- | Default textarea configuration
defaultConfig :: forall msg. TextareaConfig msg
defaultConfig =
  { value: ""
  , placeholder: ""
  , disabled: false
  , readOnly: false
  , required: false
  , autoResize: false
  , minRows: 3
  , maxRows: 10
  , maxLength: Nothing
  , error: false
  , errorMessage: ""
  , className: ""
  , id: Nothing
  , name: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // config modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration modifier type
type ConfigMod cfg = cfg -> cfg

-- | Set value
value :: forall msg. String -> ConfigMod (TextareaConfig msg)
value v cfg = cfg { value = v }

-- | Set placeholder
placeholder :: forall msg. String -> ConfigMod (TextareaConfig msg)
placeholder p cfg = cfg { placeholder = p }

-- | Set disabled state
disabled :: forall msg. Boolean -> ConfigMod (TextareaConfig msg)
disabled d cfg = cfg { disabled = d }

-- | Set read-only state
readOnly :: forall msg. Boolean -> ConfigMod (TextareaConfig msg)
readOnly r cfg = cfg { readOnly = r }

-- | Set required state
required :: forall msg. Boolean -> ConfigMod (TextareaConfig msg)
required r cfg = cfg { required = r }

-- | Enable auto-resize to content
autoResize :: forall msg. Boolean -> ConfigMod (TextareaConfig msg)
autoResize a cfg = cfg { autoResize = a }

-- | Set minimum rows
minRows :: forall msg. Int -> ConfigMod (TextareaConfig msg)
minRows r cfg = cfg { minRows = r }

-- | Set maximum rows (for auto-resize)
maxRows :: forall msg. Int -> ConfigMod (TextareaConfig msg)
maxRows r cfg = cfg { maxRows = r }

-- | Set maximum character length
maxLength :: forall msg. Int -> ConfigMod (TextareaConfig msg)
maxLength l cfg = cfg { maxLength = Just l }

-- | Set error state
error :: forall msg. Boolean -> ConfigMod (TextareaConfig msg)
error e cfg = cfg { error = e }

-- | Set error message (also sets error state to true)
errorMessage :: forall msg. String -> ConfigMod (TextareaConfig msg)
errorMessage msg cfg = cfg { errorMessage = msg, error = true }

-- | Add custom class
className :: forall msg. String -> ConfigMod (TextareaConfig msg)
className c cfg = cfg { className = cfg.className <> " " <> c }

-- | Set id attribute
id :: forall msg. String -> ConfigMod (TextareaConfig msg)
id i cfg = cfg { id = Just i }

-- | Set name attribute
name :: forall msg. String -> ConfigMod (TextareaConfig msg)
name n cfg = cfg { name = Just n }

-- | Set input handler (receives current value)
onInput :: forall msg. (String -> msg) -> ConfigMod (TextareaConfig msg)
onInput handler cfg = cfg { onInput = Just handler }

-- | Set change handler (receives current value)
onChange :: forall msg. (String -> msg) -> ConfigMod (TextareaConfig msg)
onChange handler cfg = cfg { onChange = Just handler }

-- | Set focus handler
onFocus :: forall msg. msg -> ConfigMod (TextareaConfig msg)
onFocus handler cfg = cfg { onFocus = Just handler }

-- | Set blur handler
onBlur :: forall msg. msg -> ConfigMod (TextareaConfig msg)
onBlur handler cfg = cfg { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base textarea classes
baseClasses :: String
baseClasses =
  "flex min-h-[80px] w-full rounded-md border border-input bg-background " <>
  "px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground " <>
  "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring " <>
  "focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Error state classes
errorClasses :: String
errorClasses = "border-destructive focus-visible:ring-destructive"

-- | Render a textarea
textarea :: forall msg. Array (ConfigMod (TextareaConfig msg)) -> E.Element msg
textarea configMods =
  let
    cfg = foldl (\c f -> f c) defaultConfig configMods
    errorClass = if cfg.error then errorClasses else ""
    resizeClass = if cfg.autoResize then "resize-none overflow-hidden" else "resize-y"
    allClasses = baseClasses <> " " <> errorClass <> " " <> resizeClass <> " " <> cfg.className
  in
    E.textarea_
      ( [ E.class_ allClasses
        , E.placeholder cfg.placeholder
        , E.value cfg.value
        , E.attr "rows" (show cfg.minRows)
        ]
        <> disabledAttr cfg.disabled
        <> readonlyAttr cfg.readOnly
        <> requiredAttr cfg.required
        <> maybeAttr "id" cfg.id
        <> maybeAttr "name" cfg.name
        <> maxLengthAttr cfg.maxLength
        <> ariaInvalidAttr cfg.error
        <> maybeInputHandler cfg.onInput
        <> maybeChangeHandler cfg.onChange
        <> maybeFocusHandler cfg.onFocus
        <> maybeBlurHandler cfg.onBlur
      )
      [] -- textarea has no children, value is via attribute

-- | Textarea with label
textareaWithLabel :: forall msg.
  String ->
  Array (ConfigMod (TextareaConfig msg)) ->
  E.Element msg
textareaWithLabel labelText configMods =
  let
    cfg = foldl (\c f -> f c) defaultConfig configMods
    inputId = case cfg.id of
      Just i -> i
      Nothing -> "textarea-" <> labelText
    configWithId = configMods <> [ id inputId ]
  in
    E.div_
      [ E.class_ "space-y-2" ]
      [ -- Label
        E.label_
          [ E.class_ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70"
          , E.attr "for" inputId
          ]
          ( [ E.text labelText ]
            <> requiredIndicator cfg.required
          )
      -- Textarea
      , textarea configWithId
      -- Error message
      , errorMessageEl cfg
      ]

-- | Textarea with character counter
textareaWithCounter :: forall msg.
  Array (ConfigMod (TextareaConfig msg)) ->
  E.Element msg
textareaWithCounter configMods =
  let
    cfg = foldl (\c f -> f c) defaultConfig configMods
    currentLength = String.length cfg.value
    counterText = case cfg.maxLength of
      Just ml -> show currentLength <> " / " <> show ml
      Nothing -> show currentLength <> " characters"
    isOverLimit = case cfg.maxLength of
      Just ml -> currentLength > ml
      Nothing -> false
    counterClass = if isOverLimit then "text-destructive" else "text-muted-foreground"
  in
    E.div_
      [ E.class_ "space-y-1" ]
      [ textarea configMods
      , E.div_
          [ E.class_ "flex justify-end" ]
          [ E.span_
              [ E.class_ ("text-xs " <> counterClass) ]
              [ E.text counterText ]
          ]
      ]

-- | Full textarea field (label + textarea + counter + error)
textareaField :: forall msg.
  String ->
  Array (ConfigMod (TextareaConfig msg)) ->
  E.Element msg
textareaField labelText configMods =
  let
    cfg = foldl (\c f -> f c) defaultConfig configMods
    inputId = case cfg.id of
      Just i -> i
      Nothing -> "textarea-" <> labelText
    configWithId = configMods <> [ id inputId ]
    currentLength = String.length cfg.value
    isOverLimit = case cfg.maxLength of
      Just ml -> currentLength > ml
      Nothing -> false
  in
    E.div_
      [ E.class_ "space-y-2" ]
      [ -- Label
        E.label_
          [ E.class_ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70"
          , E.attr "for" inputId
          ]
          ( [ E.text labelText ]
            <> requiredIndicator cfg.required
          )
      -- Textarea
      , textarea configWithId
      -- Footer (error + counter)
      , E.div_
          [ E.class_ "flex justify-between" ]
          [ -- Error message
            errorMessageEl cfg
          -- Character counter
          , counterEl cfg.maxLength currentLength isOverLimit
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Attribute helpers for conditional attributes
maybeAttr :: forall msg. String -> Maybe String -> Array (E.Attribute msg)
maybeAttr _ Nothing = []
maybeAttr attrName (Just val) = [ E.attr attrName val ]

disabledAttr :: forall msg. Boolean -> Array (E.Attribute msg)
disabledAttr false = []
disabledAttr true = [ E.disabled true ]

readonlyAttr :: forall msg. Boolean -> Array (E.Attribute msg)
readonlyAttr false = []
readonlyAttr true = [ E.readonly true ]

requiredAttr :: forall msg. Boolean -> Array (E.Attribute msg)
requiredAttr false = []
requiredAttr true = [ E.required true ]

maxLengthAttr :: forall msg. Maybe Int -> Array (E.Attribute msg)
maxLengthAttr Nothing = []
maxLengthAttr (Just ml) = [ E.attr "maxlength" (show ml) ]

ariaInvalidAttr :: forall msg. Boolean -> Array (E.Attribute msg)
ariaInvalidAttr false = []
ariaInvalidAttr true = [ E.attr "aria-invalid" "true" ]

-- | Event handler helpers
maybeInputHandler :: forall msg. Maybe (String -> msg) -> Array (E.Attribute msg)
maybeInputHandler Nothing = []
maybeInputHandler (Just handler) = [ E.onInput handler ]

maybeChangeHandler :: forall msg. Maybe (String -> msg) -> Array (E.Attribute msg)
maybeChangeHandler Nothing = []
maybeChangeHandler (Just handler) = [ E.onChange handler ]

maybeFocusHandler :: forall msg. Maybe msg -> Array (E.Attribute msg)
maybeFocusHandler Nothing = []
maybeFocusHandler (Just handler) = [ E.onFocus handler ]

maybeBlurHandler :: forall msg. Maybe msg -> Array (E.Attribute msg)
maybeBlurHandler Nothing = []
maybeBlurHandler (Just handler) = [ E.onBlur handler ]

-- | Required field indicator
requiredIndicator :: forall msg. Boolean -> Array (E.Element msg)
requiredIndicator false = []
requiredIndicator true = [ E.span_ [ E.class_ "text-destructive ml-1" ] [ E.text "*" ] ]

-- | Error message element
errorMessageEl :: forall msg. TextareaConfig msg -> E.Element msg
errorMessageEl cfg =
  if cfg.error && cfg.errorMessage /= ""
    then E.p_ [ E.class_ "text-sm text-destructive" ] [ E.text cfg.errorMessage ]
    else E.empty

-- | Character counter element
counterEl :: forall msg. Maybe Int -> Int -> Boolean -> E.Element msg
counterEl Nothing _ _ = E.empty
counterEl (Just ml) currentLength isOverLimit =
  let
    counterClass = if isOverLimit then "text-destructive" else "text-muted-foreground"
    counterText = show currentLength <> " / " <> show ml
  in
    E.span_
      [ E.class_ ("text-xs " <> counterClass) ]
      [ E.text counterText ]
