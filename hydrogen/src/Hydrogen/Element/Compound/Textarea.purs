-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // text-area
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Textarea — Schema-native multi-line text input component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars.
-- | When an atom is `Nothing`, no style is emitted — the element inherits
-- | from its parent or browser defaults.
-- |
-- | **No hardcoded CSS values.** The BrandSchema provides all visual atoms.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background-color        |
-- | | textColor             | Color      | Color.RGB                 | color                   |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | placeholderColor      | Color      | Color.RGB                 | ::placeholder color     |
-- | | focusBorderColor      | Color      | Color.RGB                 | :focus border-color     |
-- | | focusRingColor        | Color      | Color.RGB                 | :focus outline          |
-- | | errorBorderColor      | Color      | Color.RGB                 | error border-color      |
-- | | errorTextColor        | Color      | Color.RGB                 | error message color     |
-- | | labelColor            | Color      | Color.RGB                 | label text color        |
-- | | counterColor          | Color      | Color.RGB                 | counter text color      |
-- | | requiredColor         | Color      | Color.RGB                 | required asterisk color |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | minHeight             | Dimension  | Device.Pixel              | min-height              |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | fontSize              | Typography | FontSize.FontSize         | font-size               |
-- | | lineHeight            | Typography | LineHeight.LineHeight     | line-height             |
-- | | labelFontSize         | Typography | FontSize.FontSize         | label font-size         |
-- | | labelFontWeight       | Typography | FontWeight.FontWeight     | label font-weight       |
-- | | counterFontSize       | Typography | FontSize.FontSize         | counter font-size       |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Textarea as Textarea
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic textarea (inherits all visual properties from context)
-- | Textarea.textarea
-- |   [ Textarea.placeholder "Enter your message..."
-- |   , Textarea.onTextareaInput UpdateMessage
-- |   ]
-- |
-- | -- With brand atoms
-- | Textarea.textarea
-- |   [ Textarea.placeholder "Enter your message..."
-- |   , Textarea.backgroundColor brand.inputBackground
-- |   , Textarea.textColor brand.foreground
-- |   , Textarea.borderColor brand.inputBorder
-- |   , Textarea.borderRadius brand.inputRadius
-- |   , Textarea.fontSize brand.bodyFontSize
-- |   , Textarea.onTextareaInput UpdateMessage
-- |   ]
-- |
-- | -- Full field with label, counter, and error
-- | Textarea.textareaField "Bio"
-- |   [ Textarea.maxLength 280
-- |   , Textarea.textareaValue state.bio
-- |   , Textarea.textareaRequired true
-- |   , Textarea.labelColor brand.foreground
-- |   , Textarea.errorTextColor brand.destructive
-- |   , Textarea.requiredColor brand.destructive
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Textarea
  ( -- * Textarea Components
    textarea
  , textareaWithLabel
  , textareaWithCounter
  , textareaField
  
  -- * Props
  , TextareaProps
  , TextareaProp
  , defaultProps
  
  -- * Content Props
  , placeholder
  , textareaValue
  , textareaDisabled
  , textareaReadOnly
  , textareaRequired
  , textareaId
  , textareaName
  , minRows
  , maxRows
  , maxLength
  , autoResize
  
  -- * Error Props
  , textareaError
  , errorMessage
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , errorBorderColor
  , errorTextColor
  , labelColor
  , counterColor
  , requiredColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , minHeight
  , paddingX
  , paddingY
  
  -- * Typography Atoms
  , fontSize
  , lineHeight
  , labelFontSize
  , labelFontWeight
  , counterFontSize
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onTextareaInput
  , onTextareaChange
  , onTextareaFocus
  , onTextareaBlur
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( show
  , (<>)
  , (>)
  , (||)
  , (/=)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.LineHeight as LineHeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Textarea properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type TextareaProps msg =
  { -- Content
    placeholder :: String
  , value :: String
  , disabled :: Boolean
  , readOnly :: Boolean
  , required :: Boolean
  , id :: Maybe String
  , name :: Maybe String
  , minRows :: Int
  , maxRows :: Int
  , maxLength :: Maybe Int
  , autoResize :: Boolean
  
  -- Error state
  , error :: Boolean
  , errorMsg :: String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , errorBorderColor :: Maybe Color.RGB
  , errorTextColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  , counterColor :: Maybe Color.RGB
  , requiredColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , minHeight :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , lineHeight :: Maybe LineHeight.LineHeight
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  , counterFontSize :: Maybe FontSize.FontSize
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onInput :: Maybe (String -> msg)
  , onChange :: Maybe (String -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type TextareaProp msg = TextareaProps msg -> TextareaProps msg

-- | Default textarea properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. TextareaProps msg
defaultProps =
  { placeholder: ""
  , value: ""
  , disabled: false
  , readOnly: false
  , required: false
  , id: Nothing
  , name: Nothing
  , minRows: 3
  , maxRows: 10
  , maxLength: Nothing
  , autoResize: false
  , error: false
  , errorMsg: ""
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , focusRingColor: Nothing
  , errorBorderColor: Nothing
  , errorTextColor: Nothing
  , labelColor: Nothing
  , counterColor: Nothing
  , requiredColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , minHeight: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , fontSize: Nothing
  , lineHeight: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , counterFontSize: Nothing
  , transitionDuration: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set placeholder text
placeholder :: forall msg. String -> TextareaProp msg
placeholder p props = props { placeholder = p }

-- | Set current value
textareaValue :: forall msg. String -> TextareaProp msg
textareaValue v props = props { value = v }

-- | Set disabled state
textareaDisabled :: forall msg. Boolean -> TextareaProp msg
textareaDisabled d props = props { disabled = d }

-- | Set read-only state
textareaReadOnly :: forall msg. Boolean -> TextareaProp msg
textareaReadOnly r props = props { readOnly = r }

-- | Set required state
textareaRequired :: forall msg. Boolean -> TextareaProp msg
textareaRequired r props = props { required = r }

-- | Set textarea id
textareaId :: forall msg. String -> TextareaProp msg
textareaId i props = props { id = Just i }

-- | Set textarea name
textareaName :: forall msg. String -> TextareaProp msg
textareaName n props = props { name = Just n }

-- | Set minimum rows
minRows :: forall msg. Int -> TextareaProp msg
minRows r props = props { minRows = r }

-- | Set maximum rows (for auto-resize)
maxRows :: forall msg. Int -> TextareaProp msg
maxRows r props = props { maxRows = r }

-- | Set maximum character length
maxLength :: forall msg. Int -> TextareaProp msg
maxLength l props = props { maxLength = Just l }

-- | Enable auto-resize to content
autoResize :: forall msg. Boolean -> TextareaProp msg
autoResize a props = props { autoResize = a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: error
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set error state
textareaError :: forall msg. Boolean -> TextareaProp msg
textareaError e props = props { error = e }

-- | Set error message (also sets error state to true)
errorMessage :: forall msg. String -> TextareaProp msg
errorMessage msg props = props { errorMsg = msg, error = true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> TextareaProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> TextareaProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> TextareaProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> TextareaProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> TextareaProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> TextareaProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set error state border color (Color.RGB atom)
errorBorderColor :: forall msg. Color.RGB -> TextareaProp msg
errorBorderColor c props = props { errorBorderColor = Just c }

-- | Set error message text color (Color.RGB atom)
errorTextColor :: forall msg. Color.RGB -> TextareaProp msg
errorTextColor c props = props { errorTextColor = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> TextareaProp msg
labelColor c props = props { labelColor = Just c }

-- | Set counter text color (Color.RGB atom)
counterColor :: forall msg. Color.RGB -> TextareaProp msg
counterColor c props = props { counterColor = Just c }

-- | Set required asterisk color (Color.RGB atom)
requiredColor :: forall msg. Color.RGB -> TextareaProp msg
requiredColor c props = props { requiredColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> TextareaProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> TextareaProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set minimum height (Device.Pixel atom)
minHeight :: forall msg. Device.Pixel -> TextareaProp msg
minHeight h props = props { minHeight = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> TextareaProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> TextareaProp msg
paddingY p props = props { paddingY = Just p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> TextareaProp msg
fontSize s props = props { fontSize = Just s }

-- | Set line height (LineHeight atom)
lineHeight :: forall msg. LineHeight.LineHeight -> TextareaProp msg
lineHeight h props = props { lineHeight = Just h }

-- | Set label font size (FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> TextareaProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> TextareaProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- | Set counter font size (FontSize atom)
counterFontSize :: forall msg. FontSize.FontSize -> TextareaProp msg
counterFontSize s props = props { counterFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> TextareaProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input handler (fires on each keystroke)
-- |
-- | Receives the current textarea value as a String.
onTextareaInput :: forall msg. (String -> msg) -> TextareaProp msg
onTextareaInput handler props = props { onInput = Just handler }

-- | Set change handler (fires on blur after change)
-- |
-- | Receives the current textarea value as a String.
onTextareaChange :: forall msg. (String -> msg) -> TextareaProp msg
onTextareaChange handler props = props { onChange = Just handler }

-- | Set focus handler (fires when textarea receives focus)
onTextareaFocus :: forall msg. msg -> TextareaProp msg
onTextareaFocus handler props = props { onFocus = Just handler }

-- | Set blur handler (fires when textarea loses focus)
onTextareaBlur :: forall msg. msg -> TextareaProp msg
onTextareaBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> TextareaProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a textarea
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
textarea :: forall msg. Array (TextareaProp msg) -> E.Element msg
textarea propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.textarea_
      (buildTextareaAttrs props)
      []

-- | Build textarea attributes from props
buildTextareaAttrs :: forall msg. TextareaProps msg -> Array (E.Attribute msg)
buildTextareaAttrs props =
  let
    -- Core attributes
    coreAttrs =
      [ E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.readonly props.readOnly
      , E.required props.required
      , E.attr "rows" (show props.minRows)
      ]
    
    -- ID attribute
    idAttr = maybe [] (\i -> [ E.id_ i ]) props.id
    
    -- Name attribute
    nameAttr = maybe [] (\n -> [ E.name n ]) props.name
    
    -- Max length attribute
    maxLengthAttr = maybe [] (\ml -> [ E.attr "maxlength" (show ml) ]) props.maxLength
    
    -- ARIA attributes for error state
    ariaAttrs = 
      if props.error
        then [ E.attr "aria-invalid" "true" ]
        else []
    
    -- Input handler
    inputHandler = maybe [] (\handler -> [ E.onInput handler ]) props.onInput
    
    -- Change handler
    changeHandler = maybe [] (\handler -> [ E.onChange handler ]) props.onChange
    
    -- Focus handler
    focusHandler = maybe [] (\handler -> [ E.onFocus handler ]) props.onFocus
    
    -- Blur handler
    blurHandler = maybe [] (\handler -> [ E.onBlur handler ]) props.onBlur
    
    -- Style attributes
    styleAttrs = buildTextareaStyles props
  in
    coreAttrs 
    <> idAttr 
    <> nameAttr 
    <> maxLengthAttr
    <> ariaAttrs
    <> inputHandler 
    <> changeHandler
    <> focusHandler
    <> blurHandler
    <> styleAttrs 
    <> props.extraAttributes

-- | Build textarea styles from Schema atoms
-- |
-- | **Pure Schema-native approach**: Only include styles for atoms that are
-- | set (`Just`). When `Nothing`, no style is emitted — the element inherits
-- | from parent/context/brand or uses browser defaults.
buildTextareaStyles :: forall msg. TextareaProps msg -> Array (E.Attribute msg)
buildTextareaStyles props =
  let
    -- Core layout styles (structural, not visual)
    layoutStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "font-family" "inherit"
      ]
    
    -- Color styles (only emit if atom provided)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.backgroundColor
    txtStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.textColor
    
    -- Border color (error state overrides normal)
    borderColorAtom = 
      if props.error
        then props.errorBorderColor
        else props.borderColor
    borderColorStyle = maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) borderColorAtom
    
    -- Border width and style
    borderWidthStyle = maybe [] (\w -> [E.style "border-width" (show w)]) props.borderWidth
    borderStyleAttr = 
      case props.borderWidth of
        Just _ -> [E.style "border-style" "solid"]
        Nothing -> 
          case props.borderColor of
            Just _ -> [E.style "border-style" "solid"]
            Nothing -> 
              case props.errorBorderColor of
                Just _ -> [E.style "border-style" "solid"]
                Nothing -> []
    
    -- Border radius
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.borderRadius
    
    -- Dimension styles
    heightStyle = maybe [] (\h -> [E.style "min-height" (show h)]) props.minHeight
    
    paddingXStyle = maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.paddingX
    paddingYStyle = maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.paddingY
    
    -- Typography styles
    fontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
    lineHeightStyle = maybe [] (\h -> [E.style "line-height" (LineHeight.toLegacyCss h)]) props.lineHeight
    
    -- Transition styles
    transitionStyle = maybe [] 
      (\d -> [E.style "transition" ("border-color " <> show d <> " ease-out, box-shadow " <> show d <> " ease-out")]) 
      props.transitionDuration
    
    -- Resize behavior
    resizeStyle =
      if props.autoResize
        then [ E.style "resize" "none", E.style "overflow" "hidden" ]
        else [ E.style "resize" "vertical" ]
    
    -- Disabled/readonly styles
    disabledStyles =
      if props.disabled || props.readOnly
        then [ E.style "opacity" "0.5", E.style "cursor" "not-allowed" ]
        else []
    
    -- Focus styles (outline handled by browser/CSS)
    focusStyles = [ E.style "outline" "none" ]
  in
    layoutStyles 
    <> bgStyle 
    <> txtStyle 
    <> borderStyleAttr
    <> borderWidthStyle
    <> borderColorStyle 
    <> radiusStyle 
    <> heightStyle 
    <> paddingXStyle 
    <> paddingYStyle
    <> fontSizeStyle 
    <> lineHeightStyle
    <> transitionStyle 
    <> resizeStyle
    <> disabledStyles
    <> focusStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // labeled components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Textarea with associated label
-- |
-- | Automatically generates an ID and associates the label via `for` attribute.
-- | All visual properties come from Schema atoms — no hardcoded values.
textareaWithLabel :: forall msg. String -> Array (TextareaProp msg) -> E.Element msg
textareaWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("textarea-" <> labelText) (\i -> i) props.id
    propsWithId = propMods <> [ textareaId fieldId ]
    
    -- Label styles (only emit if atoms provided)
    labelFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.labelFontSize
    labelFontWeightStyle = maybe [] (\w -> [E.style "font-weight" (FontWeight.toLegacyCss w)]) props.labelFontWeight
    labelColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.labelColor
    
    -- Required asterisk (only emit color if atom provided)
    requiredColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.requiredColor
    requiredSpan = 
      if props.required
        then E.span_ ([ E.style "margin-left" "4px" ] <> requiredColorStyle) [ E.text "*" ]
        else E.empty
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.label_
          ([ E.attr "for" fieldId ] <> labelFontSizeStyle <> labelFontWeightStyle <> labelColorStyle)
          [ E.text labelText
          , requiredSpan
          ]
      , textarea propsWithId
      , if props.error
          then renderErrorMessage props
          else E.empty
      ]

-- | Textarea with character counter
-- |
-- | Shows current character count and optional limit.
-- | All visual properties come from Schema atoms — no hardcoded values.
textareaWithCounter :: forall msg. Array (TextareaProp msg) -> E.Element msg
textareaWithCounter propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    currentLength = String.length props.value
    
    -- Build counter text
    counterText = case props.maxLength of
      Just ml -> show currentLength <> " / " <> show ml
      Nothing -> show currentLength <> " characters"
    
    -- Determine if over limit
    isOverLimit = case props.maxLength of
      Just ml -> currentLength > ml
      Nothing -> false
    
    -- Counter styles (use error color if over limit, else counter color)
    counterColorAtom = 
      if isOverLimit
        then props.errorTextColor
        else props.counterColor
    counterColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) counterColorAtom
    counterFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.counterFontSize
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ textarea propMods
      , E.div_
          [ E.style "display" "flex"
          , E.style "justify-content" "flex-end"
          ]
          [ E.span_
              (counterFontSizeStyle <> counterColorStyle)
              [ E.text counterText ]
          ]
      ]

-- | Full textarea field (label + textarea + counter + error)
-- |
-- | Combines label, textarea, character counter, and error message.
-- | All visual properties come from Schema atoms — no hardcoded values.
textareaField :: forall msg. String -> Array (TextareaProp msg) -> E.Element msg
textareaField labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("textarea-" <> labelText) (\i -> i) props.id
    propsWithId = propMods <> [ textareaId fieldId ]
    
    currentLength = String.length props.value
    
    -- Build counter text
    counterText = case props.maxLength of
      Just ml -> show currentLength <> " / " <> show ml
      Nothing -> ""
    
    -- Determine if over limit
    isOverLimit = case props.maxLength of
      Just ml -> currentLength > ml
      Nothing -> false
    
    -- Label styles (only emit if atoms provided)
    labelFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.labelFontSize
    labelFontWeightStyle = maybe [] (\w -> [E.style "font-weight" (FontWeight.toLegacyCss w)]) props.labelFontWeight
    labelColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.labelColor
    
    -- Required asterisk (only emit color if atom provided)
    requiredColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.requiredColor
    requiredSpan = 
      if props.required
        then E.span_ ([ E.style "margin-left" "4px" ] <> requiredColorStyle) [ E.text "*" ]
        else E.empty
    
    -- Counter styles
    counterColorAtom = 
      if isOverLimit
        then props.errorTextColor
        else props.counterColor
    counterColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) counterColorAtom
    counterFontSizeStyle = maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.counterFontSize
    
    -- Show counter only if maxLength is set
    showCounter = case props.maxLength of
      Just _ -> true
      Nothing -> false
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ -- Label
        E.label_
          ([ E.attr "for" fieldId ] <> labelFontSizeStyle <> labelFontWeightStyle <> labelColorStyle)
          [ E.text labelText
          , requiredSpan
          ]
      -- Textarea
      , textarea propsWithId
      -- Footer (error + counter)
      , E.div_
          [ E.style "display" "flex"
          , E.style "justify-content" "space-between"
          , E.style "align-items" "center"
          ]
          [ -- Error message (left side)
            if props.error
              then renderErrorMessage props
              else E.empty
          -- Character counter (right side)
          , if showCounter
              then E.span_
                ([ E.style "margin-left" "auto" ] <> counterFontSizeStyle <> counterColorStyle)
                [ E.text counterText ]
              else E.empty
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render error message
-- |
-- | Only emits color style if errorTextColor atom is provided.
renderErrorMessage :: forall msg. TextareaProps msg -> E.Element msg
renderErrorMessage props =
  let
    errorColorStyle = maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.errorTextColor
  in
    if props.errorMsg /= ""
      then E.p_
        ([ E.style "margin" "0" ] <> errorColorStyle)
        [ E.text props.errorMsg ]
      else E.empty
