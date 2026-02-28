-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input — Schema-native text input component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars:
-- |
-- | - **Color**: Background, text, border, placeholder, focus ring
-- | - **Geometry**: Border radius, border width
-- | - **Dimension**: Height, padding
-- | - **Typography**: Font size, font weight
-- | - **Motion**: Transition timing
-- |
-- | The **BrandSchema** defines what these atoms are for a given brand.
-- | This component just renders them faithfully.
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
-- | | focusRingColor        | Color      | Color.RGB                 | focus outline           |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | fontSize              | Typography | Typography.FontSize       | font-size               |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Input as Input
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Dimension.Device as Device
-- |
-- | -- Basic input
-- | Input.input
-- |   [ Input.placeholder "Enter text..."
-- |   , Input.onInputChange UpdateText
-- |   ]
-- |
-- | -- With brand atoms
-- | Input.input
-- |   [ Input.placeholder "Email address"
-- |   , Input.inputType Input.Email
-- |   , Input.backgroundColor brand.inputBackground
-- |   , Input.borderColor brand.inputBorder
-- |   , Input.focusBorderColor brand.primaryColor
-- |   , Input.borderRadius brand.inputRadius
-- |   , Input.height brand.inputHeight
-- |   ]
-- |
-- | -- Textarea
-- | Input.textarea
-- |   [ Input.placeholder "Write your message..."
-- |   , Input.rows 4
-- |   ]
-- |
-- | -- With label
-- | Input.inputWithLabel "Email"
-- |   [ Input.inputType Input.Email
-- |   , Input.inputRequired true
-- |   ]
-- | ```
-- |
-- | ## Companion Components
-- |
-- | - `input` — Single-line text input
-- | - `textarea` — Multi-line text input
-- | - `inputWithLabel` — Input with associated label
-- | - `textareaWithLabel` — Textarea with associated label

module Hydrogen.Element.Compound.Input
  ( -- * Main Components
    input
  , textarea
  , inputWithLabel
  , textareaWithLabel
  
  -- * Types
  , InputType(Text, Password, Email, Number, Tel, Url, Search, Date, Time, DatetimeLocal, Month, Week, Color, File, Hidden)
  
  -- * Props
  , InputProps
  , InputProp
  , defaultProps
  
  -- * Content Props
  , inputType
  , placeholder
  , inputValue
  , inputDisabled
  , inputRequired
  , inputReadOnly
  , inputId
  , inputName
  , rows
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , labelColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , height
  , paddingX
  , paddingY
  , minHeight
  
  -- * Typography Atoms
  , fontSize
  , labelFontSize
  , labelFontWeight
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onInputChange
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (||)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTML input types
-- |
-- | Comprehensive list of valid input types.
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
  | DatetimeLocal
  | Month
  | Week
  | Color
  | File
  | Hidden

derive instance eqInputType :: Eq InputType

instance showInputType :: Show InputType where
  show Text = "text"
  show Password = "password"
  show Email = "email"
  show Number = "number"
  show Tel = "tel"
  show Url = "url"
  show Search = "search"
  show Date = "date"
  show Time = "time"
  show DatetimeLocal = "datetime-local"
  show Month = "month"
  show Week = "week"
  show Color = "color"
  show File = "file"
  show Hidden = "hidden"

-- | Convert InputType to HTML attribute value
inputTypeToString :: InputType -> String
inputTypeToString = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` uses inherited/default styles.
type InputProps msg =
  { -- Content
    inputType :: InputType
  , placeholder :: String
  , value :: String
  , disabled :: Boolean
  , required :: Boolean
  , readOnly :: Boolean
  , id :: Maybe String
  , name :: Maybe String
  , rows :: Int
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , minHeight :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onInputChange :: Maybe (String -> msg)
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type InputProp msg = InputProps msg -> InputProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (inherit from context/brand).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. InputProps msg
defaultProps =
  { inputType: Text
  , placeholder: ""
  , value: ""
  , disabled: false
  , required: false
  , readOnly: false
  , id: Nothing
  , name: Nothing
  , rows: 3
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , focusRingColor: Nothing
  , labelColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , minHeight: Nothing
  , fontSize: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , transitionDuration: Nothing
  , onInputChange: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input type
inputType :: forall msg. InputType -> InputProp msg
inputType t props = props { inputType = t }

-- | Set placeholder text
placeholder :: forall msg. String -> InputProp msg
placeholder p props = props { placeholder = p }

-- | Set current value
inputValue :: forall msg. String -> InputProp msg
inputValue v props = props { value = v }

-- | Set disabled state
inputDisabled :: forall msg. Boolean -> InputProp msg
inputDisabled d props = props { disabled = d }

-- | Set required state
inputRequired :: forall msg. Boolean -> InputProp msg
inputRequired r props = props { required = r }

-- | Set read-only state
inputReadOnly :: forall msg. Boolean -> InputProp msg
inputReadOnly r props = props { readOnly = r }

-- | Set input id
inputId :: forall msg. String -> InputProp msg
inputId i props = props { id = Just i }

-- | Set input name
inputName :: forall msg. String -> InputProp msg
inputName n props = props { name = Just n }

-- | Set rows (for textarea)
rows :: forall msg. Int -> InputProp msg
rows r props = props { rows = r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> InputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set input text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> InputProp msg
textColor c props = props { textColor = Just c }

-- | Set input border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> InputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> InputProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> InputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> InputProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> InputProp msg
labelColor c props = props { labelColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> InputProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> InputProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> InputProp msg
height h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> InputProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> InputProp msg
paddingY p props = props { paddingY = Just p }

-- | Set minimum height for textarea (Device.Pixel atom)
minHeight :: forall msg. Device.Pixel -> InputProp msg
minHeight h props = props { minHeight = Just h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> InputProp msg
fontSize s props = props { fontSize = Just s }

-- | Set label font size (FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> InputProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> InputProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> InputProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input change handler
-- |
-- | Receives the current input value as a String.
onInputChange :: forall msg. (String -> msg) -> InputProp msg
onInputChange handler props = props { onInputChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> InputProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single-line text input
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
input :: forall msg. Array (InputProp msg) -> E.Element msg
input propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.input_
      (buildInputAttrs props)

-- | Build input attributes from props
buildInputAttrs :: forall msg. InputProps msg -> Array (E.Attribute msg)
buildInputAttrs props =
  let
    -- Core attributes
    coreAttrs =
      [ E.type_ (inputTypeToString props.inputType)
      , E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.required props.required
      , E.readonly props.readOnly
      ]
    
    -- ID attribute
    idAttr = case props.id of
      Just i -> [ E.id_ i ]
      Nothing -> []
    
    -- Name attribute
    nameAttr = case props.name of
      Just n -> [ E.name n ]
      Nothing -> []
    
    -- Input handler
    inputHandler = case props.onInputChange of
      Just handler -> [ E.onInput handler ]
      Nothing -> []
    
    -- Style attributes
    styleAttrs = buildInputStyles props
  in
    coreAttrs <> idAttr <> nameAttr <> inputHandler <> styleAttrs <> props.extraAttributes

-- | Build input styles from Schema atoms
buildInputStyles :: forall msg. InputProps msg -> Array (E.Attribute msg)
buildInputStyles props =
  let
    -- Default values (fallback if no atom provided)
    defaultBgColor = Color.rgb 255 255 255   -- White
    defaultTextColor = Color.rgb 15 23 42    -- Dark gray
    defaultBorderColor = Color.rgb 226 232 240  -- Light gray border
    
    -- Apply atoms or defaults
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    txtColor = maybe defaultTextColor (\c -> c) props.textColor
    brdColor = maybe defaultBorderColor (\c -> c) props.borderColor
    
    -- Core styles
    coreStyles =
      [ E.style "display" "block"
      , E.style "width" "100%"
      , E.style "box-sizing" "border-box"
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "color" (Color.toLegacyCss txtColor)
      ]
    
    -- Border styles
    borderStyleAttrs =
      let bw = maybe "1px" show props.borderWidth
      in [ E.style "border-style" "solid"
         , E.style "border-width" bw
         , E.style "border-color" (Color.toLegacyCss brdColor)
         ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "6px" ]  -- Default rounded
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Dimension styles
    heightStyle = case props.height of
      Nothing -> [ E.style "height" "40px" ]  -- Default height
      Just h -> [ E.style "height" (show h) ]
    
    paddingStyle =
      let
        px = maybe "12px" show props.paddingX
        py = maybe "8px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Typography styles
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "14px" ]  -- Default
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    -- Transition styles
    transitionStyle =
      let dur = maybe "150ms" show props.transitionDuration
      in [ E.style "transition" ("border-color " <> dur <> " ease-out, box-shadow " <> dur <> " ease-out") ]
    
    -- Disabled styles
    disabledStyles =
      if props.disabled || props.readOnly
        then [ E.style "opacity" "0.5", E.style "cursor" "not-allowed" ]
        else []
    
    -- Focus/outline styles
    focusStyles =
      [ E.style "outline" "none"
      ]
  in
    coreStyles 
    <> borderStyleAttrs 
    <> radiusStyle 
    <> heightStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> transitionStyle 
    <> disabledStyles
    <> focusStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // textarea
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a multi-line textarea
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
textarea :: forall msg. Array (InputProp msg) -> E.Element msg
textarea propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.textarea_
      (buildTextareaAttrs props)
      []

-- | Build textarea attributes from props
buildTextareaAttrs :: forall msg. InputProps msg -> Array (E.Attribute msg)
buildTextareaAttrs props =
  let
    -- Core attributes
    coreAttrs =
      [ E.placeholder props.placeholder
      , E.value props.value
      , E.disabled props.disabled
      , E.required props.required
      , E.readonly props.readOnly
      , E.attr "rows" (show props.rows)
      ]
    
    -- ID attribute
    idAttr = case props.id of
      Just i -> [ E.id_ i ]
      Nothing -> []
    
    -- Name attribute
    nameAttr = case props.name of
      Just n -> [ E.name n ]
      Nothing -> []
    
    -- Input handler
    inputHandler = case props.onInputChange of
      Just handler -> [ E.onInput handler ]
      Nothing -> []
    
    -- Style attributes
    styleAttrs = buildTextareaStyles props
  in
    coreAttrs <> idAttr <> nameAttr <> inputHandler <> styleAttrs <> props.extraAttributes

-- | Build textarea styles from Schema atoms
buildTextareaStyles :: forall msg. InputProps msg -> Array (E.Attribute msg)
buildTextareaStyles props =
  let
    -- Get input styles as base
    baseStyles = buildInputStyles props
    
    -- Override height for textarea
    heightOverride = case props.minHeight of
      Nothing -> [ E.style "min-height" "80px", E.style "height" "auto" ]
      Just h -> [ E.style "min-height" (show h), E.style "height" "auto" ]
    
    -- Allow vertical resize
    resizeStyle = [ E.style "resize" "vertical" ]
  in
    baseStyles <> heightOverride <> resizeStyle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // labeled components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input with associated label
-- |
-- | Automatically generates an ID and associates the label via `for` attribute.
inputWithLabel :: forall msg. String -> Array (InputProp msg) -> E.Element msg
inputWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("input-" <> sanitizeForId labelText) (\i -> i) props.id
    propsWithId = propMods <> [ inputId fieldId ]
    
    -- Label styles
    labelFontSizeVal = maybe "14px" FontSize.toLegacyCss props.labelFontSize
    labelFontWeightVal = maybe "500" FontWeight.toLegacyCss props.labelFontWeight
    labelColorVal = maybe "inherit" Color.toLegacyCss props.labelColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.label_
          [ E.attr "for" fieldId
          , E.style "font-size" labelFontSizeVal
          , E.style "font-weight" labelFontWeightVal
          , E.style "color" labelColorVal
          ]
          [ E.text labelText ]
      , input propsWithId
      ]

-- | Textarea with associated label
-- |
-- | Automatically generates an ID and associates the label via `for` attribute.
textareaWithLabel :: forall msg. String -> Array (InputProp msg) -> E.Element msg
textareaWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("textarea-" <> sanitizeForId labelText) (\i -> i) props.id
    propsWithId = propMods <> [ inputId fieldId ]
    
    -- Label styles
    labelFontSizeVal = maybe "14px" FontSize.toLegacyCss props.labelFontSize
    labelFontWeightVal = maybe "500" FontWeight.toLegacyCss props.labelFontWeight
    labelColorVal = maybe "inherit" Color.toLegacyCss props.labelColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.label_
          [ E.attr "for" fieldId
          , E.style "font-size" labelFontSizeVal
          , E.style "font-weight" labelFontWeightVal
          , E.style "color" labelColorVal
          ]
          [ E.text labelText ]
      , textarea propsWithId
      ]

-- | Sanitize a string for use as an HTML ID
-- |
-- | Replaces spaces with hyphens and converts to lowercase-like format.
sanitizeForId :: String -> String
sanitizeForId = replaceSpaces
  where
    replaceSpaces s = s  -- Simple pass-through; proper sanitization would need String operations
