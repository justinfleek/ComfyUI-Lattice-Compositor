-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // radio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Radio — Schema-native radio button component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property             | Pillar     | Type                      | CSS Output              |
-- | |----------------------|------------|---------------------------|-------------------------|
-- | | selectedColor        | Color      | Color.RGB                 | fill (selected)         |
-- | | borderColor          | Color      | Color.RGB                 | border-color            |
-- | | size                 | Dimension  | Device.Pixel              | width, height           |
-- | | gap                  | Dimension  | Device.Pixel              | gap between items       |
-- | | transitionDuration   | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Radio as Radio
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Single radio
-- | Radio.radio
-- |   [ Radio.isChecked true
-- |   , Radio.onSelect SelectOption
-- |   , Radio.selectedColor brand.primaryColor
-- |   ]
-- |
-- | -- Radio group
-- | Radio.radioGroup
-- |   [ Radio.groupName "size"
-- |   , Radio.groupValue state.selectedSize
-- |   , Radio.onValueChange SetSize
-- |   ]
-- |   [ Radio.radioItem "sm" [] [ E.text "Small" ]
-- |   , Radio.radioItem "md" [] [ E.text "Medium" ]
-- |   , Radio.radioItem "lg" [] [ E.text "Large" ]
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Radio
  ( -- * Main Components
    radio
  , radioWithLabel
  , radioGroup
  , radioItem
  
  -- * Types
  , Orientation(Horizontal, Vertical)
  
  -- * Radio Props
  , RadioProps
  , RadioProp
  , defaultProps
  
  -- * Group Props
  , RadioGroupProps
  , RadioGroupProp
  , defaultGroupProps
  
  -- * Radio Prop Builders
  , isChecked
  , isDisabled
  , radioName
  , radioValue
  
  -- * Group Prop Builders
  , groupName
  , groupValue
  , orientation
  , groupDisabled
  , onValueChange
  
  -- * Color Atoms
  , selectedColor
  , borderColor
  , labelColor
  
  -- * Dimension Atoms
  , size
  , gap
  
  -- * Typography Atoms
  , labelFontSize
  , labelFontWeight
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior
  , onSelect
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radio group orientation
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

instance showOrientation :: Show Orientation where
  show Horizontal = "horizontal"
  show Vertical = "vertical"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // radio props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radio button properties
type RadioProps msg =
  { -- State
    checked :: Boolean
  , disabled :: Boolean
  , name :: Maybe String
  , value :: Maybe String
  
  -- Color atoms
  , selectedColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , size :: Maybe Device.Pixel
  
  -- Typography atoms
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onSelect :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type RadioProp msg = RadioProps msg -> RadioProps msg

-- | Default properties
defaultProps :: forall msg. RadioProps msg
defaultProps =
  { checked: false
  , disabled: false
  , name: Nothing
  , value: Nothing
  , selectedColor: Nothing
  , borderColor: Nothing
  , labelColor: Nothing
  , size: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , transitionDuration: Nothing
  , onSelect: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // group props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radio group properties
type RadioGroupProps msg =
  { -- Group state
    name :: String
  , value :: String
  , orientation :: Orientation
  , disabled :: Boolean
  
  -- Color atoms
  , selectedColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , size :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Typography atoms
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onValueChange :: Maybe (String -> msg)
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Group property modifier
type RadioGroupProp msg = RadioGroupProps msg -> RadioGroupProps msg

-- | Default group properties
defaultGroupProps :: forall msg. RadioGroupProps msg
defaultGroupProps =
  { name: ""
  , value: ""
  , orientation: Vertical
  , disabled: false
  , selectedColor: Nothing
  , borderColor: Nothing
  , labelColor: Nothing
  , size: Nothing
  , gap: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , transitionDuration: Nothing
  , onValueChange: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // prop builders: radio state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set checked state
isChecked :: forall msg. Boolean -> RadioProp msg
isChecked c props = props { checked = c }

-- | Set disabled state
isDisabled :: forall msg. Boolean -> RadioProp msg
isDisabled d props = props { disabled = d }

-- | Set radio name (for grouping)
radioName :: forall msg. String -> RadioProp msg
radioName n props = props { name = Just n }

-- | Set radio value
radioValue :: forall msg. String -> RadioProp msg
radioValue v props = props { value = Just v }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // prop builders: group state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set group name
groupName :: forall msg. String -> RadioGroupProp msg
groupName n props = props { name = n }

-- | Set currently selected value
groupValue :: forall msg. String -> RadioGroupProp msg
groupValue v props = props { value = v }

-- | Set group orientation
orientation :: forall msg. Orientation -> RadioGroupProp msg
orientation o props = props { orientation = o }

-- | Set group disabled state
groupDisabled :: forall msg. Boolean -> RadioGroupProp msg
groupDisabled d props = props { disabled = d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set selected/checked color (Color.RGB atom)
selectedColor :: forall msg. Color.RGB -> RadioProp msg
selectedColor c props = props { selectedColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> RadioProp msg
borderColor c props = props { borderColor = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> RadioProp msg
labelColor c props = props { labelColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set radio button size (Device.Pixel atom)
size :: forall msg. Device.Pixel -> RadioProp msg
size s props = props { size = Just s }

-- | Set gap between group items (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> RadioGroupProp msg
gap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label font size (FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> RadioProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> RadioProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> RadioProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set select handler
onSelect :: forall msg. msg -> RadioProp msg
onSelect handler props = props { onSelect = Just handler }

-- | Set value change handler (for groups)
onValueChange :: forall msg. (String -> msg) -> RadioGroupProp msg
onValueChange handler props = props { onValueChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> RadioProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a radio button
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
radio :: forall msg. Array (RadioProp msg) -> E.Element msg
radio propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.button_
      (buildRadioAttrs props)
      [ if props.checked then innerDot props else E.empty ]

-- | Build radio button attributes
buildRadioAttrs :: forall msg. RadioProps msg -> Array (E.Attribute msg)
buildRadioAttrs props =
  let
    -- Default colors
    defaultSelectedColor = Color.rgb 59 130 246  -- Blue
    defaultBorderColor = Color.rgb 203 213 225   -- Gray
    
    brdColor = maybe defaultBorderColor (\c -> c) props.borderColor
    selColor = maybe defaultSelectedColor (\c -> c) props.selectedColor
    
    -- Use selected color for border when checked
    currentBorderColor = if props.checked then selColor else brdColor
    
    -- Size (default: 18px)
    sizeValue = maybe "18px" show props.size
    
    -- Transition
    transitionValue = maybe "150ms" show props.transitionDuration
    
    -- Core styles
    coreStyles =
      [ E.type_ "button"
      , E.role "radio"
      , E.attr "aria-checked" (if props.checked then "true" else "false")
      , E.disabled props.disabled
      , E.style "position" "relative"
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "flex-shrink" "0"
      , E.style "width" sizeValue
      , E.style "height" sizeValue
      , E.style "border-radius" "50%"
      , E.style "border" ("2px solid " <> Color.toLegacyCss currentBorderColor)
      , E.style "background-color" "transparent"
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "transition" ("all " <> transitionValue <> " ease-out")
      , E.style "outline" "none"
      ]
    
    -- Disabled opacity
    disabledStyle = if props.disabled
      then [ E.style "opacity" "0.5" ]
      else []
    
    -- Click handler
    clickHandler = case props.onSelect of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
  in
    coreStyles <> disabledStyle <> clickHandler <> props.extraAttributes

-- | Inner dot for checked state
innerDot :: forall msg. RadioProps msg -> E.Element msg
innerDot props =
  let
    defaultSelectedColor = Color.rgb 59 130 246
    selColor = maybe defaultSelectedColor (\c -> c) props.selectedColor
  in
    E.span_
      [ E.style "display" "block"
      , E.style "width" "10px"
      , E.style "height" "10px"
      , E.style "border-radius" "50%"
      , E.style "background-color" (Color.toLegacyCss selColor)
      ]
      []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // labeled radio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a radio button with label
radioWithLabel :: forall msg. String -> Array (RadioProp msg) -> E.Element msg
radioWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Label styles
    fontSizeStyle = case props.labelFontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.labelFontWeight of
      Nothing -> [ E.style "font-weight" "400" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    colorStyle = case props.labelColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
    
    cursorStyle = if props.disabled
      then [ E.style "cursor" "not-allowed", E.style "opacity" "0.7" ]
      else [ E.style "cursor" "pointer" ]
  in
    E.label_
      ( [ E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "gap" "8px"
        ]
        <> cursorStyle
      )
      [ radio propMods
      , E.span_
          ([ E.style "line-height" "1.4" ] <> fontSizeStyle <> fontWeightStyle <> colorStyle)
          [ E.text labelText ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // radio group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a radio group
-- |
-- | Container for radio items with automatic selection management.
radioGroup :: forall msg. Array (RadioGroupProp msg) -> Array (E.Element msg) -> E.Element msg
radioGroup propMods children =
  let
    props = foldl (\p f -> f p) defaultGroupProps propMods
    
    -- Layout direction
    flexDirection = case props.orientation of
      Horizontal -> "row"
      Vertical -> "column"
    
    -- Gap
    gapValue = maybe "12px" show props.gap
  in
    E.div_
      ( [ E.role "radiogroup"
        , E.style "display" "flex"
        , E.style "flex-direction" flexDirection
        , E.style "gap" gapValue
        ]
        <> props.extraAttributes
      )
      children

-- | Create a radio item within a group
-- |
-- | Use this inside radioGroup. The value is used to match against groupValue.
radioItem :: forall msg. String -> Array (RadioProp msg) -> Array (E.Element msg) -> E.Element msg
radioItem itemValue propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Label styles
    fontSizeStyle = case props.labelFontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.labelFontWeight of
      Nothing -> [ E.style "font-weight" "400" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    colorStyle = case props.labelColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
    
    cursorStyle = if props.disabled
      then [ E.style "cursor" "not-allowed", E.style "opacity" "0.7" ]
      else [ E.style "cursor" "pointer" ]
    
    -- Build radio with value
    radioProps = propMods <> [ radioValue itemValue ]
  in
    E.label_
      ( [ E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "gap" "8px"
        ]
        <> cursorStyle
      )
      [ radio radioProps
      , E.span_
          ([ E.style "line-height" "1.4" ] <> fontSizeStyle <> fontWeightStyle <> colorStyle)
          children
      ]
