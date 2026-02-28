-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // check-box
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Checkbox — Schema-native checkbox input component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property             | Pillar     | Type                      | CSS Output              |
-- | |----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor      | Color      | Color.RGB                 | background (checked)    |
-- | | borderColor          | Color      | Color.RGB                 | border-color            |
-- | | checkColor           | Color      | Color.RGB                 | check mark color        |
-- | | size                 | Dimension  | Device.Pixel              | width, height           |
-- | | borderRadius         | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth          | Dimension  | Device.Pixel              | border-width            |
-- | | transitionDuration   | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Checkbox as Checkbox
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic checkbox
-- | Checkbox.checkbox
-- |   [ Checkbox.isChecked true
-- |   , Checkbox.onToggle ToggleMsg
-- |   ]
-- |
-- | -- With brand atoms
-- | Checkbox.checkbox
-- |   [ Checkbox.isChecked state.accepted
-- |   , Checkbox.onToggle ToggleTerms
-- |   , Checkbox.backgroundColor brand.primaryColor
-- |   , Checkbox.borderColor brand.inputBorder
-- |   , Checkbox.checkColor brand.onPrimaryColor
-- |   ]
-- |
-- | -- With label
-- | Checkbox.checkboxWithLabel "Accept terms"
-- |   [ Checkbox.isChecked state.accepted
-- |   , Checkbox.onToggle ToggleTerms
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Checkbox
  ( -- * Main Components
    checkbox
  , checkboxWithLabel
  
  -- * Props
  , CheckboxProps
  , CheckboxProp
  , defaultProps
  
  -- * State Props
  , isChecked
  , isDisabled
  , checkboxId
  
  -- * Color Atoms
  , backgroundColor
  , borderColor
  , checkColor
  , labelColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , size
  
  -- * Typography Atoms
  , labelFontSize
  , labelFontWeight
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onToggle
  ) where

import Prelude
  ( show
  , (<>)
  , not
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
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Checkbox properties
type CheckboxProps msg =
  { -- State
    checked :: Boolean
  , disabled :: Boolean
  , id :: Maybe String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , checkColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , size :: Maybe Device.Pixel
  
  -- Typography atoms
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onToggle :: Maybe msg
  }

-- | Property modifier
type CheckboxProp msg = CheckboxProps msg -> CheckboxProps msg

-- | Default properties
defaultProps :: forall msg. CheckboxProps msg
defaultProps =
  { checked: false
  , disabled: false
  , id: Nothing
  , backgroundColor: Nothing
  , borderColor: Nothing
  , checkColor: Nothing
  , labelColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , size: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , transitionDuration: Nothing
  , onToggle: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set checked state
isChecked :: forall msg. Boolean -> CheckboxProp msg
isChecked c props = props { checked = c }

-- | Set disabled state
isDisabled :: forall msg. Boolean -> CheckboxProp msg
isDisabled d props = props { disabled = d }

-- | Set checkbox id
checkboxId :: forall msg. String -> CheckboxProp msg
checkboxId i props = props { id = Just i }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color when checked (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> CheckboxProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> CheckboxProp msg
borderColor c props = props { borderColor = Just c }

-- | Set check mark color (Color.RGB atom)
checkColor :: forall msg. Color.RGB -> CheckboxProp msg
checkColor c props = props { checkColor = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> CheckboxProp msg
labelColor c props = props { labelColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> CheckboxProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> CheckboxProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set checkbox size (Device.Pixel atom)
size :: forall msg. Device.Pixel -> CheckboxProp msg
size s props = props { size = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label font size (FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> CheckboxProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> CheckboxProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> CheckboxProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set toggle handler
onToggle :: forall msg. msg -> CheckboxProp msg
onToggle handler props = props { onToggle = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a checkbox
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | Uses a button+SVG pattern for better styling control.
checkbox :: forall msg. Array (CheckboxProp msg) -> E.Element msg
checkbox propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.button_
      (buildCheckboxAttrs props)
      [ if props.checked then checkmark props else E.empty ]

-- | Build checkbox attributes
buildCheckboxAttrs :: forall msg. CheckboxProps msg -> Array (E.Attribute msg)
buildCheckboxAttrs props =
  let
    -- Default colors
    defaultBgColor = Color.rgb 59 130 246   -- Blue
    defaultBorderColor = Color.rgb 203 213 225  -- Gray
    
    -- Background: colored when checked, transparent when unchecked
    bgColor = if props.checked
      then maybe defaultBgColor (\c -> c) props.backgroundColor
      else Color.rgb 255 255 255  -- White when unchecked
    
    brdColor = maybe defaultBorderColor (\c -> c) props.borderColor
    
    -- Size (default: 18px)
    sizeValue = maybe "18px" show props.size
    
    -- Border width (default: 2px)
    brdWidth = maybe "2px" show props.borderWidth
    
    -- Border radius (default: 4px)
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "4px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Transition
    transitionValue = maybe "150ms" show props.transitionDuration
    
    -- Core styles
    coreStyles =
      [ E.type_ "button"
      , E.role "checkbox"
      , E.attr "aria-checked" (if props.checked then "true" else "false")
      , E.disabled props.disabled
      , E.style "position" "relative"
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "flex-shrink" "0"
      , E.style "width" sizeValue
      , E.style "height" sizeValue
      , E.style "border-style" "solid"
      , E.style "border-width" brdWidth
      , E.style "border-color" (if props.checked then Color.toLegacyCss bgColor else Color.toLegacyCss brdColor)
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "transition" ("all " <> transitionValue <> " ease-out")
      , E.style "outline" "none"
      ]
    
    -- ID attribute
    idAttr = case props.id of
      Just i -> [ E.id_ i ]
      Nothing -> []
    
    -- Disabled opacity
    disabledStyle = if props.disabled
      then [ E.style "opacity" "0.5" ]
      else []
    
    -- Click handler
    clickHandler = case props.onToggle of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
  in
    coreStyles <> radiusStyle <> idAttr <> disabledStyle <> clickHandler

-- | Checkmark SVG icon
checkmark :: forall msg. CheckboxProps msg -> E.Element msg
checkmark props =
  let
    -- Default check color (white)
    defaultCheckColor = Color.rgb 255 255 255
    chkColor = maybe defaultCheckColor (\c -> c) props.checkColor
  in
    E.svg_
      [ E.attr "width" "12"
      , E.attr "height" "12"
      , E.attr "viewBox" "0 0 24 24"
      , E.attr "fill" "none"
      , E.attr "stroke" (Color.toLegacyCss chkColor)
      , E.attr "stroke-width" "3"
      , E.attr "stroke-linecap" "round"
      , E.attr "stroke-linejoin" "round"
      ]
      [ E.svgElement "polyline"
          [ E.attr "points" "20 6 9 17 4 12" ]
          []
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // labeled checkbox
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a checkbox with label
checkboxWithLabel :: forall msg. String -> Array (CheckboxProp msg) -> E.Element msg
checkboxWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    fieldId = maybe ("checkbox-" <> labelText) (\i -> i) props.id
    propsWithId = propMods <> [ checkboxId fieldId ]
    
    -- Label styles
    fontSizeStyle = case props.labelFontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.labelFontWeight of
      Nothing -> [ E.style "font-weight" "500" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    colorStyle = case props.labelColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
    
    cursorStyle = if props.disabled
      then [ E.style "cursor" "not-allowed", E.style "opacity" "0.7" ]
      else [ E.style "cursor" "pointer" ]
  in
    E.label_
      ( [ E.attr "for" fieldId
        , E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "gap" "8px"
        ]
        <> cursorStyle
      )
      [ checkbox propsWithId
      , E.span_
          ([ E.style "line-height" "1" ] <> fontSizeStyle <> fontWeightStyle <> colorStyle)
          [ E.text labelText ]
      ]
