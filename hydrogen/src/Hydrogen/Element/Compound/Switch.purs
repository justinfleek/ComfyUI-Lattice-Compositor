-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // switch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Switch — Schema-native toggle switch component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property             | Pillar     | Type                      | CSS Output              |
-- | |----------------------|------------|---------------------------|-------------------------|
-- | | trackColorOff        | Color      | Color.RGB                 | background (unchecked)  |
-- | | trackColorOn         | Color      | Color.RGB                 | background (checked)    |
-- | | thumbColor           | Color      | Color.RGB                 | thumb background        |
-- | | width                | Dimension  | Device.Pixel              | track width             |
-- | | height               | Dimension  | Device.Pixel              | track height            |
-- | | thumbSize            | Dimension  | Device.Pixel              | thumb diameter          |
-- | | transitionDuration   | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Switch as Switch
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic switch
-- | Switch.switch
-- |   [ Switch.isChecked true
-- |   , Switch.onToggle ToggleHandler
-- |   ]
-- |
-- | -- With brand atoms
-- | Switch.switch
-- |   [ Switch.isChecked state.enabled
-- |   , Switch.onToggle ToggleNotifs
-- |   , Switch.trackColorOn brand.primaryColor
-- |   , Switch.trackColorOff brand.switchTrack
-- |   , Switch.thumbColor brand.switchThumb
-- |   ]
-- |
-- | -- With label
-- | Switch.switchWithLabel "Enable notifications"
-- |   [ Switch.isChecked state.enabled
-- |   , Switch.onToggle ToggleNotifs
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Switch
  ( -- * Main Components
    switch
  , switchWithLabel
  
  -- * Props
  , SwitchProps
  , SwitchProp
  , defaultProps
  
  -- * State Props
  , isChecked
  , isDisabled
  
  -- * Color Atoms
  , trackColorOff
  , trackColorOn
  , thumbColor
  , labelColor
  
  -- * Dimension Atoms
  , width
  , height
  , thumbSize
  
  -- * Typography Atoms
  , labelFontSize
  , labelFontWeight
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onToggle
  
  -- * Escape Hatch
  , extraAttributes
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
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Switch properties
type SwitchProps msg =
  { -- State
    checked :: Boolean
  , disabled :: Boolean
  
  -- Color atoms
  , trackColorOff :: Maybe Color.RGB
  , trackColorOn :: Maybe Color.RGB
  , thumbColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , width :: Maybe Device.Pixel
  , height :: Maybe Device.Pixel
  , thumbSize :: Maybe Device.Pixel
  
  -- Typography atoms
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onToggle :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type SwitchProp msg = SwitchProps msg -> SwitchProps msg

-- | Default properties
defaultProps :: forall msg. SwitchProps msg
defaultProps =
  { checked: false
  , disabled: false
  , trackColorOff: Nothing
  , trackColorOn: Nothing
  , thumbColor: Nothing
  , labelColor: Nothing
  , width: Nothing
  , height: Nothing
  , thumbSize: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , transitionDuration: Nothing
  , onToggle: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set checked state
isChecked :: forall msg. Boolean -> SwitchProp msg
isChecked c props = props { checked = c }

-- | Set disabled state
isDisabled :: forall msg. Boolean -> SwitchProp msg
isDisabled d props = props { disabled = d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track color when unchecked (Color.RGB atom)
trackColorOff :: forall msg. Color.RGB -> SwitchProp msg
trackColorOff c props = props { trackColorOff = Just c }

-- | Set track color when checked (Color.RGB atom)
trackColorOn :: forall msg. Color.RGB -> SwitchProp msg
trackColorOn c props = props { trackColorOn = Just c }

-- | Set thumb color (Color.RGB atom)
thumbColor :: forall msg. Color.RGB -> SwitchProp msg
thumbColor c props = props { thumbColor = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> SwitchProp msg
labelColor c props = props { labelColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track width (Device.Pixel atom)
width :: forall msg. Device.Pixel -> SwitchProp msg
width w props = props { width = Just w }

-- | Set track height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> SwitchProp msg
height h props = props { height = Just h }

-- | Set thumb size/diameter (Device.Pixel atom)
thumbSize :: forall msg. Device.Pixel -> SwitchProp msg
thumbSize s props = props { thumbSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label font size (FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> SwitchProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> SwitchProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> SwitchProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set toggle handler
onToggle :: forall msg. msg -> SwitchProp msg
onToggle handler props = props { onToggle = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> SwitchProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a switch toggle
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
switch :: forall msg. Array (SwitchProp msg) -> E.Element msg
switch propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.button_
      (buildSwitchAttrs props)
      [ buildThumb props ]

-- | Build switch track attributes
buildSwitchAttrs :: forall msg. SwitchProps msg -> Array (E.Attribute msg)
buildSwitchAttrs props =
  let
    -- Default colors
    defaultOffColor = Color.rgb 203 213 225  -- Gray
    defaultOnColor = Color.rgb 59 130 246   -- Blue
    
    trackCol = if props.checked
      then maybe defaultOnColor (\c -> c) props.trackColorOn
      else maybe defaultOffColor (\c -> c) props.trackColorOff
    
    -- Dimensions (default: 44x24)
    widthValue = maybe "44px" show props.width
    heightValue = maybe "24px" show props.height
    
    -- Transition
    transitionValue = maybe "150ms" show props.transitionDuration
    
    -- Core styles
    coreStyles =
      [ E.type_ "button"
      , E.role "switch"
      , E.attr "aria-checked" (if props.checked then "true" else "false")
      , E.disabled props.disabled
      , E.style "position" "relative"
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "flex-shrink" "0"
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "width" widthValue
      , E.style "height" heightValue
      , E.style "border-radius" "9999px"
      , E.style "border" "2px solid transparent"
      , E.style "background-color" (Color.toLegacyCss trackCol)
      , E.style "transition" ("background-color " <> transitionValue <> " ease-out")
      , E.style "outline" "none"
      ]
    
    -- Disabled opacity
    disabledStyle = if props.disabled
      then [ E.style "opacity" "0.5" ]
      else []
    
    -- Click handler
    clickHandler = case props.onToggle of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
  in
    coreStyles <> disabledStyle <> clickHandler <> props.extraAttributes

-- | Build thumb element
buildThumb :: forall msg. SwitchProps msg -> E.Element msg
buildThumb props =
  let
    -- Default thumb color
    defaultThumbColor = Color.rgb 255 255 255  -- White
    thumbCol = maybe defaultThumbColor (\c -> c) props.thumbColor
    
    -- Thumb size (default: 20px)
    thumbSizeValue = maybe "20px" show props.thumbSize
    
    -- Calculate translation (track width - thumb size - padding)
    -- Default: 44 - 20 - 4 = 20px
    translateValue = if props.checked then "20px" else "0px"
    
    -- Transition
    transitionValue = maybe "150ms" show props.transitionDuration
  in
    E.span_
      [ E.style "pointer-events" "none"
      , E.style "display" "block"
      , E.style "width" thumbSizeValue
      , E.style "height" thumbSizeValue
      , E.style "border-radius" "50%"
      , E.style "background-color" (Color.toLegacyCss thumbCol)
      , E.style "box-shadow" "0 1px 3px rgba(0, 0, 0, 0.2)"
      , E.style "transform" ("translateX(" <> translateValue <> ")")
      , E.style "transition" ("transform " <> transitionValue <> " ease-out")
      ]
      []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // labeled switch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a switch with label
switchWithLabel :: forall msg. String -> Array (SwitchProp msg) -> E.Element msg
switchWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
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
      ( [ E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "gap" "12px"
        ]
        <> cursorStyle
      )
      [ switch propMods
      , E.span_
          ([ E.style "line-height" "1" ] <> fontSizeStyle <> fontWeightStyle <> colorStyle)
          [ E.text labelText ]
      ]
