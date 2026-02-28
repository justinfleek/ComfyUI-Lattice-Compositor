-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // toggle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toggle — Schema-native toggle button component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Toggle buttons are used for binary or multi-selection states.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background (unpressed)  |
-- | | pressedBackgroundColor| Color      | Color.RGB                 | background (pressed)    |
-- | | textColor             | Color      | Color.RGB                 | color                   |
-- | | pressedTextColor      | Color      | Color.RGB                 | color (pressed)         |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Toggle as Toggle
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Single toggle button
-- | Toggle.toggle
-- |   [ Toggle.pressed state.isBold
-- |   , Toggle.onPressedChange ToggleBold
-- |   ]
-- |   [ E.text "Bold" ]
-- |
-- | -- With brand atoms
-- | Toggle.toggle
-- |   [ Toggle.pressed state.isActive
-- |   , Toggle.pressedBackgroundColor brand.primaryColor
-- |   , Toggle.pressedTextColor brand.onPrimaryColor
-- |   ]
-- |   [ E.text "Active" ]
-- |
-- | -- Toggle group
-- | Toggle.toggleGroup [ Toggle.gap (Device.px 4.0) ]
-- |   [ Toggle.toggle [ Toggle.pressed (state.align == "left") ] [ E.text "Left" ]
-- |   , Toggle.toggle [ Toggle.pressed (state.align == "center") ] [ E.text "Center" ]
-- |   , Toggle.toggle [ Toggle.pressed (state.align == "right") ] [ E.text "Right" ]
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Toggle
  ( -- * Main Components
    toggle
  , toggleGroup
  
  -- * Props
  , ToggleProps
  , ToggleProp
  , GroupProps
  , GroupProp
  , defaultProps
  , defaultGroupProps
  
  -- * Identity Props
  , value
  , groupAriaLabel
  
  -- * State Props
  , pressed
  , isDisabled
  
  -- * Color Atoms
  , backgroundColor
  , pressedBackgroundColor
  , hoverBackgroundColor
  , textColor
  , pressedTextColor
  , hoverTextColor
  , borderColor
  , focusRingColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  , focusRingWidth
  
  -- * Dimension Atoms
  , height
  , paddingX
  , paddingY
  , gap
  
  -- * Typography Atoms
  , fontSize
  , fontWeight
  
  -- * Motion Atoms
  , transitionDuration
  , reducedMotion
  
  -- * Accessibility Props
  , ariaLabel
  
  -- * Behavior Props
  , onPressedChange
  , onKeyDown
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( show
  , (<>)
  , not
  , negate
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
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // toggle props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toggle button properties
type ToggleProps msg =
  { -- Identity (for UUID5 generation)
    value :: String
    
  -- State
  , pressed :: Boolean
  , disabled :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , pressedBackgroundColor :: Maybe Color.RGB
  , hoverBackgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , pressedTextColor :: Maybe Color.RGB
  , hoverTextColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  , focusRingWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Accessibility
  , ariaLabel :: Maybe String
  , reducedMotion :: Boolean
  
  -- Behavior
  , onPressedChange :: Maybe msg
  , onKeyDown :: Maybe (String -> msg)
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type ToggleProp msg = ToggleProps msg -> ToggleProps msg

-- | Default properties
defaultProps :: forall msg. ToggleProps msg
defaultProps =
  { value: ""
  , pressed: false
  , disabled: false
  , backgroundColor: Nothing
  , pressedBackgroundColor: Nothing
  , hoverBackgroundColor: Nothing
  , textColor: Nothing
  , pressedTextColor: Nothing
  , hoverTextColor: Nothing
  , borderColor: Nothing
  , focusRingColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , focusRingWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , transitionDuration: Nothing
  , ariaLabel: Nothing
  , reducedMotion: false
  , onPressedChange: Nothing
  , onKeyDown: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // group props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toggle group properties
type GroupProps msg =
  { -- Accessibility
    ariaLabel :: Maybe String
    
  -- Dimension atoms
  , gap :: Maybe Device.Pixel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Group property modifier
type GroupProp msg = GroupProps msg -> GroupProps msg

-- | Default group properties
defaultGroupProps :: forall msg. GroupProps msg
defaultGroupProps =
  { ariaLabel: Nothing
  , gap: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set toggle value (identifier for UUID5 generation)
-- |
-- | The value is used to generate a deterministic UUID5 id:
-- | `uuid5(nsToggle, value)` → same value always produces same id.
value :: forall msg. String -> ToggleProp msg
value v props = props { value = v }

-- | Set pressed state
pressed :: forall msg. Boolean -> ToggleProp msg
pressed p props = props { pressed = p }

-- | Set disabled state
isDisabled :: forall msg. Boolean -> ToggleProp msg
isDisabled d props = props { disabled = d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color when not pressed (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ToggleProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set background color when pressed (Color.RGB atom)
pressedBackgroundColor :: forall msg. Color.RGB -> ToggleProp msg
pressedBackgroundColor c props = props { pressedBackgroundColor = Just c }

-- | Set background color on hover (Color.RGB atom)
hoverBackgroundColor :: forall msg. Color.RGB -> ToggleProp msg
hoverBackgroundColor c props = props { hoverBackgroundColor = Just c }

-- | Set text color when not pressed (Color.RGB atom)
textColor :: forall msg. Color.RGB -> ToggleProp msg
textColor c props = props { textColor = Just c }

-- | Set text color when pressed (Color.RGB atom)
pressedTextColor :: forall msg. Color.RGB -> ToggleProp msg
pressedTextColor c props = props { pressedTextColor = Just c }

-- | Set text color on hover (Color.RGB atom)
hoverTextColor :: forall msg. Color.RGB -> ToggleProp msg
hoverTextColor c props = props { hoverTextColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> ToggleProp msg
borderColor c props = props { borderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> ToggleProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> ToggleProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> ToggleProp msg
borderWidth w props = props { borderWidth = Just w }

-- | Set focus ring width (Device.Pixel atom)
focusRingWidth :: forall msg. Device.Pixel -> ToggleProp msg
focusRingWidth w props = props { focusRingWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set toggle height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> ToggleProp msg
height h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> ToggleProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> ToggleProp msg
paddingY p props = props { paddingY = Just p }

-- | Set gap between group items (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> GroupProp msg
gap g props = props { gap = Just g }

-- | Set ARIA label for the toggle group
groupAriaLabel :: forall msg. String -> GroupProp msg
groupAriaLabel label props = props { ariaLabel = Just label }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> ToggleProp msg
fontSize s props = props { fontSize = Just s }

-- | Set font weight (FontWeight atom)
fontWeight :: forall msg. FontWeight.FontWeight -> ToggleProp msg
fontWeight w props = props { fontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> ToggleProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- | Enable reduced motion (disables transitions)
reducedMotion :: forall msg. Boolean -> ToggleProp msg
reducedMotion r props = props { reducedMotion = r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // prop builders: accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set ARIA label for screen readers
ariaLabel :: forall msg. String -> ToggleProp msg
ariaLabel label props = props { ariaLabel = Just label }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set press change handler
onPressedChange :: forall msg. msg -> ToggleProp msg
onPressedChange handler props = props { onPressedChange = Just handler }

-- | Set keyboard handler (receives key name: "Enter", "Space", "ArrowLeft", etc.)
onKeyDown :: forall msg. (String -> msg) -> ToggleProp msg
onKeyDown handler props = props { onKeyDown = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> ToggleProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a toggle button
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
toggle :: forall msg. Array (ToggleProp msg) -> Array (E.Element msg) -> E.Element msg
toggle propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.button_
      (buildToggleAttrs props)
      children

-- | Build toggle button attributes
buildToggleAttrs :: forall msg. ToggleProps msg -> Array (E.Attribute msg)
buildToggleAttrs props =
  let
    -- Generate deterministic ID from value using UUID5
    toggleId = UUID5.toString (UUID5.uuid5 UUID5.nsToggle props.value)
    
    -- Default colors
    defaultBgColor = Color.rgb 255 255 255        -- White
    defaultPressedBgColor = Color.rgb 226 232 240  -- Light gray
    defaultHoverBgColor = Color.rgb 241 245 249   -- Very light gray
    defaultTextColor = Color.rgb 71 85 105        -- Dark gray
    defaultFocusRingColor = Color.rgb 59 130 246  -- Blue
    
    -- Current colors based on pressed state
    currentBgColor = if props.pressed
      then maybe defaultPressedBgColor (\c -> c) props.pressedBackgroundColor
      else maybe defaultBgColor (\c -> c) props.backgroundColor
    
    currentTextColor = if props.pressed
      then maybe defaultTextColor (\c -> c) props.pressedTextColor
      else maybe defaultTextColor (\c -> c) props.textColor
    
    -- Hover colors (stored as CSS custom properties for :hover pseudo-class)
    hoverBgColor = maybe defaultHoverBgColor (\c -> c) props.hoverBackgroundColor
    hoverTxtColor = maybe currentTextColor (\c -> c) props.hoverTextColor
    
    -- Focus ring
    focusColor = maybe defaultFocusRingColor (\c -> c) props.focusRingColor
    focusWidth = maybe "2px" show props.focusRingWidth
    
    -- Border
    borderStyle = case props.borderColor of
      Nothing -> [ E.style "border" "1px solid rgba(0, 0, 0, 0.1)" ]
      Just bc ->
        let bw = maybe "1px" show props.borderWidth
        in [ E.style "border-style" "solid"
           , E.style "border-width" bw
           , E.style "border-color" (Color.toLegacyCss bc)
           ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "6px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Height
    heightStyle = case props.height of
      Nothing -> [ E.style "height" "36px" ]
      Just h -> [ E.style "height" (show h) ]
    
    -- Padding
    paddingStyle =
      let
        px = maybe "12px" show props.paddingX
        py = maybe "6px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Typography
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.fontWeight of
      Nothing -> [ E.style "font-weight" "500" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    -- Transition (respects reducedMotion)
    transitionValue = if props.reducedMotion
      then "none"
      else maybe "150ms" show props.transitionDuration
    
    -- ARIA label
    ariaLabelAttr = case props.ariaLabel of
      Nothing -> []
      Just label -> [ E.ariaLabel label ]
    
    -- CSS custom properties for hover/focus (runtime interprets these)
    customProperties =
      [ E.attr "data-hover-bg" (Color.toLegacyCss hoverBgColor)
      , E.attr "data-hover-color" (Color.toLegacyCss hoverTxtColor)
      , E.attr "data-focus-ring-color" (Color.toLegacyCss focusColor)
      , E.attr "data-focus-ring-width" focusWidth
      ]
    
    -- Core styles
    coreStyles =
      [ E.id_ toggleId
      , E.type_ "button"
      , E.attr "aria-pressed" (if props.pressed then "true" else "false")
      , E.attr "data-state" (if props.pressed then "on" else "off")
      , E.attr "data-value" props.value
      , E.disabled props.disabled
      , E.tabIndex 0
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "white-space" "nowrap"
      , E.style "background-color" (Color.toLegacyCss currentBgColor)
      , E.style "color" (Color.toLegacyCss currentTextColor)
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "transition" ("all " <> transitionValue <> " ease-out")
      , E.style "outline" "none"
      , E.style "user-select" "none"
      ]
    
    -- Disabled opacity
    disabledStyle = if props.disabled
      then [ E.style "opacity" "0.5", E.tabIndex (-1) ]
      else []
    
    -- Click handler
    clickHandler = case props.onPressedChange of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
    
    -- Keyboard handler (Space and Enter should toggle)
    keyboardHandler = case props.onKeyDown of
      Just handler -> if not props.disabled 
        then [ E.onKeyDown handler ]
        else []
      Nothing -> []
  in
    coreStyles 
    <> borderStyle 
    <> radiusStyle 
    <> heightStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> fontWeightStyle 
    <> ariaLabelAttr
    <> customProperties
    <> disabledStyle 
    <> clickHandler 
    <> keyboardHandler
    <> props.extraAttributes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // toggle group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a toggle group
-- |
-- | Container for multiple toggle buttons.
toggleGroup :: forall msg. Array (GroupProp msg) -> Array (E.Element msg) -> E.Element msg
toggleGroup propMods children =
  let
    props = foldl (\p f -> f p) defaultGroupProps propMods
    
    -- Gap
    gapValue = maybe "4px" show props.gap
    
    -- ARIA label
    ariaLabelAttr = case props.ariaLabel of
      Just label -> [ E.ariaLabel label ]
      Nothing -> []
  in
    E.div_
      ( [ E.role "group"
        , E.style "display" "inline-flex"
        , E.style "gap" gapValue
        ]
        <> ariaLabelAttr
        <> props.extraAttributes
      )
      children
