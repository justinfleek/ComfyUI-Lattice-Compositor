-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // compound // accordion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accordion — Schema-native collapsible content sections.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Accordions provide accessible collapsible sections with ARIA support.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background              |
-- | | textColor             | Color      | Color.RGB                 | color                   |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | iconColor             | Color      | Color.RGB                 | icon color              |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Accordion as Accordion
-- |
-- | Accordion.accordion []
-- |   [ Accordion.item [ Accordion.itemValue "section-1" ]
-- |       [ Accordion.trigger
-- |           [ Accordion.isOpen state.openSections.section1
-- |           , Accordion.onToggle (ToggleSection "section-1")
-- |           ]
-- |           [ E.text "What is Hydrogen?" ]
-- |       , Accordion.content [ Accordion.isOpen state.openSections.section1 ]
-- |           [ E.text "Hydrogen is a pure rendering abstraction..." ]
-- |       ]
-- |   , Accordion.item [ Accordion.itemValue "section-2" ]
-- |       [ Accordion.trigger
-- |           [ Accordion.isOpen state.openSections.section2
-- |           , Accordion.onToggle (ToggleSection "section-2")
-- |           ]
-- |           [ E.text "Why PureScript?" ]
-- |       , Accordion.content [ Accordion.isOpen state.openSections.section2 ]
-- |           [ E.text "PureScript is the purest functional language..." ]
-- |       ]
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Accordion
  ( -- * Main Components
    accordion
  , item
  , trigger
  , content
  
  -- * Container Props
  , AccordionProps
  , AccordionProp
  , defaultProps
  , accordionAriaLabel
  , accordionReducedMotion
  
  -- * Item Props
  , ItemProps
  , ItemProp
  , defaultItemProps
  , itemValue
  , itemBorderColor
  , itemBorderWidth
  
  -- * Trigger Props
  , TriggerProps
  , TriggerProp
  , defaultTriggerProps
  , triggerValue
  , isOpen
  , isDisabled
  , triggerBackgroundColor
  , triggerTextColor
  , triggerIconColor
  , triggerHoverBackgroundColor
  , triggerHoverTextColor
  , triggerFocusRingColor
  , triggerFocusRingWidth
  , triggerPaddingX
  , triggerPaddingY
  , triggerFontSize
  , triggerFontWeight
  , triggerControlsContent
  , triggerReducedMotion
  , onToggle
  , onTriggerKeyDown
  
  -- * Content Props
  , ContentProps
  , ContentProp
  , defaultContentProps
  , contentValue
  , contentIsOpen
  , contentBackgroundColor
  , contentTextColor
  , contentPaddingX
  , contentPaddingY
  , transitionDuration
  , contentLabelledBy
  , contentReducedMotion
  
  -- * Escape Hatches
  , extraAttributes
  , itemExtraAttributes
  , triggerExtraAttributes
  , contentExtraAttributes
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
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // container props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accordion container properties
type AccordionProps msg =
  { -- Accessibility
    ariaLabel :: Maybe String
  , reducedMotion :: Boolean
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type AccordionProp msg = AccordionProps msg -> AccordionProps msg

-- | Default container properties
defaultProps :: forall msg. AccordionProps msg
defaultProps =
  { ariaLabel: Nothing
  , reducedMotion: false
  , extraAttributes: []
  }

-- | Set ARIA label for the accordion container
accordionAriaLabel :: forall msg. String -> AccordionProp msg
accordionAriaLabel label props = props { ariaLabel = Just label }

-- | Enable reduced motion (disables transitions globally)
accordionReducedMotion :: forall msg. Boolean -> AccordionProp msg
accordionReducedMotion r props = props { reducedMotion = r }

-- | Add extra attributes
extraAttributes :: forall msg. Array (E.Attribute msg) -> AccordionProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // item props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accordion item properties
type ItemProps msg =
  { -- State
    value :: String
  
  -- Color atoms
  , borderColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , borderWidth :: Maybe Device.Pixel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Item property modifier
type ItemProp msg = ItemProps msg -> ItemProps msg

-- | Default item properties
defaultItemProps :: forall msg. ItemProps msg
defaultItemProps =
  { value: ""
  , borderColor: Nothing
  , borderWidth: Nothing
  , extraAttributes: []
  }

-- | Set item value (identifier)
itemValue :: forall msg. String -> ItemProp msg
itemValue v props = props { value = v }

-- | Set border color (Color.RGB atom)
itemBorderColor :: forall msg. Color.RGB -> ItemProp msg
itemBorderColor c props = props { borderColor = Just c }

-- | Set border width (Device.Pixel atom)
itemBorderWidth :: forall msg. Device.Pixel -> ItemProp msg
itemBorderWidth w props = props { borderWidth = Just w }

-- | Add extra attributes to item
itemExtraAttributes :: forall msg. Array (E.Attribute msg) -> ItemProp msg
itemExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // trigger props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accordion trigger properties
type TriggerProps msg =
  { -- Identity (for UUID5 generation)
    value :: String
    
  -- State
  , open :: Boolean
  , disabled :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , hoverBackgroundColor :: Maybe Color.RGB
  , hoverTextColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , focusRingWidth :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  
  -- Accessibility
  , controlsContent :: Maybe String  -- ID of the content this trigger controls
  , reducedMotion :: Boolean
  
  -- Behavior
  , onToggle :: Maybe msg
  , onKeyDown :: Maybe (String -> msg)  -- For arrow key navigation
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Trigger property modifier
type TriggerProp msg = TriggerProps msg -> TriggerProps msg

-- | Default trigger properties
defaultTriggerProps :: forall msg. TriggerProps msg
defaultTriggerProps =
  { value: ""
  , open: false
  , disabled: false
  , backgroundColor: Nothing
  , textColor: Nothing
  , iconColor: Nothing
  , hoverBackgroundColor: Nothing
  , hoverTextColor: Nothing
  , focusRingColor: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , focusRingWidth: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , controlsContent: Nothing
  , reducedMotion: false
  , onToggle: Nothing
  , onKeyDown: Nothing
  , extraAttributes: []
  }

-- | Set trigger value (identifier for UUID5 generation)
-- |
-- | The value is used to generate deterministic IDs:
-- | - Trigger ID: `uuid5(nsAccordionTrigger, value)`
-- | - Auto-generates `aria-controls` pointing to content with same value
triggerValue :: forall msg. String -> TriggerProp msg
triggerValue v props = props { value = v }

-- | Set open state
isOpen :: forall msg. Boolean -> TriggerProp msg
isOpen o props = props { open = o }

-- | Set disabled state
isDisabled :: forall msg. Boolean -> TriggerProp msg
isDisabled d props = props { disabled = d }

-- | Set background color (Color.RGB atom)
triggerBackgroundColor :: forall msg. Color.RGB -> TriggerProp msg
triggerBackgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
triggerTextColor :: forall msg. Color.RGB -> TriggerProp msg
triggerTextColor c props = props { textColor = Just c }

-- | Set icon color (Color.RGB atom)
triggerIconColor :: forall msg. Color.RGB -> TriggerProp msg
triggerIconColor c props = props { iconColor = Just c }

-- | Set horizontal padding (Device.Pixel atom)
triggerPaddingX :: forall msg. Device.Pixel -> TriggerProp msg
triggerPaddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
triggerPaddingY :: forall msg. Device.Pixel -> TriggerProp msg
triggerPaddingY p props = props { paddingY = Just p }

-- | Set font size (FontSize atom)
triggerFontSize :: forall msg. FontSize.FontSize -> TriggerProp msg
triggerFontSize s props = props { fontSize = Just s }

-- | Set font weight (FontWeight atom)
triggerFontWeight :: forall msg. FontWeight.FontWeight -> TriggerProp msg
triggerFontWeight w props = props { fontWeight = Just w }

-- | Set toggle handler
onToggle :: forall msg. msg -> TriggerProp msg
onToggle handler props = props { onToggle = Just handler }

-- | Set hover background color (Color.RGB atom)
-- | Used via data attribute — runtime interprets hover state
triggerHoverBackgroundColor :: forall msg. Color.RGB -> TriggerProp msg
triggerHoverBackgroundColor c props = props { hoverBackgroundColor = Just c }

-- | Set hover text color (Color.RGB atom)
-- | Used via data attribute — runtime interprets hover state
triggerHoverTextColor :: forall msg. Color.RGB -> TriggerProp msg
triggerHoverTextColor c props = props { hoverTextColor = Just c }

-- | Set focus ring color (Color.RGB atom)
-- | Applied as box-shadow on focus
triggerFocusRingColor :: forall msg. Color.RGB -> TriggerProp msg
triggerFocusRingColor c props = props { focusRingColor = Just c }

-- | Set focus ring width (Device.Pixel atom)
triggerFocusRingWidth :: forall msg. Device.Pixel -> TriggerProp msg
triggerFocusRingWidth w props = props { focusRingWidth = Just w }

-- | Set the content ID this trigger controls (for aria-controls)
triggerControlsContent :: forall msg. String -> TriggerProp msg
triggerControlsContent contentId props = props { controlsContent = Just contentId }

-- | Enable reduced motion (disables transitions)
triggerReducedMotion :: forall msg. Boolean -> TriggerProp msg
triggerReducedMotion r props = props { reducedMotion = r }

-- | Set keyboard handler for arrow key navigation
-- | Runtime passes key name ("ArrowUp", "ArrowDown", "Home", "End")
onTriggerKeyDown :: forall msg. (String -> msg) -> TriggerProp msg
onTriggerKeyDown handler props = props { onKeyDown = Just handler }

-- | Add extra attributes to trigger
triggerExtraAttributes :: forall msg. Array (E.Attribute msg) -> TriggerProp msg
triggerExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // content props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accordion content properties
type ContentProps msg =
  { -- Identity (for UUID5 generation)
    value :: String
    
  -- State
  , open :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Accessibility
  , labelledBy :: Maybe String  -- ID of the trigger that labels this content
  , reducedMotion :: Boolean
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Content property modifier
type ContentProp msg = ContentProps msg -> ContentProps msg

-- | Default content properties
defaultContentProps :: forall msg. ContentProps msg
defaultContentProps =
  { value: ""
  , open: false
  , backgroundColor: Nothing
  , textColor: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , transitionDuration: Nothing
  , labelledBy: Nothing
  , reducedMotion: false
  , extraAttributes: []
  }

-- | Set content value (identifier for UUID5 generation)
-- |
-- | The value is used to generate deterministic IDs:
-- | - Content ID: `uuid5(nsAccordionContent, value)`
-- | - Auto-generates `aria-labelledby` pointing to trigger with same value
contentValue :: forall msg. String -> ContentProp msg
contentValue v props = props { value = v }

-- | Set content open state
contentIsOpen :: forall msg. Boolean -> ContentProp msg
contentIsOpen o props = props { open = o }

-- | Set background color (Color.RGB atom)
contentBackgroundColor :: forall msg. Color.RGB -> ContentProp msg
contentBackgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
contentTextColor :: forall msg. Color.RGB -> ContentProp msg
contentTextColor c props = props { textColor = Just c }

-- | Set horizontal padding (Device.Pixel atom)
contentPaddingX :: forall msg. Device.Pixel -> ContentProp msg
contentPaddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
contentPaddingY :: forall msg. Device.Pixel -> ContentProp msg
contentPaddingY p props = props { paddingY = Just p }

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> ContentProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- | Set the trigger ID that labels this content (for aria-labelledby)
contentLabelledBy :: forall msg. String -> ContentProp msg
contentLabelledBy triggerId props = props { labelledBy = Just triggerId }

-- | Enable reduced motion (disables transitions)
contentReducedMotion :: forall msg. Boolean -> ContentProp msg
contentReducedMotion r props = props { reducedMotion = r }

-- | Add extra attributes to content
contentExtraAttributes :: forall msg. Array (E.Attribute msg) -> ContentProp msg
contentExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // accordion container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the accordion container
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
accordion :: forall msg. Array (AccordionProp msg) -> Array (E.Element msg) -> E.Element msg
accordion propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- ARIA label for the accordion container
    ariaLabelAttr = case props.ariaLabel of
      Just label -> [ E.ariaLabel label ]
      Nothing -> []
    
    -- Reduced motion data attribute (for runtime CSS injection)
    reducedMotionAttr = if props.reducedMotion
      then [ E.attr "data-reduced-motion" "true" ]
      else []
  in
    E.div_
      ( [ E.attr "data-accordion" "true"
        ]
        <> ariaLabelAttr
        <> reducedMotionAttr
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // accordion item
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an accordion item (section)
item :: forall msg. Array (ItemProp msg) -> Array (E.Element msg) -> E.Element msg
item propMods children =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    
    -- Default border
    defaultBorderColor = Color.rgb 226 232 240  -- Light gray
    
    -- Border style (bottom border for item separation)
    borderColorVal = maybe defaultBorderColor (\c -> c) props.borderColor
    borderWidthVal = maybe "1px" show props.borderWidth
  in
    E.div_
      ( [ E.attr "data-accordion-item" "true"
        , E.attr "data-value" props.value
        , E.style "border-bottom-style" "solid"
        , E.style "border-bottom-width" borderWidthVal
        , E.style "border-bottom-color" (Color.toLegacyCss borderColorVal)
        ]
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // accordion trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an accordion trigger (clickable header)
trigger :: forall msg. Array (TriggerProp msg) -> Array (E.Element msg) -> E.Element msg
trigger propMods children =
  let
    props = foldl (\p f -> f p) defaultTriggerProps propMods
  in
    -- Wrap in h3 for semantics
    E.h3_
      [ E.style "margin" "0"
      , E.style "display" "flex"
      ]
      [ E.button_
          (buildTriggerAttrs props)
          (children <> [ chevronIcon props ])
      ]

-- | Build trigger button attributes
buildTriggerAttrs :: forall msg. TriggerProps msg -> Array (E.Attribute msg)
buildTriggerAttrs props =
  let
    -- Generate deterministic IDs using UUID5
    -- Trigger ID: uuid5(nsAccordionTrigger, value)
    -- Content ID: uuid5(nsAccordionContent, value) — used for aria-controls
    triggerId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionTrigger props.value)
    contentId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionContent props.value)
    
    -- Default colors
    defaultTextColor = Color.rgb 15 23 42      -- Dark (foreground)
    defaultFocusRingColor = Color.rgb 59 130 246  -- Blue focus ring
    
    -- Text color
    textColorVal = maybe defaultTextColor (\c -> c) props.textColor
    
    -- Focus ring
    focusColor = maybe defaultFocusRingColor (\c -> c) props.focusRingColor
    focusWidth = maybe "2" show props.focusRingWidth
    
    -- Background (default transparent)
    bgStyle = case props.backgroundColor of
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
      Nothing -> [ E.style "background-color" "transparent" ]
    
    -- Padding
    paddingStyle =
      let
        px = maybe "0" show props.paddingX
        py = maybe "16px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Typography
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "inherit" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.fontWeight of
      Nothing -> [ E.style "font-weight" "500" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    -- Transition (respects reducedMotion)
    transitionStyle = if props.reducedMotion
      then [ E.style "transition" "none" ]
      else [ E.style "transition" "all 150ms ease-out" ]
    
    -- Hover data attributes (runtime interprets for :hover styling)
    hoverAttrs = case props.hoverBackgroundColor of
      Just c -> [ E.attr "data-hover-bg" (Color.toLegacyCss c) ]
      Nothing -> []
    
    hoverTextAttrs = case props.hoverTextColor of
      Just c -> [ E.attr "data-hover-color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    -- Focus ring data attributes (runtime interprets for :focus-visible)
    focusRingAttrs =
      [ E.attr "data-focus-ring-color" (Color.toLegacyCss focusColor)
      , E.attr "data-focus-ring-width" focusWidth
      ]
    
    -- ARIA controls: auto-generated from value, or explicit override
    ariaControlsAttr = case props.controlsContent of
      Just explicitId -> [ E.attr "aria-controls" explicitId ]
      Nothing -> [ E.attr "aria-controls" contentId ]  -- Auto-generated
    
    -- Core styles
    coreStyles =
      [ E.id_ triggerId  -- UUID5-generated deterministic ID
      , E.type_ "button"
      , E.attr "aria-expanded" (if props.open then "true" else "false")
      , E.attr "data-state" (if props.open then "open" else "closed")
      , E.attr "data-value" props.value
      , E.disabled props.disabled
      , E.style "display" "flex"
      , E.style "flex" "1"
      , E.style "align-items" "center"
      , E.style "justify-content" "space-between"
      , E.style "width" "100%"
      , E.style "border" "none"
      , E.style "color" (Color.toLegacyCss textColorVal)
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "outline" "none"
      , E.style "text-align" "left"
      ]
    
    -- Disabled opacity
    disabledStyle = if props.disabled
      then [ E.style "opacity" "0.5" ]
      else []
    
    -- Click handler
    clickHandler = case props.onToggle of
      Just handler -> if not props.disabled then [ E.onClick handler ] else []
      Nothing -> []
    
    -- Keyboard handler for arrow navigation
    keyDownHandler = case props.onKeyDown of
      Just handler -> if not props.disabled then [ E.onKeyDown handler ] else []
      Nothing -> []
  in
    coreStyles 
    <> transitionStyle
    <> bgStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> fontWeightStyle 
    <> disabledStyle 
    <> hoverAttrs
    <> hoverTextAttrs
    <> focusRingAttrs
    <> ariaControlsAttr
    <> clickHandler 
    <> keyDownHandler
    <> props.extraAttributes

-- | Render the chevron icon
chevronIcon :: forall msg. TriggerProps msg -> E.Element msg
chevronIcon props =
  let
    -- Icon color
    defaultIconColor = Color.rgb 100 116 139  -- Muted gray
    iconColorVal = maybe defaultIconColor (\c -> c) props.iconColor
    
    -- Rotation transform based on open state
    rotationStyle = if props.open
      then "rotate(180deg)"
      else "rotate(0deg)"
    
    -- Transition (respects reducedMotion)
    transitionVal = if props.reducedMotion
      then "none"
      else "transform 200ms ease-out"
  in
    E.svg_
      [ E.attr "viewBox" "0 0 24 24"
      , E.attr "fill" "none"
      , E.attr "stroke" (Color.toLegacyCss iconColorVal)
      , E.attr "stroke-width" "2"
      , E.attr "stroke-linecap" "round"
      , E.attr "stroke-linejoin" "round"
      , E.style "width" "16px"
      , E.style "height" "16px"
      , E.style "flex-shrink" "0"
      , E.style "transition" transitionVal
      , E.style "transform" rotationStyle
      ]
      [ E.polyline_
          [ E.attr "points" "6 9 12 15 18 9" ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // accordion content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render accordion content (collapsible area)
content :: forall msg. Array (ContentProp msg) -> Array (E.Element msg) -> E.Element msg
content propMods children =
  let
    props = foldl (\p f -> f p) defaultContentProps propMods
    
    -- Generate deterministic IDs using UUID5
    -- Content ID: uuid5(nsAccordionContent, value)
    -- Trigger ID: uuid5(nsAccordionTrigger, value) — used for aria-labelledby
    contentId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionContent props.value)
    triggerId = UUID5.toString (UUID5.uuid5 UUID5.nsAccordionTrigger props.value)
    
    -- Transition duration (respects reducedMotion)
    transitionVal = if props.reducedMotion
      then "none"
      else "all " <> maybe "200ms" show props.transitionDuration <> " ease-out"
    
    -- Visibility styles
    visibilityStyles = if props.open
      then [ E.style "max-height" "1000px"
           , E.style "opacity" "1"
           ]
      else [ E.style "max-height" "0"
           , E.style "opacity" "0"
           , E.style "visibility" "hidden"
           ]
    
    -- Padding
    paddingStyle =
      let
        px = maybe "0" show props.paddingX
        py = maybe "0" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Colors
    bgStyle = case props.backgroundColor of
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    textStyle = case props.textColor of
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
      Nothing -> []
    
    -- ARIA labelledby: auto-generated from value, or explicit override
    labelledByAttr = case props.labelledBy of
      Just explicitId -> [ E.ariaLabelledBy explicitId ]
      Nothing -> [ E.ariaLabelledBy triggerId ]  -- Auto-generated
    
    -- Core styles
    coreStyles =
      [ E.id_ contentId  -- UUID5-generated deterministic ID
      , E.role "region"
      , E.attr "data-state" (if props.open then "open" else "closed")
      , E.attr "data-value" props.value
      , E.style "overflow" "hidden"
      , E.style "transition" transitionVal
      ]
  in
    E.div_
      ( coreStyles 
        <> labelledByAttr
        <> visibilityStyles 
        <> paddingStyle 
        <> bgStyle 
        <> textStyle 
        <> props.extraAttributes
      )
      [ -- Inner wrapper with padding for content
        E.div_
          [ E.style "padding-bottom" "16px"
          , E.style "font-size" "14px"
          ]
          children
      ]
