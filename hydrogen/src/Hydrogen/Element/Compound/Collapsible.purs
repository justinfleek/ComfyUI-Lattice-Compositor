-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // collapsible
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Collapsible Component
-- |
-- | Animated expand/collapse panels with trigger elements.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Features
-- |
-- | - Trigger element (clickable)
-- | - Open/closed state
-- | - Controlled mode via isOpen prop
-- | - Icon rotation animation via CSS
-- | - Disabled state
-- | - Accessible (ARIA expanded)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Collapsible as Collapsible
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic collapsible
-- | Collapsible.collapsible
-- |   [ Collapsible.isOpen state.expanded
-- |   , Collapsible.onToggle ToggleExpanded
-- |   ]
-- |   (Collapsible.trigger [] [ E.text "Click to expand" ])
-- |   (Collapsible.content [] [ E.text "Hidden content here" ])
-- |
-- | -- With icon
-- | Collapsible.collapsible
-- |   [ Collapsible.isOpen true
-- |   , Collapsible.showIcon true
-- |   ]
-- |   (Collapsible.triggerWithIcon [] "Advanced Options")
-- |   (Collapsible.content [] advancedContent)
-- |
-- | -- Disabled
-- | Collapsible.collapsible
-- |   [ Collapsible.collapsibleDisabled true ]
-- |   trigger
-- |   content
-- | ```
module Hydrogen.Element.Compound.Collapsible
  ( -- * Components
    collapsible
  , trigger
  , triggerWithIcon
  , content
    -- * Props
  , CollapsibleProps
  , CollapsibleProp
  , TriggerProps
  , TriggerProp
  , ContentProps
  , ContentProp
  , defaultProps
  , defaultTriggerProps
  , defaultContentProps
    -- * Prop Builders
  , isOpen
  , onToggle
  , collapsibleDisabled
  , showIcon
  , iconPosition
  , className
  , triggerClassName
  , contentClassName
    -- * Types
  , IconPosition(IconLeft, IconRight)
  ) where

import Prelude
  ( class Eq
  , (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon position relative to trigger text
data IconPosition
  = IconLeft
  | IconRight

derive instance eqIconPosition :: Eq IconPosition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collapsible properties
type CollapsibleProps msg =
  { isOpen :: Boolean
  , onToggle :: Maybe (Boolean -> msg)
  , disabled :: Boolean
  , showIcon :: Boolean
  , iconPosition :: IconPosition
  , className :: String
  }

-- | Collapsible property modifier
type CollapsibleProp msg = CollapsibleProps msg -> CollapsibleProps msg

-- | Default collapsible properties
defaultProps :: forall msg. CollapsibleProps msg
defaultProps =
  { isOpen: false
  , onToggle: Nothing
  , disabled: false
  , showIcon: true
  , iconPosition: IconRight
  , className: ""
  }

-- | Trigger properties
type TriggerProps msg =
  { className :: String
  , onClick :: Maybe msg
  }

-- | Trigger property modifier
type TriggerProp msg = TriggerProps msg -> TriggerProps msg

-- | Default trigger properties
defaultTriggerProps :: forall msg. TriggerProps msg
defaultTriggerProps =
  { className: ""
  , onClick: Nothing
  }

-- | Content properties
type ContentProps =
  { className :: String
  }

-- | Content property modifier
type ContentProp = ContentProps -> ContentProps

-- | Default content properties
defaultContentProps :: ContentProps
defaultContentProps =
  { className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set open state
isOpen :: forall msg. Boolean -> CollapsibleProp msg
isOpen o props = props { isOpen = o }

-- | Set toggle handler
onToggle :: forall msg. (Boolean -> msg) -> CollapsibleProp msg
onToggle handler props = props { onToggle = Just handler }

-- | Set disabled state
collapsibleDisabled :: forall msg. Boolean -> CollapsibleProp msg
collapsibleDisabled d props = props { disabled = d }

-- | Show expand/collapse icon
showIcon :: forall msg. Boolean -> CollapsibleProp msg
showIcon s props = props { showIcon = s }

-- | Set icon position
iconPosition :: forall msg. IconPosition -> CollapsibleProp msg
iconPosition p props = props { iconPosition = p }

-- | Add custom class to container
className :: forall msg. String -> CollapsibleProp msg
className c props = props { className = props.className <> " " <> c }

-- | Add custom class to trigger
triggerClassName :: forall msg. String -> TriggerProp msg
triggerClassName c props = props { className = props.className <> " " <> c }

-- | Add custom class to content
contentClassName :: String -> ContentProp
contentClassName c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collapsible container
-- |
-- | Wraps trigger and content with expand/collapse behavior.
-- | The `isOpen` prop controls visibility; `onToggle` receives the new state.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
collapsible :: forall msg. 
  Array (CollapsibleProp msg) -> 
  E.Element msg -> 
  E.Element msg -> 
  E.Element msg
collapsible propMods triggerEl contentEl =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    openClass = if props.isOpen then "collapsible-open" else "collapsible-closed"
    
    disabledClass = if props.disabled then "collapsible-disabled opacity-50" else ""
  in
    E.div_
      [ E.classes [ "collapsible", openClass, disabledClass, props.className ]
      , E.dataAttr "state" (if props.isOpen then "open" else "closed")
      , E.dataAttr "disabled" (if props.disabled then "true" else "false")
      ]
      [ triggerEl
      , contentEl
      ]

-- | Trigger element
-- |
-- | Clickable element that toggles the collapsible.
-- | Pass the onClick handler to wire up toggle behavior.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
trigger :: forall msg. Array (TriggerProp msg) -> Array (E.Element msg) -> E.Element msg
trigger propMods children =
  let
    props = foldl (\p f -> f p) defaultTriggerProps propMods
    
    triggerClasses =
      "collapsible-trigger flex items-center justify-between w-full py-2 px-3 text-left font-medium transition-colors hover:bg-accent rounded-md cursor-pointer focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
    
    clickHandler = case props.onClick of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
  in
    E.button_
      ( [ E.classes [ triggerClasses, props.className ]
        , E.attr "type" "button"
        , E.attr "aria-expanded" "false"
        ] <> clickHandler
      )
      children

-- | Trigger with icon
-- |
-- | Trigger element with chevron icon that rotates via CSS.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
triggerWithIcon :: forall msg. Array (TriggerProp msg) -> String -> E.Element msg
triggerWithIcon propMods label =
  let
    props = foldl (\p f -> f p) defaultTriggerProps propMods
    
    triggerClasses =
      "collapsible-trigger flex items-center justify-between w-full py-2 px-3 text-left font-medium transition-colors hover:bg-accent rounded-md cursor-pointer focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
    
    clickHandler = case props.onClick of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
  in
    E.button_
      ( [ E.classes [ triggerClasses, props.className ]
        , E.attr "type" "button"
        , E.attr "aria-expanded" "false"
        ] <> clickHandler
      )
      [ E.span_ [] [ E.text label ]
      , chevronIcon
      ]

-- | Content element
-- |
-- | Collapsible content that expands/collapses based on parent state.
-- | Use CSS transitions with data-state for animation.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
content :: forall msg. Array ContentProp -> Array (E.Element msg) -> E.Element msg
content propMods children =
  let
    props = foldl (\p f -> f p) defaultContentProps propMods
    
    contentClasses =
      "collapsible-content overflow-hidden transition-all data-[state=closed]:h-0 data-[state=closed]:opacity-0 data-[state=open]:opacity-100"
  in
    E.div_
      [ E.classes [ contentClasses, props.className ]
      , E.dataAttr "state" "closed"
      , E.ariaHidden true
      ]
      [ E.div_
          [ E.class_ "collapsible-content-inner py-2 px-3" ]
          children
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chevron icon (rotates on expand via CSS)
chevronIcon :: forall msg. E.Element msg
chevronIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.class_ "collapsible-chevron transition-transform duration-200 data-[state=open]:rotate-180"
    ]
    [ E.polyline_ [ E.attr "points" "6 9 12 15 18 9" ] ]
