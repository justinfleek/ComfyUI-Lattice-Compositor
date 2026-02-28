-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // ui // collapsible
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Collapsible Component — Pure Element Version
-- |
-- | Animated expand/collapse panels with trigger elements.
-- | Renders using the pure Element abstraction for target-agnostic UI.
-- |
-- | ## Features
-- |
-- | - Trigger element (clickable)
-- | - Open/closed state via props
-- | - Icon rotation via CSS data attributes
-- | - Disabled state
-- | - Accessible (ARIA expanded)
-- | - Lazy content rendering option
-- |
-- | ## Usage with Halogen
-- |
-- | ```purescript
-- | import Hydrogen.UI.Collapsible as Collapsible
-- | import Hydrogen.Target.Halogen as TH
-- |
-- | myCollapsible :: Collapsible.Element Action
-- | myCollapsible = Collapsible.collapsible
-- |   [ Collapsible.isOpen state.expanded
-- |   , Collapsible.onToggle ToggleExpanded
-- |   ]
-- |   (Collapsible.trigger [] [ E.text "Settings" ])
-- |   (Collapsible.content [] [ settingsContent ])
-- |
-- | render :: State -> H.ComponentHTML Action Slots m
-- | render state = TH.toHalogen myCollapsible
-- | ```
-- |
-- | ## Usage for Static Rendering
-- |
-- | ```purescript
-- | import Hydrogen.UI.Collapsible as Collapsible
-- | import Hydrogen.Target.Static as TS
-- |
-- | html :: String
-- | html = TS.render (Collapsible.collapsible
-- |   [ Collapsible.isOpen true ]
-- |   (Collapsible.trigger [] [ E.text "FAQ" ])
-- |   (Collapsible.content [] [ E.text "Answer here" ]))
-- | ```
module Hydrogen.UI.Collapsible
  ( -- * Components
    collapsible
  , trigger
  , triggerWithIcon
  , content
  
  -- * Configuration
  , CollapsibleConfig
  , TriggerConfig
  , ContentConfig
  , defaultConfig
  , defaultTriggerConfig
  , defaultContentConfig
  
  -- * Config Modifiers
  , isOpen
  , onToggle
  , disabled
  , showIcon
  , iconPosition
  , lazyRender
  , className
  , triggerClassName
  , contentClassName
  
  -- * Types
  , IconPosition(IconLeft, IconRight)
  ) where

import Prelude
  ( class Eq
  , (<>)
  , (&&)
  , not
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
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collapsible configuration
type CollapsibleConfig msg =
  { isOpen :: Boolean
  , onToggle :: Maybe (Boolean -> msg)
  , disabled :: Boolean
  , showIcon :: Boolean
  , iconPosition :: IconPosition
  , lazyRender :: Boolean
  , className :: String
  }

-- | Default collapsible configuration
defaultConfig :: forall msg. CollapsibleConfig msg
defaultConfig =
  { isOpen: false
  , onToggle: Nothing
  , disabled: false
  , showIcon: true
  , iconPosition: IconRight
  , lazyRender: false
  , className: ""
  }

-- | Trigger configuration
type TriggerConfig =
  { className :: String
  }

-- | Default trigger configuration
defaultTriggerConfig :: TriggerConfig
defaultTriggerConfig =
  { className: ""
  }

-- | Content configuration
type ContentConfig =
  { className :: String
  }

-- | Default content configuration
defaultContentConfig :: ContentConfig
defaultContentConfig =
  { className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // config modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration modifier type
type ConfigMod cfg = cfg -> cfg

-- | Set open state
isOpen :: forall msg. Boolean -> ConfigMod (CollapsibleConfig msg)
isOpen o cfg = cfg { isOpen = o }

-- | Set toggle handler (receives new state)
onToggle :: forall msg. (Boolean -> msg) -> ConfigMod (CollapsibleConfig msg)
onToggle handler cfg = cfg { onToggle = Just handler }

-- | Set disabled state
disabled :: forall msg. Boolean -> ConfigMod (CollapsibleConfig msg)
disabled d cfg = cfg { disabled = d }

-- | Show expand/collapse icon
showIcon :: forall msg. Boolean -> ConfigMod (CollapsibleConfig msg)
showIcon s cfg = cfg { showIcon = s }

-- | Set icon position
iconPosition :: forall msg. IconPosition -> ConfigMod (CollapsibleConfig msg)
iconPosition p cfg = cfg { iconPosition = p }

-- | Enable lazy rendering of content (only renders when open)
lazyRender :: forall msg. Boolean -> ConfigMod (CollapsibleConfig msg)
lazyRender l cfg = cfg { lazyRender = l }

-- | Add custom class to container
className :: forall msg. String -> ConfigMod (CollapsibleConfig msg)
className c cfg = cfg { className = cfg.className <> " " <> c }

-- | Add custom class to trigger
triggerClassName :: String -> ConfigMod TriggerConfig
triggerClassName c cfg = cfg { className = cfg.className <> " " <> c }

-- | Add custom class to content
contentClassName :: String -> ConfigMod ContentConfig
contentClassName c cfg = cfg { className = cfg.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collapsible container
-- |
-- | Wraps trigger and content with expand/collapse behavior.
-- | State is controlled via props — parent manages open/closed state.
collapsible :: forall msg.
  Array (ConfigMod (CollapsibleConfig msg)) ->
  E.Element msg ->
  E.Element msg ->
  E.Element msg
collapsible configMods triggerEl contentEl =
  let
    cfg = foldl (\c f -> f c) defaultConfig configMods
    
    stateStr = if cfg.isOpen then "open" else "closed"
    
    containerClasses = buildContainerClasses cfg
    
    -- Wrap trigger with click handler if not disabled
    wrappedTrigger = wrapTriggerWithHandler cfg triggerEl
    
    -- Content may be lazy-rendered
    renderedContent = 
      if cfg.lazyRender && not cfg.isOpen
        then E.empty
        else contentEl
  in
    E.div_
      [ E.class_ containerClasses
      , E.attr "data-state" stateStr
      , E.attr "data-disabled" (if cfg.disabled then "true" else "false")
      ]
      [ wrappedTrigger
      , renderedContent
      ]

-- | Build container CSS classes
buildContainerClasses :: forall msg. CollapsibleConfig msg -> String
buildContainerClasses cfg =
  let
    base = "collapsible"
    stateClass = if cfg.isOpen then "collapsible-open" else "collapsible-closed"
    disabledClass = if cfg.disabled then "collapsible-disabled opacity-50" else ""
  in
    base <> " " <> stateClass <> " " <> disabledClass <> " " <> cfg.className

-- | Wrap trigger element with click handler
wrapTriggerWithHandler :: forall msg.
  CollapsibleConfig msg ->
  E.Element msg ->
  E.Element msg
wrapTriggerWithHandler cfg triggerEl =
  case cfg.onToggle of
    Nothing -> triggerEl
    Just handler ->
      if cfg.disabled
        then triggerEl
        else
          -- Wrap in a div that handles the click
          E.div_
            [ E.onClick (handler (not cfg.isOpen))
            , E.style "cursor" "pointer"
            ]
            [ triggerEl ]

-- | Trigger element
-- |
-- | Clickable element that toggles the collapsible.
-- | ARIA attributes are set based on parent state.
trigger :: forall msg.
  Array (ConfigMod TriggerConfig) ->
  Array (E.Element msg) ->
  E.Element msg
trigger configMods children =
  let
    cfg = foldl (\c f -> f c) defaultTriggerConfig configMods
    
    triggerClasses =
      "collapsible-trigger flex items-center justify-between w-full py-2 px-3 " <>
      "text-left font-medium transition-colors hover:bg-accent rounded-md " <>
      "cursor-pointer focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
  in
    E.button_
      [ E.class_ (triggerClasses <> " " <> cfg.className)
      , E.type_ "button"
      , E.attr "aria-expanded" "false"
      ]
      children

-- | Trigger with chevron icon
-- |
-- | Trigger element with chevron icon that rotates on expand.
triggerWithIcon :: forall msg.
  Array (ConfigMod TriggerConfig) ->
  String ->
  E.Element msg
triggerWithIcon configMods label =
  let
    cfg = foldl (\c f -> f c) defaultTriggerConfig configMods
    
    triggerClasses =
      "collapsible-trigger flex items-center justify-between w-full py-2 px-3 " <>
      "text-left font-medium transition-colors hover:bg-accent rounded-md " <>
      "cursor-pointer focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
  in
    E.button_
      [ E.class_ (triggerClasses <> " " <> cfg.className)
      , E.type_ "button"
      , E.attr "aria-expanded" "false"
      ]
      [ E.span_ [] [ E.text label ]
      , chevronIcon
      ]

-- | Content element
-- |
-- | Collapsible content that expands/collapses.
-- | Animation is handled via CSS transitions on height/opacity.
content :: forall msg.
  Array (ConfigMod ContentConfig) ->
  Array (E.Element msg) ->
  E.Element msg
content configMods children =
  let
    cfg = foldl (\c f -> f c) defaultContentConfig configMods
    
    contentClasses =
      "collapsible-content overflow-hidden transition-all " <>
      "data-[state=closed]:h-0 data-[state=closed]:opacity-0 " <>
      "data-[state=open]:opacity-100"
  in
    E.div_
      [ E.class_ (contentClasses <> " " <> cfg.className)
      , E.attr "data-state" "closed"
      , E.attr "aria-hidden" "true"
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
    [ polylineIcon ]

-- | Polyline for chevron shape
polylineIcon :: forall msg. E.Element msg
polylineIcon =
  E.svgElement "polyline"
    [ E.attr "points" "6 9 12 15 18 9" ]
    []
