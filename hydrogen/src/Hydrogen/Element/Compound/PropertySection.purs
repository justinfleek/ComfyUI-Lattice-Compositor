-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // property-section
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PropertySection — Collapsible labeled section for property panels.
-- |
-- | A PropertySection aggregates related controls into a named, collapsible
-- | group. This is the building block for settings panels, inspector UIs,
-- | and property editors.
-- |
-- | ## Design Philosophy
-- |
-- | At billion-agent scale, property panels must be:
-- | - **Scannable**: Clear labels, visual hierarchy
-- | - **Collapsible**: Hide complexity when not needed
-- | - **Composable**: Sections can contain any Element children
-- | - **Accessible**: Keyboard navigation, ARIA labels
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.PropertySection as Section
-- | import Hydrogen.Element.Compound.Slider as Slider
-- | import Hydrogen.Element.Compound.NumberInput as NumberInput
-- | 
-- | -- Transform section with multiple controls
-- | Section.section
-- |   [ Section.label "Transform"
-- |   , Section.isOpen state.transformOpen
-- |   , Section.onToggle ToggleTransform
-- |   ]
-- |   [ Section.row "X" [ NumberInput.numberInput [...] ]
-- |   , Section.row "Y" [ NumberInput.numberInput [...] ]
-- |   , Section.row "Rotation" [ Slider.slider [...] ]
-- |   ]
-- |
-- | -- Collapsed section
-- | Section.section
-- |   [ Section.label "Advanced"
-- |   , Section.isOpen false
-- |   ]
-- |   [ ... ]
-- | ```
module Hydrogen.Element.Compound.PropertySection
  ( -- * Components
    section
  , row
  , labeledRow
  , divider
  
  -- * Props
  , SectionProps
  , SectionProp
  , RowProps
  , RowProp
  , defaultProps
  , defaultRowProps
  
  -- * Prop Builders
  , label
  , isOpen
  , onToggle
  , sectionDisabled
  , icon
  , className
  , rowLabel
  , rowClassName
  , rowTooltip
  , compact
  ) where

import Prelude
  ( (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Section properties
type SectionProps msg =
  { label :: String
  , isOpen :: Boolean
  , onToggle :: Maybe (Boolean -> msg)
  , disabled :: Boolean
  , icon :: Maybe (E.Element msg)
  , className :: String
  }

-- | Section property modifier
type SectionProp msg = SectionProps msg -> SectionProps msg

-- | Default section properties
defaultProps :: forall msg. SectionProps msg
defaultProps =
  { label: "Properties"
  , isOpen: true
  , onToggle: Nothing
  , disabled: false
  , icon: Nothing
  , className: ""
  }

-- | Row properties
type RowProps msg =
  { label :: Maybe String
  , className :: String
  , tooltip :: Maybe String
  , compact :: Boolean
  }

-- | Row property modifier
type RowProp msg = RowProps msg -> RowProps msg

-- | Default row properties
defaultRowProps :: forall msg. RowProps msg
defaultRowProps =
  { label: Nothing
  , className: ""
  , tooltip: Nothing
  , compact: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set section label
label :: forall msg. String -> SectionProp msg
label l props = props { label = l }

-- | Set open state
isOpen :: forall msg. Boolean -> SectionProp msg
isOpen o props = props { isOpen = o }

-- | Set toggle handler
onToggle :: forall msg. (Boolean -> msg) -> SectionProp msg
onToggle handler props = props { onToggle = Just handler }

-- | Set disabled state
sectionDisabled :: forall msg. Boolean -> SectionProp msg
sectionDisabled d props = props { disabled = d }

-- | Set section icon
icon :: forall msg. E.Element msg -> SectionProp msg
icon i props = props { icon = Just i }

-- | Add custom class to section
className :: forall msg. String -> SectionProp msg
className c props = props { className = props.className <> " " <> c }

-- | Set row label
rowLabel :: forall msg. String -> RowProp msg
rowLabel l props = props { label = Just l }

-- | Add custom class to row
rowClassName :: forall msg. String -> RowProp msg
rowClassName c props = props { className = props.className <> " " <> c }

-- | Set row tooltip
rowTooltip :: forall msg. String -> RowProp msg
rowTooltip t props = props { tooltip = Just t }

-- | Enable compact mode
compact :: forall msg. RowProp msg
compact props = props { compact = true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property section
-- |
-- | A collapsible container with a labeled header for grouping related
-- | property controls. Use with `row` for individual property entries.
-- |
-- | Pure Element — can be rendered to any target.
section :: forall msg. Array (SectionProp msg) -> Array (E.Element msg) -> E.Element msg
section propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    openClass = if props.isOpen then "property-section-open" else "property-section-closed"
    disabledClass = if props.disabled then "opacity-50 pointer-events-none" else ""
    
    -- Header with toggle
    headerEl = E.div_
      [ E.classes 
          [ "property-section-header"
          , "flex items-center justify-between"
          , "px-3 py-2"
          , "bg-muted/50"
          , "border-b border-border"
          , "cursor-pointer select-none"
          , "hover:bg-muted/70 transition-colors"
          ]
      , E.dataAttr "section-header" "true"
      ]
      [ E.div_
          [ E.class_ "flex items-center gap-2" ]
          [ chevronIcon props.isOpen
          , case props.icon of
              Just ic -> ic
              Nothing -> E.empty
          , E.span_
              [ E.classes 
                  [ "text-sm font-medium text-foreground"
                  ]
              ]
              [ E.text props.label ]
          ]
      ]
    
    -- Content container
    contentEl = E.div_
      [ E.classes 
          [ "property-section-content"
          , "px-3 py-2"
          , "space-y-2"
          , if props.isOpen then "block" else "hidden"
          ]
      , E.dataAttr "section-content" "true"
      , E.dataAttr "state" (if props.isOpen then "open" else "closed")
      ]
      children
  in
    E.div_
      [ E.classes 
          [ "property-section"
          , "border border-border rounded-md"
          , "bg-background"
          , openClass
          , disabledClass
          , props.className
          ]
      , E.dataAttr "disabled" (if props.disabled then "true" else "false")
      ]
      [ headerEl
      , contentEl
      ]

-- | Property row
-- |
-- | A row for a single property control. Use inside a `section`.
-- | For labeled rows, use `labeledRow` instead.
-- |
-- | Pure Element — can be rendered to any target.
row :: forall msg. Array (RowProp msg) -> Array (E.Element msg) -> E.Element msg
row propMods children =
  let
    props = foldl (\p f -> f p) defaultRowProps propMods
    
    heightClass = if props.compact then "min-h-6" else "min-h-8"
    
    tooltipAttrs = case props.tooltip of
      Just t -> [ E.attr "title" t ]
      Nothing -> []
  in
    E.div_
      ( [ E.classes 
            [ "property-row"
            , "flex items-center"
            , heightClass
            , props.className
            ]
        ] <> tooltipAttrs
      )
      children

-- | Labeled property row
-- |
-- | A row with a label on the left and controls on the right.
-- | Standard layout: 40% label, 60% control.
-- |
-- | ```purescript
-- | labeledRow "X Position" [ NumberInput.numberInput [...] ]
-- | ```
-- |
-- | Pure Element — can be rendered to any target.
labeledRow :: forall msg. String -> Array (E.Element msg) -> E.Element msg
labeledRow labelText controls =
  E.div_
    [ E.classes 
        [ "property-labeled-row"
        , "flex items-center gap-2"
        , "min-h-8"
        ]
    ]
    [ E.label_
        [ E.classes 
            [ "text-xs text-muted-foreground"
            , "w-24 shrink-0"
            , "truncate"
            ]
        ]
        [ E.text labelText ]
    , E.div_
        [ E.classes 
            [ "flex-1"
            , "flex items-center gap-1"
            ]
        ]
        controls
    ]

-- | Section divider
-- |
-- | A horizontal line to visually separate groups within a section.
-- |
-- | Pure Element — can be rendered to any target.
divider :: forall msg. E.Element msg
divider =
  E.hr_
    [ E.classes 
        [ "property-divider"
        , "border-t border-border"
        , "my-2"
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chevron icon that rotates based on open state
chevronIcon :: forall msg. Boolean -> E.Element msg
chevronIcon isExpanded =
  let
    rotateClass = if isExpanded then "rotate-90" else "rotate-0"
  in
    E.svg_
      [ E.attr "xmlns" "http://www.w3.org/2000/svg"
      , E.attr "width" "14"
      , E.attr "height" "14"
      , E.attr "viewBox" "0 0 24 24"
      , E.attr "fill" "none"
      , E.attr "stroke" "currentColor"
      , E.attr "stroke-width" "2"
      , E.attr "stroke-linecap" "round"
      , E.attr "stroke-linejoin" "round"
      , E.classes 
          [ "transition-transform duration-150"
          , rotateClass
          , "text-muted-foreground"
          ]
      ]
      [ E.polyline_ [ E.attr "points" "9 18 15 12 9 6" ] ]
