-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // treeview // content
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Content — Render node content using slots and templates.
-- |
-- | ## Design Philosophy
-- |
-- | Nodes can contain arbitrary content organized into slots:
-- | - Leading: Expand icon, checkbox
-- | - Icon: Node icon (file, folder, custom)
-- | - Main: Primary label
-- | - Subtitle: Secondary text
-- | - Trailing: Badges, counts
-- | - Actions: Hover actions
-- | - Below: Expandable details
-- |
-- | ## Content Templates
-- |
-- | Pre-built configurations for common patterns:
-- | - TextOnly: Simple label
-- | - IconText: File explorer style
-- | - TitleSubtitle: Two-line
-- | - Card: Rich content (org charts)
-- | - Avatar: Person nodes
-- | - Metric: Dashboard values
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Node (TreeNode data)
-- | - TreeView.State (expansion, selection)
-- | - Schema.Graph.NodeContent (slots, templates)
-- | - Hydrogen.Render.Element (Element)

module Hydrogen.Element.Compound.TreeView.Content
  ( -- * Content Rendering
    renderNodeContent
  , renderSlot
  
  -- * Slot Renderers
  , renderLeadingSlot
  , renderIconSlot
  , renderMainSlot
  , renderSubtitleSlot
  , renderTrailingSlot
  , renderActionsSlot
  , renderBelowSlot
  
  -- * Content Props
  , ContentProps
  , defaultContentProps
  , withTemplate
  , withSlotRenderer
  , withExpandIcon
  , withCheckbox
  
  -- * Custom Content
  , SlotRenderer
  , emptySlot
  , textSlot
  , iconSlot
  , badgeSlot
  , buttonSlot
  , customSlot
  
  -- * Template Builders
  , applyTemplate
  , textOnlyTemplate
  , iconTextTemplate
  , cardTemplate
  , avatarTemplate
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (==)
  , (&&)
  , map
  , not
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.TreeView.Types
  ( CheckState(Checked, Unchecked, Indeterminate)
  , iconToEmoji
  , iconToAria
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( TreeNode
  , nodeLabel
  , nodeIcon
  , nodeHasChildren
  )

import Hydrogen.Schema.Graph.NodeContent
  ( ContentSlot(SlotLeading, SlotIcon, SlotMain, SlotSubtitle, SlotTrailing, SlotActions, SlotBelow, SlotOverlay, SlotBackground)
  , ContentTemplate(TemplateTextOnly, TemplateIconText, TemplateTitleSubtitle, TemplateCard, TemplateAvatar, TemplateMetric, TemplateProgress, TemplateThumbnail, TemplateCustom)
  ) as Schema

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // content props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Custom slot renderer function type
type SlotRenderer msg = 
  { node :: TreeNode
  , expanded :: Boolean
  , selected :: Boolean
  , focused :: Boolean
  , checkState :: CheckState
  } -> E.Element msg

-- | Properties for content rendering
type ContentProps msg =
  { template :: Schema.ContentTemplate
  , showExpandIcon :: Boolean
  , showCheckbox :: Boolean
  , iconSize :: Number
  , labelClass :: String
  , customSlots :: Array { slot :: Schema.ContentSlot, renderer :: SlotRenderer msg }
  }

-- | Default content properties
defaultContentProps :: forall msg. ContentProps msg
defaultContentProps =
  { template: Schema.TemplateIconText
  , showExpandIcon: true
  , showCheckbox: false
  , iconSize: 16.0
  , labelClass: "tree-node-label"
  , customSlots: []
  }

-- | Set content template
withTemplate :: forall msg. Schema.ContentTemplate -> ContentProps msg -> ContentProps msg
withTemplate t p = p { template = t }

-- | Add a custom slot renderer
withSlotRenderer :: forall msg. Schema.ContentSlot -> SlotRenderer msg -> ContentProps msg -> ContentProps msg
withSlotRenderer slot renderer p = 
  p { customSlots = Array.snoc p.customSlots { slot, renderer } }

-- | Toggle expand icon visibility
withExpandIcon :: forall msg. Boolean -> ContentProps msg -> ContentProps msg
withExpandIcon b p = p { showExpandIcon = b }

-- | Toggle checkbox visibility
withCheckbox :: forall msg. Boolean -> ContentProps msg -> ContentProps msg
withCheckbox b p = p { showCheckbox = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // content rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render complete node content based on template
renderNodeContent ::
  forall msg.
  ContentProps msg ->
  TreeNode ->
  Boolean ->      -- expanded
  Boolean ->      -- selected
  Boolean ->      -- focused
  CheckState ->
  Boolean ->      -- hovering
  E.Element msg
renderNodeContent props node expanded selected focused checkState hovering =
  let
    context = 
      { node
      , expanded
      , selected
      , focused
      , checkState
      }
    
    -- Get slots to render based on template
    slots = templateSlots props.template
    
    -- Render each slot
    renderedSlots = map (renderSlotFromContext props context hovering) slots
  in
    E.div_
      [ E.class_ "tree-node-content"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      , E.style "flex" "1"
      , E.style "min-width" "0"  -- Allow text truncation
      ]
      renderedSlots

-- | Get slots for a template
templateSlots :: Schema.ContentTemplate -> Array Schema.ContentSlot
templateSlots Schema.TemplateTextOnly = 
  [ Schema.SlotLeading, Schema.SlotMain ]
templateSlots Schema.TemplateIconText = 
  [ Schema.SlotLeading, Schema.SlotIcon, Schema.SlotMain ]
templateSlots Schema.TemplateTitleSubtitle = 
  [ Schema.SlotLeading, Schema.SlotIcon, Schema.SlotMain, Schema.SlotSubtitle ]
templateSlots Schema.TemplateCard = 
  [ Schema.SlotLeading, Schema.SlotIcon, Schema.SlotMain, Schema.SlotSubtitle, Schema.SlotTrailing ]
templateSlots Schema.TemplateAvatar = 
  [ Schema.SlotLeading, Schema.SlotIcon, Schema.SlotMain, Schema.SlotSubtitle ]
templateSlots Schema.TemplateMetric = 
  [ Schema.SlotLeading, Schema.SlotMain, Schema.SlotTrailing ]
templateSlots Schema.TemplateProgress = 
  [ Schema.SlotLeading, Schema.SlotIcon, Schema.SlotMain, Schema.SlotTrailing ]
templateSlots Schema.TemplateThumbnail = 
  [ Schema.SlotLeading, Schema.SlotIcon, Schema.SlotMain ]
templateSlots Schema.TemplateCustom = 
  [ Schema.SlotLeading, Schema.SlotIcon, Schema.SlotMain, Schema.SlotTrailing, Schema.SlotActions ]

-- | Render a single slot from context
renderSlotFromContext ::
  forall msg.
  ContentProps msg ->
  { node :: TreeNode, expanded :: Boolean, selected :: Boolean, focused :: Boolean, checkState :: CheckState } ->
  Boolean ->  -- hovering
  Schema.ContentSlot ->
  E.Element msg
renderSlotFromContext props context hovering slot =
  -- Check for custom renderer first
  case findCustomRenderer slot props.customSlots of
    Just renderer -> renderer context
    Nothing -> renderSlot props context.node context.expanded context.selected context.checkState hovering slot

-- | Find a custom renderer for a slot
findCustomRenderer :: 
  forall msg.
  Schema.ContentSlot -> 
  Array { slot :: Schema.ContentSlot, renderer :: SlotRenderer msg } -> 
  Maybe (SlotRenderer msg)
findCustomRenderer targetSlot customs =
  case Array.find (\c -> c.slot == targetSlot) customs of
    Just found -> Just found.renderer
    Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // slot rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a specific slot
renderSlot ::
  forall msg.
  ContentProps msg ->
  TreeNode ->
  Boolean ->      -- expanded
  Boolean ->      -- selected
  CheckState ->
  Boolean ->      -- hovering
  Schema.ContentSlot ->
  E.Element msg
renderSlot props node expanded selected checkState hovering slot =
  case slot of
    Schema.SlotLeading -> renderLeadingSlot props node expanded checkState
    Schema.SlotIcon -> renderIconSlot props node expanded
    Schema.SlotMain -> renderMainSlot props node selected
    Schema.SlotSubtitle -> renderSubtitleSlot props node
    Schema.SlotTrailing -> renderTrailingSlot props node
    Schema.SlotActions -> renderActionsSlot props node hovering
    Schema.SlotBelow -> renderBelowSlot props node expanded
    Schema.SlotOverlay -> E.empty
    Schema.SlotBackground -> E.empty

-- | Render leading slot (expand icon, checkbox)
renderLeadingSlot ::
  forall msg.
  ContentProps msg ->
  TreeNode ->
  Boolean ->      -- expanded
  CheckState ->
  E.Element msg
renderLeadingSlot props node expanded checkState =
  let
    hasChildren = nodeHasChildren node
    
    expandIcon = if props.showExpandIcon && hasChildren
      then
        E.span_
          [ E.class_ "tree-expand-icon"
          , E.style "width" "16px"
          , E.style "height" "16px"
          , E.style "display" "inline-flex"
          , E.style "align-items" "center"
          , E.style "justify-content" "center"
          , E.style "transition" "transform 150ms"
          , E.style "transform" (if expanded then "rotate(90deg)" else "rotate(0deg)")
          , E.style "cursor" "pointer"
          , E.style "flex-shrink" "0"
          ]
          [ E.text "▶" ]
      else if props.showExpandIcon
        then
          -- Spacer for alignment
          E.span_
            [ E.style "width" "16px"
            , E.style "display" "inline-block"
            , E.style "flex-shrink" "0"
            ]
            []
        else
          E.empty
    
    checkbox = if props.showCheckbox
      then renderCheckbox checkState
      else E.empty
  in
    E.span_
      [ E.class_ "tree-leading-slot"
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      ]
      [ expandIcon, checkbox ]

-- | Render a checkbox
renderCheckbox :: forall msg. CheckState -> E.Element msg
renderCheckbox checkState =
  let
    icon = case checkState of
      Checked -> "☑"
      Unchecked -> "☐"
      Indeterminate -> "▣"
    
    ariaChecked = case checkState of
      Checked -> "true"
      Unchecked -> "false"
      Indeterminate -> "mixed"
  in
    E.span_
      [ E.class_ "tree-checkbox"
      , E.role "checkbox"
      , E.attr "aria-checked" ariaChecked
      , E.style "width" "16px"
      , E.style "height" "16px"
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "cursor" "pointer"
      ]
      [ E.text icon ]

-- | Render icon slot
renderIconSlot ::
  forall msg.
  ContentProps msg ->
  TreeNode ->
  Boolean ->      -- expanded
  E.Element msg
renderIconSlot props node _expanded =
  case nodeIcon node of
    Nothing -> E.empty
    Just icon ->
      E.span_
        [ E.class_ "tree-icon-slot"
        , E.attr "aria-label" (iconToAria icon)
        , E.style "display" "inline-flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , E.style "flex-shrink" "0"
        , E.style "font-size" (show props.iconSize <> "px")
        ]
        [ E.text (iconToEmoji icon) ]

-- | Render main content slot (label)
renderMainSlot ::
  forall msg.
  ContentProps msg ->
  TreeNode ->
  Boolean ->      -- selected
  E.Element msg
renderMainSlot props node selected =
  let
    fontWeight = if selected then "600" else "400"
  in
    E.span_
      [ E.class_ props.labelClass
      , E.style "flex" "1"
      , E.style "overflow" "hidden"
      , E.style "text-overflow" "ellipsis"
      , E.style "white-space" "nowrap"
      , E.style "font-weight" fontWeight
      ]
      [ E.text (nodeLabel node) ]

-- | Render subtitle slot
renderSubtitleSlot ::
  forall msg.
  ContentProps msg ->
  TreeNode ->
  E.Element msg
renderSubtitleSlot _props _node =
  -- Subtitle would come from node metadata/custom data
  -- For now, render empty (can be customized via slot renderer)
  E.empty

-- | Render trailing slot (badges, counts)
renderTrailingSlot ::
  forall msg.
  ContentProps msg ->
  TreeNode ->
  E.Element msg
renderTrailingSlot _props _node =
  -- Trailing content would come from node metadata
  -- For now, render empty (can be customized via slot renderer)
  E.empty

-- | Render actions slot (show on hover)
renderActionsSlot ::
  forall msg.
  ContentProps msg ->
  TreeNode ->
  Boolean ->      -- hovering
  E.Element msg
renderActionsSlot _props _node hovering =
  if not hovering
    then E.empty
    else
      E.span_
        [ E.class_ "tree-actions-slot"
        , E.style "display" "inline-flex"
        , E.style "gap" "4px"
        ]
        []  -- Actions would be added via custom slot renderer

-- | Render below slot (expandable details)
renderBelowSlot ::
  forall msg.
  ContentProps msg ->
  TreeNode ->
  Boolean ->      -- expanded
  E.Element msg
renderBelowSlot _props _node _expanded =
  -- Below content is custom content below the main row
  -- Would be shown when node is expanded
  E.empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // slot builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Empty slot (renders nothing)
emptySlot :: forall msg. SlotRenderer msg
emptySlot _ = E.empty

-- | Text slot
textSlot :: forall msg. String -> SlotRenderer msg
textSlot text _ = E.text text

-- | Icon slot (emoji or symbol)
iconSlot :: forall msg. String -> Number -> SlotRenderer msg
iconSlot icon size _ =
  E.span_
    [ E.style "font-size" (show size <> "px") ]
    [ E.text icon ]

-- | Badge slot (count or status)
badgeSlot :: forall msg. String -> String -> SlotRenderer msg
badgeSlot text bgColor _ =
  E.span_
    [ E.class_ "tree-badge"
    , E.style "display" "inline-flex"
    , E.style "align-items" "center"
    , E.style "justify-content" "center"
    , E.style "padding" "2px 6px"
    , E.style "font-size" "11px"
    , E.style "font-weight" "500"
    , E.style "border-radius" "9999px"
    , E.style "background-color" bgColor
    , E.style "color" "white"
    ]
    [ E.text text ]

-- | Button slot
buttonSlot :: forall msg. String -> msg -> SlotRenderer msg
buttonSlot label onClick _ =
  E.element "button"
    [ E.class_ "tree-action-button"
    , E.onClick onClick
    , E.style "padding" "2px 8px"
    , E.style "font-size" "12px"
    , E.style "border" "1px solid #e5e7eb"
    , E.style "border-radius" "4px"
    , E.style "background" "white"
    , E.style "cursor" "pointer"
    ]
    [ E.text label ]

-- | Custom element slot
customSlot :: forall msg. E.Element msg -> SlotRenderer msg
customSlot element _ = element

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // template builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a template to props
applyTemplate :: forall msg. Schema.ContentTemplate -> ContentProps msg -> ContentProps msg
applyTemplate = withTemplate

-- | Configure for text-only display
textOnlyTemplate :: forall msg. ContentProps msg -> ContentProps msg
textOnlyTemplate = withTemplate Schema.TemplateTextOnly

-- | Configure for icon + text (file explorer)
iconTextTemplate :: forall msg. ContentProps msg -> ContentProps msg
iconTextTemplate = withTemplate Schema.TemplateIconText

-- | Configure for rich card content
cardTemplate :: forall msg. ContentProps msg -> ContentProps msg
cardTemplate = withTemplate Schema.TemplateCard

-- | Configure for avatar + name
avatarTemplate :: forall msg. ContentProps msg -> ContentProps msg
avatarTemplate = withTemplate Schema.TemplateAvatar
