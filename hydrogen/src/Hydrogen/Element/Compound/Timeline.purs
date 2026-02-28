-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // element // timeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Timeline Component
-- |
-- | A flexible timeline component for displaying chronological events,
-- | milestones, and progress indicators.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Timeline as Timeline
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic vertical timeline
-- | Timeline.timeline
-- |   [ Timeline.orientation Timeline.Vertical ]
-- |   [ Timeline.timelineItem
-- |       [ Timeline.title "Project Started"
-- |       , Timeline.date "Jan 2024"
-- |       , Timeline.itemState Timeline.Completed
-- |       ]
-- |       [ E.text "Initial project kickoff" ]
-- |   , Timeline.timelineItem
-- |       [ Timeline.title "Development Phase"
-- |       , Timeline.date "Feb 2024"
-- |       , Timeline.itemState Timeline.Active
-- |       ]
-- |       [ E.text "Building core features" ]
-- |   ]
-- |
-- | -- Horizontal timeline
-- | Timeline.timeline
-- |   [ Timeline.orientation Timeline.Horizontal ]
-- |   items
-- | ```
module Hydrogen.Element.Compound.Timeline
  ( -- * Timeline Components
    timeline
  , timelineItem
  , timelineConnector
  , timelineDot
  , timelineContent
    -- * Props
  , TimelineProps
  , TimelineProp
  , ItemProps
  , ItemProp
  , defaultProps
  , defaultItemProps
    -- * Prop Builders - Timeline
  , orientation
  , alternating
  , className
    -- * Prop Builders - Item
  , title
  , description
  , date
  , icon
  , itemState
  , collapsible
  , expanded
  , onToggle
  , itemClassName
    -- * Types
  , Orientation(Vertical, Horizontal)
  , ItemState(Pending, Active, Completed)
  ) where

import Prelude
  ( class Eq
  , (<>)
  , (==)
  , (&&)
  , not
  , (/=)
  )

import Data.Array (foldl, null)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timeline orientation
data Orientation
  = Vertical
  | Horizontal

derive instance eqOrientation :: Eq Orientation

-- | Timeline item state
data ItemState
  = Pending
  | Active
  | Completed

derive instance eqItemState :: Eq ItemState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timeline container properties
type TimelineProps =
  { orientation :: Orientation
  , alternating :: Boolean
  , className :: String
  }

-- | Timeline property modifier
type TimelineProp = TimelineProps -> TimelineProps

-- | Default timeline properties
defaultProps :: TimelineProps
defaultProps =
  { orientation: Vertical
  , alternating: false
  , className: ""
  }

-- | Timeline item properties
type ItemProps msg =
  { title :: String
  , description :: String
  , date :: String
  , icon :: Maybe String
  , state :: ItemState
  , collapsible :: Boolean
  , expanded :: Boolean
  , className :: String
  , onToggle :: Maybe (Boolean -> msg)
  }

-- | Item property modifier
type ItemProp msg = ItemProps msg -> ItemProps msg

-- | Default item properties
defaultItemProps :: forall msg. ItemProps msg
defaultItemProps =
  { title: ""
  , description: ""
  , date: ""
  , icon: Nothing
  , state: Pending
  , collapsible: false
  , expanded: true
  , className: ""
  , onToggle: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set timeline orientation
orientation :: Orientation -> TimelineProp
orientation o props = props { orientation = o }

-- | Enable alternating sides (vertical only)
alternating :: Boolean -> TimelineProp
alternating a props = props { alternating = a }

-- | Add custom class to timeline container
className :: String -> TimelineProp
className c props = props { className = props.className <> " " <> c }

-- | Set item title
title :: forall msg. String -> ItemProp msg
title t props = props { title = t }

-- | Set item description
description :: forall msg. String -> ItemProp msg
description d props = props { description = d }

-- | Set item date
date :: forall msg. String -> ItemProp msg
date d props = props { date = d }

-- | Set item icon (icon name or emoji)
icon :: forall msg. String -> ItemProp msg
icon i props = props { icon = Just i }

-- | Set item state
itemState :: forall msg. ItemState -> ItemProp msg
itemState s props = props { state = s }

-- | Make item collapsible
collapsible :: forall msg. Boolean -> ItemProp msg
collapsible c props = props { collapsible = c }

-- | Set expanded state (for collapsible items)
expanded :: forall msg. Boolean -> ItemProp msg
expanded e props = props { expanded = e }

-- | Set toggle handler for collapsible items
onToggle :: forall msg. (Boolean -> msg) -> ItemProp msg
onToggle handler props = props { onToggle = Just handler }

-- | Add custom class to item
itemClassName :: forall msg. String -> ItemProp msg
itemClassName c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timeline container
-- |
-- | Wraps timeline items with proper layout and orientation.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
timeline :: forall msg. Array TimelineProp -> Array (E.Element msg) -> E.Element msg
timeline propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isHorizontal = props.orientation == Horizontal
    
    containerClasses = case props.orientation of
      Horizontal -> "flex items-start gap-0 overflow-x-auto"
      Vertical -> 
        if props.alternating
          then "relative"
          else "relative flex flex-col"
  in
    E.div_
      [ E.classes [ containerClasses, props.className ]
      , E.dataAttr "orientation" (if isHorizontal then "horizontal" else "vertical")
      , E.dataAttr "alternating" (if props.alternating then "true" else "false")
      , E.role "list"
      ]
      children

-- | Timeline item
-- |
-- | Individual timeline entry with dot, connector, and content.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
timelineItem :: forall msg. Array (ItemProp msg) -> Array (E.Element msg) -> E.Element msg
timelineItem propMods content =
  let
    props = foldl (\p f -> f p) defaultItemProps propMods
    
    stateClasses = case props.state of
      Completed -> "timeline-item-completed"
      Active -> "timeline-item-active"
      Pending -> "timeline-item-pending"
    
    containerClasses = 
      "relative flex gap-4 pb-8 last:pb-0"
  in
    E.div_
      [ E.classes [ containerClasses, stateClasses, props.className ]
      , E.role "listitem"
      ]
      [ E.div_
          [ E.class_ "flex flex-col items-center" ]
          [ timelineDot props
          , timelineConnector props
          ]
      , timelineContent props content
      ]

-- | Timeline dot/marker
-- |
-- | The visual indicator for a timeline item.
timelineDot :: forall msg. ItemProps msg -> E.Element msg
timelineDot props =
  let
    baseClasses = 
      "relative z-10 flex h-10 w-10 shrink-0 items-center justify-center rounded-full border-2"
    
    stateClasses = case props.state of
      Completed -> "border-primary bg-primary text-primary-foreground"
      Active -> "border-primary bg-background text-primary ring-4 ring-primary/20"
      Pending -> "border-muted-foreground/30 bg-muted text-muted-foreground"
    
    iconContent = case props.icon of
      Just i -> E.text i
      Nothing -> case props.state of
        Completed -> E.text "✓"
        Active -> E.span_ [ E.class_ "h-3 w-3 rounded-full bg-primary animate-pulse" ] []
        Pending -> E.text "○"
  in
    E.div_
      [ E.classes [ baseClasses, stateClasses ]
      , E.ariaHidden true
      ]
      [ iconContent ]

-- | Timeline connector line
-- |
-- | The connecting line between timeline items.
timelineConnector :: forall msg. ItemProps msg -> E.Element msg
timelineConnector props =
  let
    baseClasses = "flex-1 w-0.5 min-h-8"
    
    stateClasses = case props.state of
      Completed -> "bg-primary"
      Active -> "bg-gradient-to-b from-primary to-muted-foreground/30"
      Pending -> "bg-muted-foreground/30"
  in
    E.div_
      [ E.classes [ baseClasses, stateClasses ]
      , E.ariaHidden true
      ]
      []

-- | Timeline content area
-- |
-- | The content section of a timeline item.
timelineContent :: forall msg. ItemProps msg -> Array (E.Element msg) -> E.Element msg
timelineContent props children =
  let
    baseClasses = "flex-1 pt-1.5 pb-2"
    
    titleClasses = case props.state of
      Completed -> "font-semibold text-foreground"
      Active -> "font-semibold text-primary"
      Pending -> "font-medium text-muted-foreground"
    
    contentClasses = 
      if props.collapsible && not props.expanded
        then "hidden"
        else "mt-2"
    
    toggleHandler = case props.onToggle of
      Just handler -> [ E.onClick (handler (not props.expanded)) ]
      Nothing -> []
    
    collapsibleAttrs = 
      if props.collapsible
        then 
          [ E.classes [ "cursor-pointer hover:bg-muted/50 -mx-2 px-2 rounded transition-colors" ]
          , E.attr "aria-expanded" (if props.expanded then "true" else "false")
          ] <> toggleHandler
        else []
  in
    E.div_
      [ E.class_ baseClasses ]
      [ E.div_
          ( [ E.class_ "flex items-start justify-between gap-2 mb-1" ] <> collapsibleAttrs )
          [ E.div_
              []
              [ E.h3_ [ E.class_ titleClasses ] [ E.text props.title ]
              , if props.description /= ""
                  then E.p_ [ E.class_ "text-sm text-muted-foreground" ] [ E.text props.description ]
                  else E.text ""
              ]
          , E.span_ [ E.class_ "text-xs text-muted-foreground whitespace-nowrap" ] [ E.text props.date ]
          ]
      , if not (null children)
          then 
            E.div_
              [ E.class_ contentClasses ]
              children
          else E.text ""
      ]
