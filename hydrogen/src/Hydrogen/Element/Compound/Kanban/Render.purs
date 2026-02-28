-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // kanban // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Render — Pure Element rendering for Kanban boards.
-- |
-- | ## Design Philosophy
-- |
-- | This module provides pure render functions that produce Element values.
-- | All styling uses Schema atoms — no CSS strings, no Tailwind classes.
-- |
-- | ## Schema Atoms Used
-- |
-- | | Property         | Pillar    | Type                | Purpose            |
-- | |------------------|-----------|---------------------|-------------------|
-- | | backgroundColor  | Color     | Color.RGB           | Board/card bg      |
-- | | borderColor      | Color     | Color.RGB           | Card borders       |
-- | | headerColor      | Color     | Color.RGB           | Column headers     |
-- | | textColor        | Color     | Color.RGB           | Text color         |
-- | | priorityColor    | Color     | Color.RGB           | Priority indicator |
-- | | borderRadius     | Geometry  | Geometry.Radius     | Corner rounding    |
-- | | padding          | Dimension | Device.Pixel        | Internal padding   |
-- | | gap              | Dimension | Device.Pixel        | Spacing            |
-- | | columnWidth      | Dimension | Device.Pixel        | Column width       |
-- | | elevation        | Elevation | BoxShadow           | Card shadows       |

module Hydrogen.Element.Compound.Kanban.Render
  ( -- * Render Functions
    renderBoard
  , renderColumn
  , renderCard
  , renderSwimlane
  , renderAddCardButton
  , renderDragPreview
  
  -- * Config
  , KanbanConfig
  , defaultConfig
  
  -- * Config Props
  , KanbanProp
  , backgroundColor
  , borderColor
  , cardBackgroundColor
  , headerColor
  , textColor
  , mutedTextColor
  , selectedColor
  , hoverColor
  , borderRadius
  , cardRadius
  , padding
  , cardPadding
  , gap
  , columnWidth
  , columnMinHeight
  , priorityLowColor
  , priorityMediumColor
  , priorityHighColor
  , priorityUrgentColor
  , onCardClick
  , onCardExpand
  , onColumnCollapse
  , onAddCard
  ) where

import Prelude
  ( const
  , map
  , not
  , show
  , ($)
  , (&&)
  , (<>)
  , (==)
  , (/=)
  )

import Data.Array (foldl, null)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device

import Hydrogen.Element.Compound.Kanban.Types
  ( CardId
  , ColumnId
  , KanbanMsg
      ( MoveCard
      , AddCard
      , RemoveCard
      , ExpandCard
      , CollapseCard
      , ToggleColumnCollapse
      , BeginDrag
      , EndDrag
      , CancelDrag
      , SelectCard
      , DeselectCard
      )
  , Priority(PriorityLow, PriorityMedium, PriorityHigh, PriorityUrgent)
  , unwrapCardId
  , unwrapColumnId
  )
import Hydrogen.Element.Compound.Kanban.Card
  ( KanbanCard
  , CardLabel
  , Assignee
  , cardIdOf
  , cardTitle
  , cardDescription
  , cardLabels
  , cardAssignee
  , cardDueDate
  , cardPriority
  , cardExpanded
  , labelText
  , labelColor
  , assigneeName
  , assigneeAvatar
  , assigneeInitials
  , formatDueDate
  )
import Hydrogen.Element.Compound.Kanban.Column
  ( KanbanColumn
  , columnIdOf
  , columnTitle
  , columnColor
  , columnCollapsed
  , columnCollapsible
  , columnCardCountLabel
  , isColumnOverWIP
  )
import Hydrogen.Element.Compound.Kanban.State
  ( KanbanState
  , Swimlane
  , swimlaneName
  , swimlaneCollapsed
  , getColumns
  , getCardsInColumn
  , cardCountInColumn
  , getDraggedCard
  , getSelectedCard
  , isDragging
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kanban board configuration (all Schema atoms)
type KanbanConfig =
  { backgroundColor :: Color.RGB
  , borderColor :: Color.RGB
  , cardBackgroundColor :: Color.RGB
  , headerColor :: Color.RGB
  , textColor :: Color.RGB
  , mutedTextColor :: Color.RGB
  , selectedColor :: Color.RGB
  , hoverColor :: Color.RGB
  , borderRadius :: Geometry.Radius
  , cardRadius :: Geometry.Radius
  , padding :: Device.Pixel
  , cardPadding :: Device.Pixel
  , gap :: Device.Pixel
  , columnWidth :: Device.Pixel
  , columnMinHeight :: Device.Pixel
  , priorityLowColor :: Color.RGB
  , priorityMediumColor :: Color.RGB
  , priorityHighColor :: Color.RGB
  , priorityUrgentColor :: Color.RGB
  , onCardClick :: Maybe (CardId -> KanbanMsg)
  , onCardExpand :: Maybe (CardId -> Boolean -> KanbanMsg)
  , onColumnCollapse :: Maybe (ColumnId -> KanbanMsg)
  , onAddCard :: Maybe (ColumnId -> KanbanMsg)
  }

-- | Config property modifier
type KanbanProp = KanbanConfig -> KanbanConfig

-- | Default configuration
defaultConfig :: KanbanConfig
defaultConfig =
  { backgroundColor: Color.rgb 248 250 252        -- slate-50
  , borderColor: Color.rgb 226 232 240            -- slate-200
  , cardBackgroundColor: Color.rgb 255 255 255    -- white
  , headerColor: Color.rgb 241 245 249            -- slate-100
  , textColor: Color.rgb 15 23 42                 -- slate-900
  , mutedTextColor: Color.rgb 100 116 139         -- slate-500
  , selectedColor: Color.rgb 219 234 254          -- blue-100
  , hoverColor: Color.rgb 241 245 249             -- slate-100
  , borderRadius: Geometry.px 8.0                 -- 8px
  , cardRadius: Geometry.px 8.0                   -- 8px
  , padding: Device.px 16.0                       -- 16px
  , cardPadding: Device.px 12.0                   -- 12px
  , gap: Device.px 16.0                           -- 16px
  , columnWidth: Device.px 288.0                  -- 288px (18rem)
  , columnMinHeight: Device.px 200.0              -- 200px
  , priorityLowColor: Color.rgb 34 197 94         -- green-500
  , priorityMediumColor: Color.rgb 234 179 8      -- yellow-500
  , priorityHighColor: Color.rgb 249 115 22       -- orange-500
  , priorityUrgentColor: Color.rgb 239 68 68      -- red-500
  , onCardClick: Nothing
  , onCardExpand: Nothing
  , onColumnCollapse: Nothing
  , onAddCard: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // config setters
-- ═════════════════════════════════════════════════════════════════════════════

backgroundColor :: Color.RGB -> KanbanProp
backgroundColor c cfg = cfg { backgroundColor = c }

borderColor :: Color.RGB -> KanbanProp
borderColor c cfg = cfg { borderColor = c }

cardBackgroundColor :: Color.RGB -> KanbanProp
cardBackgroundColor c cfg = cfg { cardBackgroundColor = c }

headerColor :: Color.RGB -> KanbanProp
headerColor c cfg = cfg { headerColor = c }

textColor :: Color.RGB -> KanbanProp
textColor c cfg = cfg { textColor = c }

mutedTextColor :: Color.RGB -> KanbanProp
mutedTextColor c cfg = cfg { mutedTextColor = c }

selectedColor :: Color.RGB -> KanbanProp
selectedColor c cfg = cfg { selectedColor = c }

hoverColor :: Color.RGB -> KanbanProp
hoverColor c cfg = cfg { hoverColor = c }

borderRadius :: Geometry.Radius -> KanbanProp
borderRadius r cfg = cfg { borderRadius = r }

cardRadius :: Geometry.Radius -> KanbanProp
cardRadius r cfg = cfg { cardRadius = r }

padding :: Device.Pixel -> KanbanProp
padding p cfg = cfg { padding = p }

cardPadding :: Device.Pixel -> KanbanProp
cardPadding p cfg = cfg { cardPadding = p }

gap :: Device.Pixel -> KanbanProp
gap g cfg = cfg { gap = g }

columnWidth :: Device.Pixel -> KanbanProp
columnWidth w cfg = cfg { columnWidth = w }

columnMinHeight :: Device.Pixel -> KanbanProp
columnMinHeight h cfg = cfg { columnMinHeight = h }

priorityLowColor :: Color.RGB -> KanbanProp
priorityLowColor c cfg = cfg { priorityLowColor = c }

priorityMediumColor :: Color.RGB -> KanbanProp
priorityMediumColor c cfg = cfg { priorityMediumColor = c }

priorityHighColor :: Color.RGB -> KanbanProp
priorityHighColor c cfg = cfg { priorityHighColor = c }

priorityUrgentColor :: Color.RGB -> KanbanProp
priorityUrgentColor c cfg = cfg { priorityUrgentColor = c }

onCardClick :: (CardId -> KanbanMsg) -> KanbanProp
onCardClick f cfg = cfg { onCardClick = Just f }

onCardExpand :: (CardId -> Boolean -> KanbanMsg) -> KanbanProp
onCardExpand f cfg = cfg { onCardExpand = Just f }

onColumnCollapse :: (ColumnId -> KanbanMsg) -> KanbanProp
onColumnCollapse f cfg = cfg { onColumnCollapse = Just f }

onAddCard :: (ColumnId -> KanbanMsg) -> KanbanProp
onAddCard f cfg = cfg { onAddCard = Just f }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // render functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render complete Kanban board
renderBoard :: Array KanbanProp -> KanbanState -> E.Element KanbanMsg
renderBoard props state =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
    columns = getColumns state
  in
    E.div_
      ([ E.role "region"
       , E.ariaLabel "Kanban board"
       ] <> E.styles
          [ Tuple "display" "flex"
          , Tuple "gap" $ show cfg.gap
          , Tuple "padding" $ show cfg.padding
          , Tuple "overflow-x" "auto"
          , Tuple "min-height" "500px"
          , Tuple "background-color" $ Color.toHex cfg.backgroundColor
          ])
      (map (renderColumn props state) columns)

-- | Render a single column
renderColumn :: Array KanbanProp -> KanbanState -> KanbanColumn -> E.Element KanbanMsg
renderColumn props state col =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
    colId = columnIdOf col
    cards = getCardsInColumn colId state
    cardCnt = cardCountInColumn colId state
    isCollapsed = columnCollapsed col
    isOverWIP = isColumnOverWIP cardCnt col
    
    headerBgColor = case columnColor col of
      Just c -> c
      Nothing -> cfg.headerColor
  in
    E.div_
      ([ E.role "listbox"
       , E.ariaLabel (columnTitle col)
       , E.attr "data-column-id" (unwrapColumnId colId)
       ] <> E.styles
          [ Tuple "display" "flex"
          , Tuple "flex-direction" "column"
          , Tuple "flex-shrink" "0"
          , Tuple "width" (if isCollapsed then "48px" else show cfg.columnWidth)
          , Tuple "background-color" (Color.toHex cfg.backgroundColor)
          , Tuple "border-radius" (Geometry.toLegacyCss cfg.borderRadius)
          , Tuple "border" ("1px solid " <> Color.toHex cfg.borderColor)
          ])
      [ -- Header
        renderColumnHeader cfg col cardCnt isOverWIP headerBgColor
      , -- Cards (if not collapsed)
        if isCollapsed
          then E.empty
          else renderColumnContent cfg props state col cards
      ]

-- | Render column header
renderColumnHeader :: KanbanConfig -> KanbanColumn -> Int -> Boolean -> Color.RGB -> E.Element KanbanMsg
renderColumnHeader cfg col cardCnt isOverWIP headerBgColor =
  let
    colId = columnIdOf col
    isCollapsed = columnCollapsed col
    countLabel = columnCardCountLabel cardCnt col
    
    countBadgeColor = if isOverWIP
      then Color.rgb 239 68 68  -- red-500
      else cfg.mutedTextColor
  in
    E.div_
      (E.styles
          [ Tuple "display" "flex"
          , Tuple "align-items" "center"
          , Tuple "justify-content" "space-between"
          , Tuple "padding" (show cfg.cardPadding)
          , Tuple "background-color" (Color.toHex headerBgColor)
          , Tuple "border-radius" (Geometry.toLegacyCss cfg.borderRadius <> " " <> Geometry.toLegacyCss cfg.borderRadius <> " 0 0")
          ])
      [ if isCollapsed
          then 
            -- Vertical text when collapsed
            E.span_
              (E.styles
                  [ Tuple "writing-mode" "vertical-lr"
                  , Tuple "transform" "rotate(180deg)"
                  , Tuple "font-weight" "600"
                  , Tuple "font-size" "14px"
                  , Tuple "color" (Color.toHex cfg.textColor)
                  ])
              [ E.text (columnTitle col) ]
          else
            E.div_
              (E.styles
                  [ Tuple "display" "flex"
                  , Tuple "align-items" "center"
                  , Tuple "gap" "8px"
                  , Tuple "flex" "1"
                  ])
              [ E.h3_
                  (E.styles
                      [ Tuple "font-weight" "600"
                      , Tuple "font-size" "14px"
                      , Tuple "color" (Color.toHex cfg.textColor)
                      , Tuple "margin" "0"
                      ])
                  [ E.text (columnTitle col) ]
              , E.span_
                  (E.styles
                      [ Tuple "font-size" "12px"
                      , Tuple "padding" "2px 8px"
                      , Tuple "border-radius" "9999px"
                      , Tuple "background-color" (Color.toHex countBadgeColor)
                      , Tuple "color" "white"
                      ])
                  [ E.text countLabel ]
              ]
      , -- Collapse/Expand button
        if columnCollapsible col
          then
            let
              -- Use custom callback or default to ToggleColumnCollapse
              toggleMsg = case cfg.onColumnCollapse of
                Just f -> f colId
                Nothing -> ToggleColumnCollapse colId
              
              -- Arrow direction and label depend on collapsed state
              arrowIcon = if isCollapsed then ">" else "<"
              ariaLabelText = if isCollapsed then "Expand column" else "Collapse column"
            in
              E.button_
                ([ E.type_ "button"
                 , E.ariaLabel ariaLabelText
                 , E.onClick toggleMsg
                 ] <> E.styles
                    [ Tuple "padding" "4px"
                    , Tuple "border" "none"
                    , Tuple "background" "transparent"
                    , Tuple "cursor" "pointer"
                    , Tuple "border-radius" "4px"
                    , Tuple "margin-top" (if isCollapsed then "8px" else "0")
                    ])
                [ E.text arrowIcon ]
          else E.empty
      ]

-- | Render column content (cards area)
-- |
-- | The props, state, and col parameters are used for:
-- | - props: allows future extension for dynamic prop handling
-- | - state: provides access to selection/drag state for card highlighting and drop handling
-- | - col: provides column context for accessibility, data attributes, and drop target
-- |
-- | Drop behavior:
-- | - onDragOver: allows dropping (prevents default)
-- | - onDrop: moves dragged card to this column at the end
-- | - onClick: deselects any selected card (clicking empty area)
renderColumnContent :: KanbanConfig -> Array KanbanProp -> KanbanState -> KanbanColumn -> Array KanbanCard -> E.Element KanbanMsg
renderColumnContent cfg _props state col cards =
  let
    colId = columnIdOf col
    colTitle = columnTitle col
    cardCnt = cardCountInColumn colId state
    
    -- When a card is dropped here, move it to this column at the end
    -- The runtime will read the dragged card from state
    dropHandler = case getDraggedCard state of
      Nothing -> EndDrag  -- No card being dragged, just end
      Just draggedCardId -> MoveCard draggedCardId colId cardCnt
    
    -- Visual feedback: highlight when dragging over
    dropTargetStyle = if isDragging state
      then [ Tuple "outline" ("2px dashed " <> Color.toHex cfg.selectedColor) ]
      else []
  in
    E.div_
      ([ E.role "group"
       , E.ariaLabel ("Cards in " <> colTitle)
       , E.attr "data-content-for" (unwrapColumnId colId)
       -- Click handler: clicking empty area deselects
       , E.onClick DeselectCard
       -- Drop target handlers
       , E.onDragOver EndDrag  -- Allow drop (EndDrag is a no-op message for dragover)
       , E.onDrop dropHandler
       ] <> E.styles
          ([ Tuple "flex" "1"
           , Tuple "padding" (show cfg.cardPadding)
           , Tuple "display" "flex"
           , Tuple "flex-direction" "column"
           , Tuple "gap" "8px"
           , Tuple "overflow-y" "auto"
           , Tuple "min-height" (show cfg.columnMinHeight)
           ] <> dropTargetStyle))
      (map (renderCardWithSelection cfg state) cards <> [renderAddCardButtonWithConfig cfg colId])

-- | Render a card with selection state awareness
-- |
-- | Applies visual feedback for:
-- | - Selected cards (highlighted border)
-- | - Cards being dragged (reduced opacity)
renderCardWithSelection :: KanbanConfig -> KanbanState -> KanbanCard -> E.Element KanbanMsg
renderCardWithSelection cfg state card =
  let
    cId = cardIdOf card
    isSelected = getSelectedCard state == Just cId
    isBeingDragged = getDraggedCard state == Just cId
    
    -- Build selection/drag styles
    selectionStyles = 
      if isBeingDragged
        then [ Tuple "opacity" "0.5" ]
        else if isSelected
          then [ Tuple "border-color" (Color.toHex cfg.selectedColor)
               , Tuple "box-shadow" ("0 0 0 2px " <> Color.toHex cfg.selectedColor)
               ]
          else []
  in
    renderCardWithStyles cfg card selectionStyles

-- | Render a single card (without selection state)
-- |
-- | Event handlers:
-- | - onClick: SelectCard (single click selects)
-- | - onDoubleClick: ExpandCard/CollapseCard (toggle details)
-- | - onDragStart: BeginDrag (start drag operation)
-- | - onDragEnd: EndDrag (complete drag operation)
-- | - onKeyDown: CancelDrag on Escape, DeselectCard on Escape when not dragging
renderCard :: KanbanConfig -> KanbanCard -> E.Element KanbanMsg
renderCard cfg card = renderCardWithStyles cfg card []

-- | Render a card with additional styles for selection/drag feedback
-- |
-- | This is the core card renderer that accepts extra styles for:
-- | - Selection highlighting (border, box-shadow)
-- | - Drag feedback (opacity)
renderCardWithStyles :: KanbanConfig -> KanbanCard -> Array (Tuple String String) -> E.Element KanbanMsg
renderCardWithStyles cfg card extraStyles =
  let
    cId = cardIdOf card
    priority = cardPriority card
    priorityColor = priorityToColor cfg priority
    labels = cardLabels card
    hasLabels = not (null labels)
    isExpanded = cardExpanded card
    desc = cardDescription card
    hasDesc = desc /= ""
    
    -- Click message: use custom callback or default to SelectCard
    clickMsg = case cfg.onCardClick of
      Just f -> f cId
      Nothing -> SelectCard cId
    
    -- Expand/collapse message: use custom callback or default messages
    -- onCardExpand receives the card ID and the NEW expanded state
    toggleExpandMsg = case cfg.onCardExpand of
      Just f -> f cId (not isExpanded)  -- Pass the new state (toggled)
      Nothing -> if isExpanded then CollapseCard cId else ExpandCard cId
    
    -- Keyboard handler: Escape cancels drag, Enter expands, other keys ignored
    -- Using const to create a handler that returns the same message regardless
    -- of key for unrecognized keys (re-selecting the current card is a no-op)
    handleKeyDown key = 
      if key == "Escape" then CancelDrag 
      else if key == "Enter" then toggleExpandMsg
      else const clickMsg key  -- Ignore other keys, keep selection
    
    -- Base card styles
    -- Note: hoverColor is included as a data attribute for the runtime.
    -- The runtime reads this value and applies it during hover state.
    -- This keeps rendering pure — we describe WHAT the hover color IS,
    -- not HOW to apply it (that's the runtime's job).
    baseStyles = 
      [ Tuple "position" "relative"
      , Tuple "padding" (show cfg.cardPadding)
      , Tuple "background-color" (Color.toHex cfg.cardBackgroundColor)
      , Tuple "border-radius" (Geometry.toLegacyCss cfg.cardRadius)
      , Tuple "border" ("1px solid " <> Color.toHex cfg.borderColor)
      , Tuple "cursor" "grab"
      , Tuple "box-shadow" "0 1px 3px rgba(0,0,0,0.1)"
      -- Hover color as data for runtime state management
      , Tuple "--hydrogen-hover-bg" (Color.toHex cfg.hoverColor)
      ]
  in
    E.div_
      ([ E.role "option"
       , E.attr "data-card-id" (unwrapCardId cId)
       , E.attr "draggable" "true"
       , E.attr "tabindex" "0"  -- Make focusable for keyboard events
       -- Click handlers: use config callbacks if provided
       , E.onClick clickMsg
       , E.onDoubleClick toggleExpandMsg
       -- Drag handlers
       , E.onDragStart (BeginDrag cId)
       , E.onDragEnd EndDrag
       -- Keyboard handler
       , E.onKeyDown handleKeyDown
       ] <> E.styles (baseStyles <> extraStyles))
      [ -- Priority indicator
        renderPriorityIndicator cfg.cardRadius priorityColor
      , -- Labels
        if hasLabels then renderCardLabels labels else E.empty
      , -- Title
        E.h4_
          (E.styles
              [ Tuple "font-size" "14px"
              , Tuple "font-weight" "500"
              , Tuple "color" (Color.toHex cfg.textColor)
              , Tuple "margin" "0"
              ])
          [ E.text (cardTitle card) ]
      , -- Description (if expanded)
        if isExpanded && hasDesc
          then
            E.p_
              (E.styles
                  [ Tuple "font-size" "12px"
                  , Tuple "color" (Color.toHex cfg.mutedTextColor)
                  , Tuple "margin" "8px 0 0 0"
                  ])
              [ E.text desc ]
          else E.empty
      , -- Footer (due date, assignee)
        renderCardFooter cfg card
      , -- Actions (delete button, shown when expanded)
        if isExpanded
          then renderCardActions cfg cId
          else E.empty
      ]

-- | Render priority indicator bar
renderPriorityIndicator :: Geometry.Radius -> Color.RGB -> E.Element KanbanMsg
renderPriorityIndicator radius color =
  E.div_
    (E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" "0"
        , Tuple "top" "0"
        , Tuple "bottom" "0"
        , Tuple "width" "4px"
        , Tuple "background-color" (Color.toHex color)
        , Tuple "border-radius" (Geometry.toLegacyCss radius <> " 0 0 " <> Geometry.toLegacyCss radius)
        ])
    []

-- | Get priority color from config
priorityToColor :: KanbanConfig -> Priority -> Color.RGB
priorityToColor cfg PriorityLow = cfg.priorityLowColor
priorityToColor cfg PriorityMedium = cfg.priorityMediumColor
priorityToColor cfg PriorityHigh = cfg.priorityHighColor
priorityToColor cfg PriorityUrgent = cfg.priorityUrgentColor

-- | Render card labels
renderCardLabels :: Array CardLabel -> E.Element KanbanMsg
renderCardLabels labels =
  E.div_
    (E.styles
        [ Tuple "display" "flex"
        , Tuple "flex-wrap" "wrap"
        , Tuple "gap" "4px"
        , Tuple "margin-bottom" "8px"
        ])
    (map renderLabel labels)
  where
    renderLabel :: CardLabel -> E.Element KanbanMsg
    renderLabel lbl =
      E.span_
        (E.styles
            [ Tuple "font-size" "12px"
            , Tuple "padding" "2px 8px"
            , Tuple "border-radius" "9999px"
            , Tuple "background-color" (Color.toHex (labelColor lbl))
            , Tuple "color" "white"
            ])
        [ E.text (labelText lbl) ]

-- | Render card footer (due date, assignee)
renderCardFooter :: KanbanConfig -> KanbanCard -> E.Element KanbanMsg
renderCardFooter cfg card =
  let
    mDueDate = cardDueDate card
    mAssignee = cardAssignee card
    hasDueDate = case mDueDate of
      Just _ -> true
      Nothing -> false
    hasAssignee = case mAssignee of
      Just _ -> true
      Nothing -> false
  in
    if not hasDueDate && not hasAssignee
      then E.empty
      else
        E.div_
          (E.styles
              [ Tuple "display" "flex"
              , Tuple "align-items" "center"
              , Tuple "justify-content" "space-between"
              , Tuple "margin-top" "8px"
              ])
          [ -- Due date
            case mDueDate of
              Just dd ->
                E.div_
                  (E.styles
                      [ Tuple "display" "flex"
                      , Tuple "align-items" "center"
                      , Tuple "gap" "4px"
                      , Tuple "font-size" "12px"
                      , Tuple "color" (Color.toHex cfg.mutedTextColor)
                      ])
                  [ E.text (formatDueDate dd) ]
              Nothing -> E.empty
          , -- Assignee avatar (image if available, initials fallback)
            case mAssignee of
              Just a -> renderAssigneeAvatar cfg a
              Nothing -> E.empty
          ]

-- | Render assignee avatar
-- |
-- | Uses avatar image URL if available, otherwise shows initials.
-- | This implements the full Assignee type: name, avatar, initials.
renderAssigneeAvatar :: KanbanConfig -> Assignee -> E.Element KanbanMsg
renderAssigneeAvatar cfg a =
  case assigneeAvatar a of
    Just avatarUrl ->
      -- Render image avatar
      E.img_
        ([ E.src avatarUrl
         , E.alt (assigneeName a)
         , E.title (assigneeName a)
         ] <> E.styles
            [ Tuple "width" "24px"
            , Tuple "height" "24px"
            , Tuple "border-radius" "9999px"
            , Tuple "object-fit" "cover"
            ])
    Nothing ->
      -- Render initials fallback
      E.div_
        ([ E.title (assigneeName a) ] <> E.styles
            [ Tuple "width" "24px"
            , Tuple "height" "24px"
            , Tuple "border-radius" "9999px"
            , Tuple "background-color" (Color.toHex cfg.selectedColor)
            , Tuple "color" (Color.toHex cfg.textColor)
            , Tuple "display" "flex"
            , Tuple "align-items" "center"
            , Tuple "justify-content" "center"
            , Tuple "font-size" "12px"
            , Tuple "font-weight" "500"
            ])
        [ E.text (assigneeInitials a) ]

-- | Render card actions (delete button)
-- |
-- | Actions are shown when the card is expanded. The delete button
-- | emits a RemoveCard message to remove the card from the board.
renderCardActions :: KanbanConfig -> CardId -> E.Element KanbanMsg
renderCardActions cfg cId =
  E.div_
    (E.styles
        [ Tuple "display" "flex"
        , Tuple "justify-content" "flex-end"
        , Tuple "margin-top" "8px"
        , Tuple "padding-top" "8px"
        , Tuple "border-top" ("1px solid " <> Color.toHex cfg.borderColor)
        ])
    [ E.button_
        ([ E.type_ "button"
         , E.ariaLabel "Delete card"
         , E.onClick (RemoveCard cId)
         ] <> E.styles
            [ Tuple "padding" "4px 8px"
            , Tuple "font-size" "12px"
            , Tuple "color" (Color.toHex cfg.priorityUrgentColor)
            , Tuple "background" "transparent"
            , Tuple "border" ("1px solid " <> Color.toHex cfg.priorityUrgentColor)
            , Tuple "border-radius" "4px"
            , Tuple "cursor" "pointer"
            ])
        [ E.text "Delete" ]
    ]

-- | Render swimlane
renderSwimlane :: Array KanbanProp -> Swimlane -> Array (E.Element KanbanMsg) -> E.Element KanbanMsg
renderSwimlane props sl children =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
    isCollapsed = swimlaneCollapsed sl
  in
    E.div_
      (E.styles
          [ Tuple "border-bottom" ("1px solid " <> Color.toHex cfg.borderColor)
          , Tuple "padding-bottom" (show cfg.padding)
          , Tuple "margin-bottom" (show cfg.padding)
          ])
      [ -- Swimlane header
        E.div_
          (E.styles
              [ Tuple "display" "flex"
              , Tuple "align-items" "center"
              , Tuple "gap" "8px"
              , Tuple "padding" "8px 0"
              , Tuple "margin-bottom" "8px"
              ])
          [ E.div_
              (E.styles
                  [ Tuple "width" "4px"
                  , Tuple "height" "16px"
                  , Tuple "border-radius" "2px"
                  , Tuple "background-color" (Color.toHex cfg.selectedColor)
                  ])
              []
          , E.h3_
              (E.styles
                  [ Tuple "font-weight" "600"
                  , Tuple "font-size" "14px"
                  , Tuple "color" (Color.toHex cfg.textColor)
                  , Tuple "margin" "0"
                  ])
              [ E.text (swimlaneName sl) ]
          ]
      , -- Content
        if isCollapsed
          then E.empty
          else
            E.div_
              (E.styles
                  [ Tuple "display" "flex"
                  , Tuple "gap" (show cfg.gap)
                  ])
              children
      ]

-- | Render add card button (props-based API)
-- |
-- | Uses config callback if provided, otherwise emits AddCard message
renderAddCardButton :: Array KanbanProp -> ColumnId -> E.Element KanbanMsg
renderAddCardButton props colId =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
  in
    renderAddCardButtonWithConfig cfg colId

-- | Render add card button (config-based API)
-- |
-- | Internal version that takes config directly for use within render functions.
-- | Uses config callback if provided, otherwise emits AddCard message.
renderAddCardButtonWithConfig :: KanbanConfig -> ColumnId -> E.Element KanbanMsg
renderAddCardButtonWithConfig cfg colId =
  let
    -- Use custom callback or default to AddCard
    addMsg = case cfg.onAddCard of
      Just f -> f colId
      Nothing -> AddCard colId
  in
    E.button_
      ([ E.type_ "button"
       , E.onClick addMsg
       ] <> E.styles
          [ Tuple "width" "100%"
          , Tuple "padding" "8px"
          , Tuple "text-align" "left"
          , Tuple "font-size" "14px"
          , Tuple "color" (Color.toHex cfg.mutedTextColor)
          , Tuple "background" "transparent"
          , Tuple "border" "none"
          , Tuple "cursor" "pointer"
          , Tuple "border-radius" (Geometry.toLegacyCss cfg.cardRadius)
          , Tuple "display" "flex"
          , Tuple "align-items" "center"
          , Tuple "gap" "8px"
          -- Hover color as data for runtime state management
          , Tuple "--hydrogen-hover-bg" (Color.toHex cfg.hoverColor)
          ])
      [ E.text "+ Add card" ]

-- | Render drag preview
renderDragPreview :: Array KanbanProp -> KanbanCard -> Number -> Number -> E.Element KanbanMsg
renderDragPreview props card x y =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
  in
    E.div_
      (E.styles
          [ Tuple "position" "fixed"
          , Tuple "left" (show x <> "px")
          , Tuple "top" (show y <> "px")
          , Tuple "width" (show cfg.columnWidth)
          , Tuple "opacity" "0.8"
          , Tuple "pointer-events" "none"
          , Tuple "z-index" "1000"
          , Tuple "transform" "rotate(3deg)"
          ])
      [ renderCard cfg card ]
