-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // kanban
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban — Schema-native drag-and-drop Kanban board component.
-- |
-- | ## Design Philosophy
-- |
-- | This component is a **compound** of Schema atoms, composed from:
-- | - Color: header colors, priority indicators, labels
-- | - Dimension: column width, padding, gaps
-- | - Geometry: border radius
-- | - Reactive: drag state, selection state
-- | - Gestural: drag-drop operations
-- |
-- | ## Architecture
-- |
-- | Kanban is organized into submodules:
-- |
-- | | Module   | Purpose                                      |
-- | |----------|----------------------------------------------|
-- | | Types    | Identifiers, Priority, WIPLimit, Messages    |
-- | | Card     | Card data structure and operations           |
-- | | Column   | Column data structure and operations         |
-- | | State    | Board state management                       |
-- | | Render   | Pure Element rendering                       |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Kanban as Kanban
-- |
-- | -- Build initial state
-- | let state = Kanban.initialState
-- |              # Kanban.addColumn (Kanban.kanbanColumn (Kanban.columnId "todo") "To Do")
-- |              # Kanban.addColumn (Kanban.kanbanColumn (Kanban.columnId "doing") "In Progress")
-- |              # Kanban.addColumn (Kanban.kanbanColumn (Kanban.columnId "done") "Done")
-- |
-- | -- Render board
-- | Kanban.renderBoard
-- |   [ Kanban.backgroundColor brand.surfaceColor
-- |   , Kanban.borderColor brand.borderColor
-- |   , Kanban.borderRadius brand.containerRadius
-- |   ]
-- |   state
-- | ```

module Hydrogen.Element.Compound.Kanban
  ( -- * Re-exports: Types
    module Types
  
  -- * Re-exports: Card
  , module Card
  
  -- * Re-exports: Column
  , module Column
  
  -- * Re-exports: State
  , module State
  
  -- * Re-exports: Render
  , module Render
  ) where

import Hydrogen.Element.Compound.Kanban.Types
  ( BoardId
  , boardId
  , unwrapBoardId
  , ColumnId
  , columnId
  , unwrapColumnId
  , CardId
  , cardId
  , unwrapCardId
  , SwimlaneId
  , swimlaneId
  , unwrapSwimlaneId
  , Priority(PriorityLow, PriorityMedium, PriorityHigh, PriorityUrgent)
  , priorityToInt
  , priorityFromInt
  , priorityLabel
  , WIPLimit
  , wipLimit
  , unwrapWIPLimit
  , noWIPLimit
  , isOverWIPLimit
  , KanbanMsg
      ( MoveCard
      , MoveColumn
      , AddCard
      , RemoveCard
      , ExpandCard
      , CollapseCard
      , ToggleColumnCollapse
      , BeginDrag
      , UpdateDrag
      , EndDrag
      , CancelDrag
      , SelectCard
      , DeselectCard
      )
  , DropPosition(DropBefore, DropAfter, DropInto)
  ) as Types

import Hydrogen.Element.Compound.Kanban.Card
  ( KanbanCard
  , kanbanCard
  , emptyCard
  , cardIdOf
  , cardTitle
  , cardDescription
  , cardLabels
  , cardAssignee
  , cardDueDate
  , cardPriority
  , cardExpanded
  , cardColumnId
  , cardSwimlaneId
  , cardIndex
  , setCardTitle
  , setCardDescription
  , addCardLabel
  , removeCardLabel
  , setCardAssignee
  , clearCardAssignee
  , setCardDueDate
  , clearCardDueDate
  , setCardPriority
  , setCardExpanded
  , toggleCardExpanded
  , setCardColumn
  , setCardSwimlane
  , setCardIndex
  , CardLabel
  , cardLabel
  , labelText
  , labelColor
  , Assignee
  , assignee
  , assigneeName
  , assigneeAvatar
  , assigneeInitials
  , DueDate
  , dueDate
  , dueDateYear
  , dueDateMonth
  , dueDateDay
  , isDueDatePast
  , isDueDateToday
  , isDueDateSoon
  , formatDueDate
  ) as Card

import Hydrogen.Element.Compound.Kanban.Column
  ( KanbanColumn
  , kanbanColumn
  , emptyColumn
  , columnIdOf
  , columnTitle
  , columnColor
  , columnWIPLimit
  , columnCollapsed
  , columnIndex
  , columnCollapsible
  , setColumnTitle
  , setColumnColor
  , clearColumnColor
  , setColumnWIPLimit
  , removeColumnWIPLimit
  , setColumnCollapsed
  , toggleColumnCollapsed
  , setColumnIndex
  , setColumnCollapsible
  , isColumnOverWIP
  , columnCardCountLabel
  ) as Column

import Hydrogen.Element.Compound.Kanban.State
  ( KanbanState
  , initialState
  , emptyState
  , update
  , getColumns
  , getColumn
  , addColumn
  , removeColumn
  , updateColumn
  , moveColumn
  , columnCount
  , getCards
  , getCard
  , getCardsInColumn
  , addCard
  , removeCard
  , updateCard
  , moveCard
  , moveCardRelative
  , moveCardToColumn
  , cardCount
  , cardCountInColumn
  , Swimlane
  , swimlane
  , swimlaneName
  , swimlaneCollapsed
  , getSwimlanes
  , addSwimlane
  , removeSwimlane
  , toggleSwimlaneCollapsed
  , getCardsInSwimlane
  , getDragState
  , setDragState
  , clearDragState
  , isDragging
  , getDraggedCard
  , getSelectedCard
  , selectCard
  , clearSelection
  , isColumnCollapsedInState
  , setColumnCollapsedInState
  , toggleColumnCollapsedInState
  ) as State

import Hydrogen.Element.Compound.Kanban.Render
  ( renderBoard
  , renderColumn
  , renderCard
  , renderSwimlane
  , renderAddCardButton
  , renderDragPreview
  , KanbanConfig
  , defaultConfig
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
  ) as Render
