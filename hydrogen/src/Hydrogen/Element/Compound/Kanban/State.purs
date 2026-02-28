-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // kanban // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban State — Runtime state management for the Kanban board.
-- |
-- | ## Dependencies
-- | - Kanban.Types (CardId, ColumnId, SwimlaneId)
-- | - Kanban.Card (KanbanCard)
-- | - Kanban.Column (KanbanColumn)
-- | - Hydrogen.Schema.Gestural.DragDrop (DragState)
-- |
-- | ## State Structure
-- |
-- | The board state contains:
-- | - All columns
-- | - All cards
-- | - Optional swimlanes
-- | - Drag state
-- | - Selected card
-- | - Collapsed columns

module Hydrogen.Element.Compound.Kanban.State
  ( -- * Board State
    KanbanState
  , initialState
  , emptyState
  
  -- * Message Handler
  , update
  
  -- * Column Operations
  , getColumns
  , getColumn
  , addColumn
  , removeColumn
  , updateColumn
  , moveColumn
  , columnCount
  
  -- * Card Operations
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
  
  -- * Swimlane Operations
  , Swimlane
  , swimlane
  , swimlaneName
  , swimlaneCollapsed
  , getSwimlanes
  , addSwimlane
  , removeSwimlane
  , toggleSwimlaneCollapsed
  , getCardsInSwimlane
  
  -- * Drag State
  , getDragState
  , setDragState
  , clearDragState
  , isDragging
  , getDraggedCard
  
  -- * Selection
  , getSelectedCard
  , selectCard
  , clearSelection
  
  -- * Collapsed Columns
  , isColumnCollapsedInState
  , setColumnCollapsedInState
  , toggleColumnCollapsedInState
  ) where

import Prelude
  ( map
  , not
  , (#)
  , (+)
  , (<>)
  , (==)
  , (/=)
  , (>=)
  )

import Data.Array (filter, findIndex, length, snoc, sortBy)
import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Ord (comparing)
import Data.Set (Set)
import Data.Set as Set

import Hydrogen.Element.Compound.Kanban.Types
  ( CardId
  , ColumnId
  , SwimlaneId
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
  , cardId
  , unwrapCardId
  )
import Hydrogen.Element.Compound.Kanban.Card
  ( KanbanCard
  , cardIdOf
  , cardColumnId
  , cardSwimlaneId
  , cardIndex
  , setCardColumn
  , setCardIndex
  , setCardExpanded
  )
import Hydrogen.Element.Compound.Kanban.Column
  ( KanbanColumn
  , columnIdOf
  , columnIndex
  , setColumnIndex
  )
import Hydrogen.Schema.Gestural.DragDrop as DragDrop
import Hydrogen.Schema.Gestural.Pointer (pointerPosition)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // swimlane
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swimlane for horizontal grouping
type Swimlane =
  { id :: SwimlaneId
  , name :: String
  , collapsed :: Boolean
  }

-- | Create a swimlane
swimlane :: SwimlaneId -> String -> Swimlane
swimlane id name = { id, name, collapsed: false }

-- | Get swimlane name
swimlaneName :: Swimlane -> String
swimlaneName s = s.name

-- | Get swimlane collapsed state
swimlaneCollapsed :: Swimlane -> Boolean
swimlaneCollapsed s = s.collapsed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // kanban state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Kanban board state
type KanbanState =
  { columns :: Array KanbanColumn
  , cards :: Array KanbanCard
  , swimlanes :: Array Swimlane
  , dragState :: DragDrop.DragState
  , selectedCard :: Maybe CardId
  , collapsedColumns :: Set ColumnId
  }

-- | Initial empty state
initialState :: KanbanState
initialState =
  { columns: []
  , cards: []
  , swimlanes: []
  , dragState: DragDrop.initialDragState
  , selectedCard: Nothing
  , collapsedColumns: Set.empty
  }

-- | Alias for initial state
emptyState :: KanbanState
emptyState = initialState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // column operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all columns (sorted by index)
getColumns :: KanbanState -> Array KanbanColumn
getColumns state = sortBy (comparing columnIndex) state.columns

-- | Get column by ID
getColumn :: ColumnId -> KanbanState -> Maybe KanbanColumn
getColumn colId state =
  Array.find (\c -> columnIdOf c == colId) state.columns

-- | Add column to board
addColumn :: KanbanColumn -> KanbanState -> KanbanState
addColumn col state =
  let newCol = setColumnIndex (length state.columns) col
  in state { columns = snoc state.columns newCol }

-- | Remove column by ID
removeColumn :: ColumnId -> KanbanState -> KanbanState
removeColumn colId state =
  state { columns = filter (\c -> columnIdOf c /= colId) state.columns }

-- | Update column by ID
updateColumn :: ColumnId -> (KanbanColumn -> KanbanColumn) -> KanbanState -> KanbanState
updateColumn colId f state =
  state { columns = map (\c -> if columnIdOf c == colId then f c else c) state.columns }

-- | Move column to new index
moveColumn :: ColumnId -> Int -> KanbanState -> KanbanState
moveColumn colId newIndex state =
  let
    cols = filter (\c -> columnIdOf c /= colId) state.columns
    mCol = getColumn colId state
  in case mCol of
    Nothing -> state
    Just col ->
      let
        reindexed = Array.mapWithIndex (\i c -> setColumnIndex i c) cols
        inserted = insertAt newIndex (setColumnIndex newIndex col) reindexed
      in state { columns = inserted }
  where
    insertAt :: Int -> KanbanColumn -> Array KanbanColumn -> Array KanbanColumn
    insertAt idx item arr =
      let 
        before = Array.take idx arr
        after = Array.drop idx arr
      in before <> [item] <> after

-- | Get column count
columnCount :: KanbanState -> Int
columnCount state = length state.columns

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // card operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all cards
getCards :: KanbanState -> Array KanbanCard
getCards state = state.cards

-- | Get card by ID
getCard :: CardId -> KanbanState -> Maybe KanbanCard
getCard cId state =
  Array.find (\c -> cardIdOf c == cId) state.cards

-- | Get cards in a column (sorted by index)
getCardsInColumn :: ColumnId -> KanbanState -> Array KanbanCard
getCardsInColumn colId state =
  sortBy (comparing cardIndex)
    (filter (\c -> cardColumnId c == colId) state.cards)

-- | Add card to board
addCard :: KanbanCard -> KanbanState -> KanbanState
addCard card state =
  let
    cardsInCol = getCardsInColumn (cardColumnId card) state
    newCard = setCardIndex (length cardsInCol) card
  in state { cards = snoc state.cards newCard }

-- | Remove card by ID
removeCard :: CardId -> KanbanState -> KanbanState
removeCard cId state =
  state { cards = filter (\c -> cardIdOf c /= cId) state.cards }

-- | Update card by ID
updateCard :: CardId -> (KanbanCard -> KanbanCard) -> KanbanState -> KanbanState
updateCard cId f state =
  state { cards = map (\c -> if cardIdOf c == cId then f c else c) state.cards }

-- | Move card to column at index
moveCard :: CardId -> ColumnId -> Int -> KanbanState -> KanbanState
moveCard cId colId newIndex state =
  let
    mCard = getCard cId state
  in case mCard of
    Nothing -> state
    Just card ->
      let
        updatedCard = card # setCardColumn colId # setCardIndex newIndex
        -- Remove from old position
        otherCards = filter (\c -> cardIdOf c /= cId) state.cards
        -- Reindex cards in target column
        targetCards = filter (\c -> cardColumnId c == colId) otherCards
        reindexed = reindexCardsAfter newIndex targetCards
        -- Combine
        nonTargetCards = filter (\c -> cardColumnId c /= colId) otherCards
      in state { cards = nonTargetCards <> reindexed <> [updatedCard] }
  where
    reindexCardsAfter :: Int -> Array KanbanCard -> Array KanbanCard
    reindexCardsAfter idx cards =
      map (\c -> if cardIndex c >= idx then setCardIndex (cardIndex c + 1) c else c) cards

-- | Move card relative to a target card using DropPosition
-- |
-- | This enables fine-grained drop positioning:
-- | - DropBefore: Insert before the target card
-- | - DropAfter: Insert after the target card
-- | - DropInto: Insert at the end of the target's column (target is the column itself)
-- |
-- | Uses `findIndex` to locate the target card in its column's card array.
moveCardRelative :: CardId -> CardId -> DropPosition -> KanbanState -> KanbanState
moveCardRelative draggedId targetId position state =
  case getCard targetId state of
    Nothing -> state  -- Target card not found
    Just targetCard ->
      let
        targetColId = cardColumnId targetCard
        cardsInCol = getCardsInColumn targetColId state
        -- Find target's position in the sorted column cards
        mTargetIdx = findIndex (\c -> cardIdOf c == targetId) cardsInCol
      in case mTargetIdx of
        Nothing -> state  -- Target not in column (shouldn't happen)
        Just targetIdx ->
          let
            -- Compute insertion index based on drop position
            insertIdx = case position of
              DropBefore -> targetIdx
              DropAfter -> targetIdx + 1
              DropInto -> length cardsInCol  -- End of column
          in
            moveCard draggedId targetColId insertIdx state

-- | Move card to end of column (convenience for DropInto with column target)
moveCardToColumn :: CardId -> ColumnId -> KanbanState -> KanbanState
moveCardToColumn cId colId state =
  let
    insertIdx = cardCountInColumn colId state
  in
    moveCard cId colId insertIdx state

-- | Get total card count
cardCount :: KanbanState -> Int
cardCount state = length state.cards

-- | Get card count in column
cardCountInColumn :: ColumnId -> KanbanState -> Int
cardCountInColumn colId state =
  length (getCardsInColumn colId state)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // swimlane operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all swimlanes
getSwimlanes :: KanbanState -> Array Swimlane
getSwimlanes state = state.swimlanes

-- | Add swimlane
addSwimlane :: Swimlane -> KanbanState -> KanbanState
addSwimlane sl state = state { swimlanes = snoc state.swimlanes sl }

-- | Remove swimlane by ID
removeSwimlane :: SwimlaneId -> KanbanState -> KanbanState
removeSwimlane slId state =
  state { swimlanes = filter (\s -> s.id /= slId) state.swimlanes }

-- | Toggle swimlane collapsed state
toggleSwimlaneCollapsed :: SwimlaneId -> KanbanState -> KanbanState
toggleSwimlaneCollapsed slId state =
  state { swimlanes = map toggle state.swimlanes }
  where
    toggle :: Swimlane -> Swimlane
    toggle s = if s.id == slId then s { collapsed = not s.collapsed } else s

-- | Get cards in swimlane
getCardsInSwimlane :: SwimlaneId -> KanbanState -> Array KanbanCard
getCardsInSwimlane slId state =
  filter (\c -> cardSwimlaneId c == Just slId) state.cards

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // drag state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get drag state
getDragState :: KanbanState -> DragDrop.DragState
getDragState state = state.dragState

-- | Set drag state
setDragState :: DragDrop.DragState -> KanbanState -> KanbanState
setDragState ds state = state { dragState = ds }

-- | Clear drag state
clearDragState :: KanbanState -> KanbanState
clearDragState state = state { dragState = DragDrop.initialDragState }

-- | Check if dragging
isDragging :: KanbanState -> Boolean
isDragging state = DragDrop.isDragActive (DragDrop.currentPhase state.dragState)

-- | Get dragged card ID from drag source
getDraggedCard :: KanbanState -> Maybe CardId
getDraggedCard state = case state.dragState.source of
  Nothing -> Nothing
  Just src -> Just (cardIdFromSourceId (DragDrop.sourceId src))
  where
    -- Source ID is the card ID string
    cardIdFromSourceId :: String -> CardId
    cardIdFromSourceId s = cardId s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // selection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get selected card
getSelectedCard :: KanbanState -> Maybe CardId
getSelectedCard state = state.selectedCard

-- | Select a card
selectCard :: CardId -> KanbanState -> KanbanState
selectCard cId state = state { selectedCard = Just cId }

-- | Clear selection
clearSelection :: KanbanState -> KanbanState
clearSelection state = state { selectedCard = Nothing }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // collapsed columns
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if column is collapsed in state
isColumnCollapsedInState :: ColumnId -> KanbanState -> Boolean
isColumnCollapsedInState colId state = Set.member colId state.collapsedColumns

-- | Set column collapsed in state
setColumnCollapsedInState :: ColumnId -> Boolean -> KanbanState -> KanbanState
setColumnCollapsedInState colId collapsed state =
  if collapsed
    then state { collapsedColumns = Set.insert colId state.collapsedColumns }
    else state { collapsedColumns = Set.delete colId state.collapsedColumns }

-- | Toggle column collapsed in state
toggleColumnCollapsedInState :: ColumnId -> KanbanState -> KanbanState
toggleColumnCollapsedInState colId state =
  if Set.member colId state.collapsedColumns
    then state { collapsedColumns = Set.delete colId state.collapsedColumns }
    else state { collapsedColumns = Set.insert colId state.collapsedColumns }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // message handler
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle a Kanban message and produce a new state
-- |
-- | This is the core state transition function. All messages from the UI
-- | should be routed through this function to update the board state.
-- |
-- | ## Message Handling
-- |
-- | | Message | Effect |
-- | |---------|--------|
-- | | MoveCard | Move card to column at index |
-- | | MoveColumn | Reorder columns |
-- | | AddCard | No-op (requires external card creation) |
-- | | RemoveCard | Remove card from board |
-- | | ExpandCard | Set card expanded to true |
-- | | CollapseCard | Set card expanded to false |
-- | | ToggleColumnCollapse | Toggle column collapsed state |
-- | | BeginDrag | Start drag with card as source |
-- | | UpdateDrag | Update drag position (pure state, no effect here) |
-- | | EndDrag | Clear drag state |
-- | | CancelDrag | Clear drag state |
-- | | SelectCard | Set selected card |
-- | | DeselectCard | Clear selection |
update :: KanbanMsg -> KanbanState -> KanbanState
update msg state = case msg of
  -- Card movement
  MoveCard cId colId idx -> moveCard cId colId idx state
  
  -- Column reordering
  MoveColumn colId idx -> moveColumn colId idx state
  
  -- Card creation (no-op - requires external card data)
  -- The caller should create the card and use addCard directly
  AddCard _ -> state
  
  -- Card removal
  RemoveCard cId -> removeCard cId state
  
  -- Card expansion
  ExpandCard cId -> updateCard cId (setCardExpanded true) state
  CollapseCard cId -> updateCard cId (setCardExpanded false) state
  
  -- Column collapse
  ToggleColumnCollapse colId -> toggleColumnCollapsedInState colId state
  
  -- Drag operations
  BeginDrag cId -> beginDragCard cId state
  UpdateDrag _ _ -> state  -- Position is tracked by runtime, not state
  EndDrag -> clearDragState state
  CancelDrag -> clearDragState state
  
  -- Selection
  SelectCard cId -> selectCard cId state
  DeselectCard -> clearSelection state

-- | Begin dragging a card
-- |
-- | Sets up drag state with the card as the source.
-- | The actual visual drag position is managed by the runtime.
beginDragCard :: CardId -> KanbanState -> KanbanState
beginDragCard cId state =
  let
    -- Create drag source with card ID, type "card", empty transfer data, move effect
    source = DragDrop.dragSource 
      (unwrapCardId cId) 
      "card" 
      DragDrop.emptyTransfer 
      [DragDrop.DropMove]
    -- Initial position at origin - runtime will update with actual pointer position
    initialPos = pointerPosition 0.0 0.0
    noOffset = DragDrop.dragOffset 0.0 0.0
    timestamp = 0.0  -- Runtime should provide actual timestamp
    newDragState = DragDrop.startDrag source initialPos noOffset timestamp state.dragState
  in
    state { dragState = newDragState }
