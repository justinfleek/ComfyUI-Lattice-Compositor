-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // kanban // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Types — Core type definitions for the Kanban board component.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Identity (UUID5 for deterministic IDs)
-- |
-- | ## Architecture
-- |
-- | The Kanban board is composed of:
-- | - BoardId: Unique board identifier
-- | - ColumnId: Unique column identifier  
-- | - CardId: Unique card identifier
-- | - Priority: Card urgency level (bounded enum)
-- | - CardLabel: Tag with color
-- | - Swimlane: Horizontal grouping

module Hydrogen.Element.Compound.Kanban.Types
  ( -- * Identifiers
    BoardId
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
  
  -- * Priority
  , Priority(PriorityLow, PriorityMedium, PriorityHigh, PriorityUrgent)
  , priorityToInt
  , priorityFromInt
  , priorityLabel
  
  -- * WIP Limit
  , WIPLimit
  , wipLimit
  , unwrapWIPLimit
  , noWIPLimit
  , isOverWIPLimit
  
  -- * Messages
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
  
  -- * Drop Position
  , DropPosition(DropBefore, DropAfter, DropInto)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , compare
  , show
  , (==)
  , (>)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // identifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique board identifier
newtype BoardId = BoardId String

derive instance eqBoardId :: Eq BoardId
derive instance ordBoardId :: Ord BoardId

instance showBoardId :: Show BoardId where
  show (BoardId s) = "BoardId(" <> s <> ")"

-- | Create board ID
boardId :: String -> BoardId
boardId = BoardId

-- | Unwrap board ID
unwrapBoardId :: BoardId -> String
unwrapBoardId (BoardId s) = s

-- | Unique column identifier
newtype ColumnId = ColumnId String

derive instance eqColumnId :: Eq ColumnId
derive instance ordColumnId :: Ord ColumnId

instance showColumnId :: Show ColumnId where
  show (ColumnId s) = "ColumnId(" <> s <> ")"

-- | Create column ID
columnId :: String -> ColumnId
columnId = ColumnId

-- | Unwrap column ID
unwrapColumnId :: ColumnId -> String
unwrapColumnId (ColumnId s) = s

-- | Unique card identifier
newtype CardId = CardId String

derive instance eqCardId :: Eq CardId
derive instance ordCardId :: Ord CardId

instance showCardId :: Show CardId where
  show (CardId s) = "CardId(" <> s <> ")"

-- | Create card ID
cardId :: String -> CardId
cardId = CardId

-- | Unwrap card ID
unwrapCardId :: CardId -> String
unwrapCardId (CardId s) = s

-- | Unique swimlane identifier
newtype SwimlaneId = SwimlaneId String

derive instance eqSwimlaneId :: Eq SwimlaneId
derive instance ordSwimlaneId :: Ord SwimlaneId

instance showSwimlaneId :: Show SwimlaneId where
  show (SwimlaneId s) = "SwimlaneId(" <> s <> ")"

-- | Create swimlane ID
swimlaneId :: String -> SwimlaneId
swimlaneId = SwimlaneId

-- | Unwrap swimlane ID
unwrapSwimlaneId :: SwimlaneId -> String
unwrapSwimlaneId (SwimlaneId s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // priority
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card priority level (bounded: 4 values)
data Priority
  = PriorityLow
  | PriorityMedium
  | PriorityHigh
  | PriorityUrgent

derive instance eqPriority :: Eq Priority
derive instance ordPriority :: Ord Priority

instance showPriority :: Show Priority where
  show PriorityLow = "low"
  show PriorityMedium = "medium"
  show PriorityHigh = "high"
  show PriorityUrgent = "urgent"

-- | Convert priority to sortable integer (0-3)
priorityToInt :: Priority -> Int
priorityToInt PriorityLow = 0
priorityToInt PriorityMedium = 1
priorityToInt PriorityHigh = 2
priorityToInt PriorityUrgent = 3

-- | Parse priority from integer (clamped)
priorityFromInt :: Int -> Priority
priorityFromInt n
  | n > 2 = PriorityUrgent
  | n > 1 = PriorityHigh
  | n > 0 = PriorityMedium
  | true = PriorityLow

-- | Human-readable priority label
priorityLabel :: Priority -> String
priorityLabel PriorityLow = "Low"
priorityLabel PriorityMedium = "Medium"
priorityLabel PriorityHigh = "High"
priorityLabel PriorityUrgent = "Urgent"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // wip limit
-- ═════════════════════════════════════════════════════════════════════════════

-- | Work-In-Progress limit for a column
-- | Nothing means unlimited, Just n means maximum n cards
newtype WIPLimit = WIPLimit (Maybe Int)

derive instance eqWIPLimit :: Eq WIPLimit

instance showWIPLimit :: Show WIPLimit where
  show (WIPLimit Nothing) = "unlimited"
  show (WIPLimit (Just n)) = show n

-- | Create WIP limit
wipLimit :: Int -> WIPLimit
wipLimit n = WIPLimit (Just n)

-- | Unwrap WIP limit
unwrapWIPLimit :: WIPLimit -> Maybe Int
unwrapWIPLimit (WIPLimit m) = m

-- | No WIP limit (unlimited)
noWIPLimit :: WIPLimit
noWIPLimit = WIPLimit Nothing

-- | Check if current count exceeds WIP limit
isOverWIPLimit :: WIPLimit -> Int -> Boolean
isOverWIPLimit (WIPLimit Nothing) _ = false
isOverWIPLimit (WIPLimit (Just limit)) count = count > limit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kanban board messages
data KanbanMsg
  = MoveCard CardId ColumnId Int
      -- ^ Move card to column at index
  | MoveColumn ColumnId Int
      -- ^ Move column to index
  | AddCard ColumnId
      -- ^ Add card to column
  | RemoveCard CardId
      -- ^ Remove card
  | ExpandCard CardId
      -- ^ Expand card details
  | CollapseCard CardId
      -- ^ Collapse card details
  | ToggleColumnCollapse ColumnId
      -- ^ Toggle column collapsed state
  | BeginDrag CardId
      -- ^ Begin dragging card
  | UpdateDrag Number Number
      -- ^ Update drag position (x, y)
  | EndDrag
      -- ^ End drag operation
  | CancelDrag
      -- ^ Cancel drag operation
  | SelectCard CardId
      -- ^ Select a card
  | DeselectCard
      -- ^ Clear card selection

derive instance eqKanbanMsg :: Eq KanbanMsg

instance showKanbanMsg :: Show KanbanMsg where
  show (MoveCard cid colId idx) = 
    "MoveCard(" <> show cid <> ", " <> show colId <> ", " <> show idx <> ")"
  show (MoveColumn colId idx) = 
    "MoveColumn(" <> show colId <> ", " <> show idx <> ")"
  show (AddCard colId) = "AddCard(" <> show colId <> ")"
  show (RemoveCard cid) = "RemoveCard(" <> show cid <> ")"
  show (ExpandCard cid) = "ExpandCard(" <> show cid <> ")"
  show (CollapseCard cid) = "CollapseCard(" <> show cid <> ")"
  show (ToggleColumnCollapse colId) = "ToggleColumnCollapse(" <> show colId <> ")"
  show (BeginDrag cid) = "BeginDrag(" <> show cid <> ")"
  show (UpdateDrag x y) = "UpdateDrag(" <> show x <> ", " <> show y <> ")"
  show EndDrag = "EndDrag"
  show CancelDrag = "CancelDrag"
  show (SelectCard cid) = "SelectCard(" <> show cid <> ")"
  show DeselectCard = "DeselectCard"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // drop position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position for dropping a card
data DropPosition
  = DropBefore  -- ^ Drop before target
  | DropAfter   -- ^ Drop after target
  | DropInto    -- ^ Drop into container (column)

derive instance eqDropPosition :: Eq DropPosition

instance showDropPosition :: Show DropPosition where
  show DropBefore = "before"
  show DropAfter = "after"
  show DropInto = "into"
