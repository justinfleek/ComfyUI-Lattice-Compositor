-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // kanban // card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Card — Card data structure and operations.
-- |
-- | ## Dependencies
-- | - Kanban.Types (CardId, ColumnId, Priority)
-- | - Hydrogen.Schema.Color.RGB (label colors)
-- |
-- | ## Card Structure
-- |
-- | Cards are pure data containing:
-- | - Unique identifier
-- | - Title and description
-- | - Labels with colors
-- | - Assignee
-- | - Due date
-- | - Priority level
-- | - Expanded state

module Hydrogen.Element.Compound.Kanban.Card
  ( -- * Card Data
    KanbanCard
  , kanbanCard
  , emptyCard
  
  -- * Accessors
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
  
  -- * Modifiers
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
  
  -- * Labels
  , CardLabel
  , cardLabel
  , labelText
  , labelColor
  
  -- * Assignee
  , Assignee
  , assignee
  , assigneeName
  , assigneeAvatar
  , assigneeInitials
  
  -- * Due Date
  , DueDate
  , dueDate
  , dueDateYear
  , dueDateMonth
  , dueDateDay
  , isDueDatePast
  , isDueDateToday
  , isDueDateSoon
  , formatDueDate
  
  -- * Utility
  , labelTexts
  , hasLabel
  ) where

import Prelude
  ( class Eq
  , class Show
  , map
  , not
  , show
  , (&&)
  , (+)
  , (-)
  , (<)
  , (<>)
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (||)
  )

import Data.Array (filter, snoc)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String

import Hydrogen.Element.Compound.Kanban.Types
  ( CardId
  , ColumnId
  , Priority(PriorityLow)
  , SwimlaneId
  , cardId
  )
import Hydrogen.Schema.Color.RGB as Color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // card label
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card label with text and color
type CardLabel =
  { text :: String
  , color :: Color.RGB
  }

-- | Create a card label
cardLabel :: String -> Color.RGB -> CardLabel
cardLabel text color = { text, color }

-- | Get label text
labelText :: CardLabel -> String
labelText lbl = lbl.text

-- | Get label color
labelColor :: CardLabel -> Color.RGB
labelColor lbl = lbl.color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // assignee
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card assignee
type Assignee =
  { name :: String
  , avatar :: Maybe String
  }

-- | Create an assignee
assignee :: String -> Maybe String -> Assignee
assignee name avatar = { name, avatar }

-- | Get assignee name
assigneeName :: Assignee -> String
assigneeName a = a.name

-- | Get assignee avatar URL
assigneeAvatar :: Assignee -> Maybe String
assigneeAvatar a = a.avatar

-- | Get initials from name (first character)
assigneeInitials :: Assignee -> String
assigneeInitials a =
  let first = String.take 1 a.name
  in if first == "" then "?" else first

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // due date
-- ═════════════════════════════════════════════════════════════════════════════

-- | Due date for a card
type DueDate =
  { year :: Int
  , month :: Int  -- 1-12
  , day :: Int    -- 1-31
  }

-- | Create a due date
dueDate :: Int -> Int -> Int -> DueDate
dueDate year month day = { year, month, day }

-- | Get year
dueDateYear :: DueDate -> Int
dueDateYear d = d.year

-- | Get month (1-12)
dueDateMonth :: DueDate -> Int
dueDateMonth d = d.month

-- | Get day (1-31)
dueDateDay :: DueDate -> Int
dueDateDay d = d.day

-- | Check if due date is in the past
-- | Requires current date for comparison
isDueDatePast :: DueDate -> DueDate -> Boolean
isDueDatePast current due =
  due.year < current.year
  || (due.year == current.year && due.month < current.month)
  || (due.year == current.year && due.month == current.month && due.day < current.day)

-- | Check if due date is today
isDueDateToday :: DueDate -> DueDate -> Boolean
isDueDateToday current due =
  due.year == current.year
  && due.month == current.month
  && due.day == current.day

-- | Check if due date is within 3 days
isDueDateSoon :: DueDate -> DueDate -> Boolean
isDueDateSoon current due =
  not (isDueDatePast current due)
  && due.year == current.year
  && due.month == current.month
  && due.day >= current.day
  && due.day < current.day + 3

-- | Format due date for display (YYYY-MM-DD)
formatDueDate :: DueDate -> String
formatDueDate d =
  show d.year <> "-" <> padZero d.month <> "-" <> padZero d.day
  where
    padZero :: Int -> String
    padZero n = if n < 10 then "0" <> show n else show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // kanban card
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kanban card data
type KanbanCard =
  { id :: CardId
  , title :: String
  , description :: String
  , labels :: Array CardLabel
  , assignee :: Maybe Assignee
  , dueDate :: Maybe DueDate
  , priority :: Priority
  , expanded :: Boolean
  , columnId :: ColumnId
  , swimlaneId :: Maybe SwimlaneId
  , index :: Int
  }

-- | Create a kanban card
kanbanCard :: CardId -> String -> ColumnId -> KanbanCard
kanbanCard id title columnId =
  { id
  , title
  , description: ""
  , labels: []
  , assignee: Nothing
  , dueDate: Nothing
  , priority: PriorityLow
  , expanded: false
  , columnId
  , swimlaneId: Nothing
  , index: 0
  }

-- | Create an empty card with generated ID
emptyCard :: String -> ColumnId -> KanbanCard
emptyCard idStr columnId = kanbanCard (cardId idStr) "" columnId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get card ID
cardIdOf :: KanbanCard -> CardId
cardIdOf c = c.id

-- | Get card title
cardTitle :: KanbanCard -> String
cardTitle c = c.title

-- | Get card description
cardDescription :: KanbanCard -> String
cardDescription c = c.description

-- | Get card labels
cardLabels :: KanbanCard -> Array CardLabel
cardLabels c = c.labels

-- | Get card assignee
cardAssignee :: KanbanCard -> Maybe Assignee
cardAssignee c = c.assignee

-- | Get card due date
cardDueDate :: KanbanCard -> Maybe DueDate
cardDueDate c = c.dueDate

-- | Get card priority
cardPriority :: KanbanCard -> Priority
cardPriority c = c.priority

-- | Get card expanded state
cardExpanded :: KanbanCard -> Boolean
cardExpanded c = c.expanded

-- | Get card column ID
cardColumnId :: KanbanCard -> ColumnId
cardColumnId c = c.columnId

-- | Get card swimlane ID
cardSwimlaneId :: KanbanCard -> Maybe SwimlaneId
cardSwimlaneId c = c.swimlaneId

-- | Get card index within column
cardIndex :: KanbanCard -> Int
cardIndex c = c.index

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set card title
setCardTitle :: String -> KanbanCard -> KanbanCard
setCardTitle title c = c { title = title }

-- | Set card description
setCardDescription :: String -> KanbanCard -> KanbanCard
setCardDescription desc c = c { description = desc }

-- | Add a label to card
addCardLabel :: CardLabel -> KanbanCard -> KanbanCard
addCardLabel lbl c = c { labels = snoc c.labels lbl }

-- | Remove a label by text
removeCardLabel :: String -> KanbanCard -> KanbanCard
removeCardLabel text c = 
  c { labels = filter (\l -> l.text /= text) c.labels }

-- | Set card assignee
setCardAssignee :: Assignee -> KanbanCard -> KanbanCard
setCardAssignee a c = c { assignee = Just a }

-- | Clear card assignee
clearCardAssignee :: KanbanCard -> KanbanCard
clearCardAssignee c = c { assignee = Nothing }

-- | Set card due date
setCardDueDate :: DueDate -> KanbanCard -> KanbanCard
setCardDueDate d c = c { dueDate = Just d }

-- | Clear card due date
clearCardDueDate :: KanbanCard -> KanbanCard
clearCardDueDate c = c { dueDate = Nothing }

-- | Set card priority
setCardPriority :: Priority -> KanbanCard -> KanbanCard
setCardPriority p c = c { priority = p }

-- | Set card expanded state
setCardExpanded :: Boolean -> KanbanCard -> KanbanCard
setCardExpanded e c = c { expanded = e }

-- | Toggle card expanded state
toggleCardExpanded :: KanbanCard -> KanbanCard
toggleCardExpanded c = c { expanded = not c.expanded }

-- | Set card column
setCardColumn :: ColumnId -> KanbanCard -> KanbanCard
setCardColumn colId c = c { columnId = colId }

-- | Set card swimlane
setCardSwimlane :: Maybe SwimlaneId -> KanbanCard -> KanbanCard
setCardSwimlane sId c = c { swimlaneId = sId }

-- | Set card index
setCardIndex :: Int -> KanbanCard -> KanbanCard
setCardIndex idx c = c { index = idx }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // utility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract all label texts from a card
-- | Useful for searching/filtering cards by labels
labelTexts :: KanbanCard -> Array String
labelTexts c = map (\lbl -> lbl.text) c.labels

-- | Check if a card has a label with the given text
hasLabel :: String -> KanbanCard -> Boolean
hasLabel labelName c = 
  let
    texts = labelTexts c
    matches = filter (\t -> t == labelName) texts
  in
    not (matches == [])
