-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // kanban // column
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Column — Column data structure and operations.
-- |
-- | ## Dependencies
-- | - Kanban.Types (ColumnId, WIPLimit)
-- | - Kanban.Card (KanbanCard)
-- | - Hydrogen.Schema.Color.RGB (header colors)
-- |
-- | ## Column Structure
-- |
-- | Columns contain:
-- | - Unique identifier
-- | - Title
-- | - Optional header color
-- | - WIP limit
-- | - Collapsed state
-- | - Index position

module Hydrogen.Element.Compound.Kanban.Column
  ( -- * Column Data
    KanbanColumn
  , kanbanColumn
  , emptyColumn
  
  -- * Accessors
  , columnIdOf
  , columnTitle
  , columnColor
  , columnWIPLimit
  , columnCollapsed
  , columnIndex
  , columnCollapsible
  
  -- * Modifiers
  , setColumnTitle
  , setColumnColor
  , clearColumnColor
  , setColumnWIPLimit
  , removeColumnWIPLimit
  , setColumnCollapsed
  , toggleColumnCollapsed
  , setColumnIndex
  , setColumnCollapsible
  
  -- * Queries
  , isColumnOverWIP
  , columnCardCountLabel
  ) where

import Prelude
  ( class Eq
  , class Show
  , not
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Compound.Kanban.Types
  ( ColumnId
  , WIPLimit
  , columnId
  , isOverWIPLimit
  , noWIPLimit
  , unwrapWIPLimit
  )
import Hydrogen.Schema.Color.RGB as Color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // kanban column
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kanban column data
type KanbanColumn =
  { id :: ColumnId
  , title :: String
  , color :: Maybe Color.RGB
  , wipLimit :: WIPLimit
  , collapsed :: Boolean
  , collapsible :: Boolean
  , index :: Int
  }

-- | Create a kanban column
kanbanColumn :: ColumnId -> String -> KanbanColumn
kanbanColumn id title =
  { id
  , title
  , color: Nothing
  , wipLimit: noWIPLimit
  , collapsed: false
  , collapsible: true
  , index: 0
  }

-- | Create an empty column with generated ID
emptyColumn :: String -> String -> KanbanColumn
emptyColumn idStr title = kanbanColumn (columnId idStr) title

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get column ID
columnIdOf :: KanbanColumn -> ColumnId
columnIdOf c = c.id

-- | Get column title
columnTitle :: KanbanColumn -> String
columnTitle c = c.title

-- | Get column header color
columnColor :: KanbanColumn -> Maybe Color.RGB
columnColor c = c.color

-- | Get column WIP limit
columnWIPLimit :: KanbanColumn -> WIPLimit
columnWIPLimit c = c.wipLimit

-- | Get column collapsed state
columnCollapsed :: KanbanColumn -> Boolean
columnCollapsed c = c.collapsed

-- | Get column index
columnIndex :: KanbanColumn -> Int
columnIndex c = c.index

-- | Get whether column is collapsible
columnCollapsible :: KanbanColumn -> Boolean
columnCollapsible c = c.collapsible

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set column title
setColumnTitle :: String -> KanbanColumn -> KanbanColumn
setColumnTitle title c = c { title = title }

-- | Set column header color
setColumnColor :: Color.RGB -> KanbanColumn -> KanbanColumn
setColumnColor color c = c { color = Just color }

-- | Clear column header color
clearColumnColor :: KanbanColumn -> KanbanColumn
clearColumnColor c = c { color = Nothing }

-- | Set column WIP limit
setColumnWIPLimit :: WIPLimit -> KanbanColumn -> KanbanColumn
setColumnWIPLimit limit c = c { wipLimit = limit }

-- | Remove column WIP limit
removeColumnWIPLimit :: KanbanColumn -> KanbanColumn
removeColumnWIPLimit c = c { wipLimit = noWIPLimit }

-- | Set column collapsed state
setColumnCollapsed :: Boolean -> KanbanColumn -> KanbanColumn
setColumnCollapsed collapsed c = c { collapsed = collapsed }

-- | Toggle column collapsed state
toggleColumnCollapsed :: KanbanColumn -> KanbanColumn
toggleColumnCollapsed c = c { collapsed = not c.collapsed }

-- | Set column index
setColumnIndex :: Int -> KanbanColumn -> KanbanColumn
setColumnIndex idx c = c { index = idx }

-- | Set whether column is collapsible
setColumnCollapsible :: Boolean -> KanbanColumn -> KanbanColumn
setColumnCollapsible collapsible c = c { collapsible = collapsible }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if column is over WIP limit
isColumnOverWIP :: Int -> KanbanColumn -> Boolean
isColumnOverWIP cardCount c = isOverWIPLimit c.wipLimit cardCount

-- | Format card count label with optional WIP limit
columnCardCountLabel :: Int -> KanbanColumn -> String
columnCardCountLabel cardCount c = case unwrapWIPLimit c.wipLimit of
  Nothing -> show cardCount
  Just limit -> show cardCount <> " / " <> show limit
