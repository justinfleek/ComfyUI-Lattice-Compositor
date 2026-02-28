-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // gestural // selection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Selection - single, multi, and range selection patterns.
-- |
-- | Models selection behavior for lists, grids, and arbitrary items.
-- | Supports Ctrl/Cmd+click multi-select and Shift+click range select.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Array (elem, filter, snoc)
-- | - Data.Maybe (Maybe)
-- |
-- | ## Dependents
-- | - Component.List (list selection)
-- | - Component.Grid (grid selection)
-- | - Component.Table (table row selection)
-- | - Component.FileManager (file selection)

module Hydrogen.Schema.Gestural.Selection
  ( -- * Selection Mode
    SelectionMode(SelectNone, SelectSingle, SelectMultiple, SelectRange)
  , allowsMultiple
  , allowsRange
    -- * Selection Action
  , SelectionAction(SelectOne, SelectToggle, SelectExtend, SelectAll, ClearSelection, SelectInvert)
  , actionFromModifiers
    -- * Selectable Item
  , SelectableItem
  , selectableItem
  , itemId
  , itemIndex
  , itemDisabled
  , isSelectable
    -- * Selection Anchor
  , SelectionAnchor
  , noAnchor
  , anchorAt
  , anchorId
  , anchorIndex
  , hasAnchor
    -- * Selection Range
  , SelectionRange
  , emptyRange
  , rangeFromIndices
  , rangeStart
  , rangeEnd
  , rangeSize
  , inRange
  , expandRange
  , contractRange
    -- * Selection Rectangle (Marquee)
  , SelectionRect
  , selectionRect
  , rectFromPoints
  , rectX
  , rectY
  , rectWidth
  , rectHeight
  , rectContainsPoint
  , rectIntersectsRect
    -- * Selection State
  , SelectionState
  , emptySelection
  , singleSelection
  , selectionMode
  , selectedIds
  , selectedCount
  , isSelected
  , hasSelection
  , selectItem
  , deselectItem
  , toggleItem
  , selectRange
  , selectAll
  , clearSelection
  , invertSelection
  ) where

import Prelude

import Data.Array (elem, filter, length, notElem, snoc)
import Data.Maybe (Maybe(Just, Nothing), isJust)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // selection // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection mode
data SelectionMode
  = SelectNone      -- ^ Selection disabled
  | SelectSingle    -- ^ Only one item at a time
  | SelectMultiple  -- ^ Multiple items via Ctrl/Cmd+click
  | SelectRange     -- ^ Range selection via Shift+click

derive instance eqSelectionMode :: Eq SelectionMode
derive instance ordSelectionMode :: Ord SelectionMode

instance showSelectionMode :: Show SelectionMode where
  show SelectNone = "none"
  show SelectSingle = "single"
  show SelectMultiple = "multiple"
  show SelectRange = "range"

-- | Does mode allow multiple selection?
allowsMultiple :: SelectionMode -> Boolean
allowsMultiple SelectMultiple = true
allowsMultiple SelectRange = true
allowsMultiple _ = false

-- | Does mode allow range selection?
allowsRange :: SelectionMode -> Boolean
allowsRange SelectRange = true
allowsRange _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // selection // action
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection action type
data SelectionAction
  = SelectOne       -- ^ Select only this item (clear others)
  | SelectToggle    -- ^ Toggle this item's selection
  | SelectExtend    -- ^ Extend selection to this item (range)
  | SelectAll       -- ^ Select all items
  | ClearSelection  -- ^ Clear selection
  | SelectInvert    -- ^ Invert selection

derive instance eqSelectionAction :: Eq SelectionAction
derive instance ordSelectionAction :: Ord SelectionAction

instance showSelectionAction :: Show SelectionAction where
  show SelectOne = "one"
  show SelectToggle = "toggle"
  show SelectExtend = "extend"
  show SelectAll = "all"
  show ClearSelection = "clear"
  show SelectInvert = "invert"

-- | Determine action from modifier keys
-- |
-- | Ctrl/Cmd = toggle, Shift = extend, neither = select one
actionFromModifiers :: { ctrl :: Boolean, shift :: Boolean } -> SelectionAction
actionFromModifiers mods
  | mods.shift = SelectExtend
  | mods.ctrl = SelectToggle
  | otherwise = SelectOne

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selectable // item
-- ═════════════════════════════════════════════════════════════════════════════

-- | An item that can be selected
type SelectableItem =
  { id :: String       -- ^ Unique identifier
  , index :: Int       -- ^ Position in list (for range select)
  , disabled :: Boolean -- ^ Can this item be selected?
  }

-- | Create selectable item
selectableItem :: String -> Int -> SelectableItem
selectableItem id index = { id, index, disabled: false }

-- | Get item ID
itemId :: SelectableItem -> String
itemId si = si.id

-- | Get item index
itemIndex :: SelectableItem -> Int
itemIndex si = si.index

-- | Is item disabled?
itemDisabled :: SelectableItem -> Boolean
itemDisabled si = si.disabled

-- | Is item selectable?
isSelectable :: SelectableItem -> Boolean
isSelectable si = not si.disabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // selection // anchor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anchor point for range selection
type SelectionAnchor =
  { id :: Maybe String    -- ^ Anchor element ID
  , index :: Maybe Int    -- ^ Anchor element index
  }

-- | No anchor set
noAnchor :: SelectionAnchor
noAnchor = { id: Nothing, index: Nothing }

-- | Set anchor at item
anchorAt :: SelectableItem -> SelectionAnchor
anchorAt item = { id: Just item.id, index: Just item.index }

-- | Get anchor ID
anchorId :: SelectionAnchor -> Maybe String
anchorId sa = sa.id

-- | Get anchor index
anchorIndex :: SelectionAnchor -> Maybe Int
anchorIndex sa = sa.index

-- | Is anchor set?
hasAnchor :: SelectionAnchor -> Boolean
hasAnchor sa = isJust sa.id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selection // range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range of selected indices
type SelectionRange =
  { start :: Int    -- ^ Start index (inclusive)
  , end :: Int      -- ^ End index (inclusive)
  }

-- | Empty range
emptyRange :: SelectionRange
emptyRange = { start: 0, end: -1 }

-- | Create range from two indices (order independent)
rangeFromIndices :: Int -> Int -> SelectionRange
rangeFromIndices a b =
  if a <= b
    then { start: a, end: b }
    else { start: b, end: a }

-- | Get range start
rangeStart :: SelectionRange -> Int
rangeStart sr = sr.start

-- | Get range end
rangeEnd :: SelectionRange -> Int
rangeEnd sr = sr.end

-- | Get range size
rangeSize :: SelectionRange -> Int
rangeSize sr =
  if sr.end < sr.start then 0 else sr.end - sr.start + 1

-- | Is index in range?
inRange :: Int -> SelectionRange -> Boolean
inRange idx sr = idx >= sr.start && idx <= sr.end

-- | Expand range to include index
expandRange :: Int -> SelectionRange -> SelectionRange
expandRange idx sr =
  { start: min sr.start idx
  , end: max sr.end idx
  }

-- | Contract range (remove from end or start based on index position)
contractRange :: Int -> SelectionRange -> SelectionRange
contractRange idx sr
  | idx == sr.start = sr { start = sr.start + 1 }
  | idx == sr.end = sr { end = sr.end - 1 }
  | otherwise = sr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // selection // rect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rectangle for marquee/lasso selection
type SelectionRect =
  { x :: Number       -- ^ Left edge
  , y :: Number       -- ^ Top edge
  , width :: Number   -- ^ Width
  , height :: Number  -- ^ Height
  }

-- | Create selection rectangle
selectionRect :: Number -> Number -> Number -> Number -> SelectionRect
selectionRect x y width height = { x, y, width, height }

-- | Create rectangle from two corner points
rectFromPoints :: { x :: Number, y :: Number } -> { x :: Number, y :: Number } -> SelectionRect
rectFromPoints p1 p2 =
  let
    minX = min p1.x p2.x
    minY = min p1.y p2.y
    maxX = max p1.x p2.x
    maxY = max p1.y p2.y
  in { x: minX, y: minY, width: maxX - minX, height: maxY - minY }

-- | Get rect X
rectX :: SelectionRect -> Number
rectX sr = sr.x

-- | Get rect Y
rectY :: SelectionRect -> Number
rectY sr = sr.y

-- | Get rect width
rectWidth :: SelectionRect -> Number
rectWidth sr = sr.width

-- | Get rect height
rectHeight :: SelectionRect -> Number
rectHeight sr = sr.height

-- | Does rect contain point?
rectContainsPoint :: { x :: Number, y :: Number } -> SelectionRect -> Boolean
rectContainsPoint p sr =
  p.x >= sr.x && p.x <= sr.x + sr.width
  && p.y >= sr.y && p.y <= sr.y + sr.height

-- | Do two rects intersect?
rectIntersectsRect :: SelectionRect -> SelectionRect -> Boolean
rectIntersectsRect a b =
  a.x < b.x + b.width && a.x + a.width > b.x
  && a.y < b.y + b.height && a.y + a.height > b.y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selection // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete selection state
type SelectionState =
  { mode :: SelectionMode          -- ^ Selection mode
  , selected :: Array String       -- ^ Selected item IDs
  , anchor :: SelectionAnchor      -- ^ Anchor for range selection
  , allItems :: Array SelectableItem  -- ^ All available items
  , timestamp :: Number            -- ^ Last change timestamp
  }

-- | Empty selection
emptySelection :: SelectionMode -> SelectionState
emptySelection mode =
  { mode
  , selected: []
  , anchor: noAnchor
  , allItems: []
  , timestamp: 0.0
  }

-- | Single item selected
singleSelection :: SelectionMode -> SelectableItem -> SelectionState
singleSelection mode item =
  { mode
  , selected: [item.id]
  , anchor: anchorAt item
  , allItems: [item]
  , timestamp: 0.0
  }

-- | Get selection mode
selectionMode :: SelectionState -> SelectionMode
selectionMode ss = ss.mode

-- | Get selected IDs
selectedIds :: SelectionState -> Array String
selectedIds ss = ss.selected

-- | Get selected count
selectedCount :: SelectionState -> Int
selectedCount ss = length ss.selected

-- | Is item selected?
isSelected :: String -> SelectionState -> Boolean
isSelected id ss = elem id ss.selected

-- | Is anything selected?
hasSelection :: SelectionState -> Boolean
hasSelection ss = length ss.selected > 0

-- | Select a single item (clears others)
selectItem :: SelectableItem -> Number -> SelectionState -> SelectionState
selectItem item ts ss =
  ss { selected = [item.id]
     , anchor = anchorAt item
     , timestamp = ts
     }

-- | Deselect an item
deselectItem :: String -> Number -> SelectionState -> SelectionState
deselectItem id ts ss =
  ss { selected = filter (_ /= id) ss.selected
     , timestamp = ts
     }

-- | Toggle item selection
toggleItem :: SelectableItem -> Number -> SelectionState -> SelectionState
toggleItem item ts ss =
  if isSelected item.id ss
    then deselectItem item.id ts ss
    else ss { selected = snoc ss.selected item.id
            , anchor = anchorAt item
            , timestamp = ts
            }

-- | Select range from anchor to item
selectRange :: SelectableItem -> Number -> SelectionState -> SelectionState
selectRange item ts ss = case ss.anchor.index of
  Nothing -> selectItem item ts ss
  Just anchorIdx ->
    let
      range = rangeFromIndices anchorIdx item.index
      inRangeItems = filter (\i -> inRange i.index range && isSelectable i) ss.allItems
      newSelected = map _.id inRangeItems
    in ss { selected = newSelected, timestamp = ts }

-- | Select all items
selectAll :: Number -> SelectionState -> SelectionState
selectAll ts ss =
  let allIds = map _.id (filter isSelectable ss.allItems)
  in ss { selected = allIds, timestamp = ts }

-- | Clear selection
clearSelection :: Number -> SelectionState -> SelectionState
clearSelection ts ss =
  ss { selected = [], anchor = noAnchor, timestamp = ts }

-- | Invert selection
invertSelection :: Number -> SelectionState -> SelectionState
invertSelection ts ss =
  let
    selectableIds = map _.id (filter isSelectable ss.allItems)
    inverted = filter (\id -> notElem id ss.selected) selectableIds
  in ss { selected = inverted, timestamp = ts }
