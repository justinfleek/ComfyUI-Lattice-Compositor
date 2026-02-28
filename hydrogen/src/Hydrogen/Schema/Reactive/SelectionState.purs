-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // reactive // selection-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SelectionState - selection models for lists, grids, and trees.
-- |
-- | Covers single selection, multi-selection, range selection,
-- | and hierarchical selection with indeterminate states.

module Hydrogen.Schema.Reactive.SelectionState
  ( -- * Selection Mode
    SelectionMode(..)
  , isSingleMode
  , isMultipleMode
  , isRangeMode
  , isNoneMode
  -- * Selection Status (per item)
  , SelectionStatus(..)
  , isSelected
  , isUnselected
  , isIndeterminate
  -- * Selection Anchor
  , SelectionAnchor
  , selectionAnchor
  , noAnchor
  , hasAnchor
  , anchorIndex
  -- * Selection Range
  , SelectionRange
  , selectionRange
  , rangeStart
  , rangeEnd
  , rangeSize
  , isInRange
  , expandRange
  -- * Single Selection (Molecule)
  , SingleSelection
  , singleSelection
  , noSelection
  , selectSingle
  , clearSingle
  , selectedIndex
  , hasSelection
  -- * Multi Selection (Molecule)
  , MultiSelection
  , multiSelection
  , emptyMultiSelection
  , selectIndex
  , deselectIndex
  , toggleIndex
  , selectAll
  , deselectAll
  , selectRange
  , selectedIndices
  , selectionCount
  , isAllSelected
  , isNoneSelected
  , isSomeSelected
  -- * Hierarchical Selection (Compound)
  , HierarchicalStatus(..)
  , isFullySelected
  , isPartiallySelected
  , isNotSelected
  , computeParentStatus
  ) where

import Prelude

import Data.Array (concat, elem, filter, length, nub, range, sort, (..))
import Data.Maybe (Maybe(Just, Nothing), isJust)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // selection mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection behavior mode
data SelectionMode
  = SelectionNone      -- ^ No selection allowed
  | SelectionSingle    -- ^ Only one item at a time
  | SelectionMultiple  -- ^ Any number of items
  | SelectionRange     -- ^ Contiguous range with shift+click

derive instance eqSelectionMode :: Eq SelectionMode
derive instance ordSelectionMode :: Ord SelectionMode

instance showSelectionMode :: Show SelectionMode where
  show SelectionNone = "none"
  show SelectionSingle = "single"
  show SelectionMultiple = "multiple"
  show SelectionRange = "range"

isSingleMode :: SelectionMode -> Boolean
isSingleMode SelectionSingle = true
isSingleMode _ = false

isMultipleMode :: SelectionMode -> Boolean
isMultipleMode SelectionMultiple = true
isMultipleMode _ = false

isRangeMode :: SelectionMode -> Boolean
isRangeMode SelectionRange = true
isRangeMode _ = false

isNoneMode :: SelectionMode -> Boolean
isNoneMode SelectionNone = true
isNoneMode _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // selection status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection state of individual item
data SelectionStatus
  = Selected         -- ^ Item is selected
  | Unselected       -- ^ Item is not selected
  | Indeterminate    -- ^ Partial selection (for parent with mixed children)

derive instance eqSelectionStatus :: Eq SelectionStatus
derive instance ordSelectionStatus :: Ord SelectionStatus

instance showSelectionStatus :: Show SelectionStatus where
  show Selected = "selected"
  show Unselected = "unselected"
  show Indeterminate = "indeterminate"

isSelected :: SelectionStatus -> Boolean
isSelected Selected = true
isSelected _ = false

isUnselected :: SelectionStatus -> Boolean
isUnselected Unselected = true
isUnselected _ = false

isIndeterminate :: SelectionStatus -> Boolean
isIndeterminate Indeterminate = true
isIndeterminate _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // selection anchor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anchor point for range selection (where shift+click started)
type SelectionAnchor =
  { index :: Maybe Int
  }

-- | Create selection anchor at index
selectionAnchor :: Int -> SelectionAnchor
selectionAnchor i = { index: Just i }

-- | No anchor set
noAnchor :: SelectionAnchor
noAnchor = { index: Nothing }

-- | Is anchor set?
hasAnchor :: SelectionAnchor -> Boolean
hasAnchor a = isJust a.index

-- | Get anchor index
anchorIndex :: SelectionAnchor -> Maybe Int
anchorIndex a = a.index

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // selection range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contiguous selection range
type SelectionRange =
  { start :: Int
  , end :: Int
  }

-- | Create selection range (normalizes order)
selectionRange :: Int -> Int -> SelectionRange
selectionRange a b = 
  { start: min a b
  , end: max a b
  }

-- | Get range start
rangeStart :: SelectionRange -> Int
rangeStart r = r.start

-- | Get range end
rangeEnd :: SelectionRange -> Int
rangeEnd r = r.end

-- | Get range size
rangeSize :: SelectionRange -> Int
rangeSize r = r.end - r.start + 1

-- | Is index within range?
isInRange :: Int -> SelectionRange -> Boolean
isInRange i r = i >= r.start && i <= r.end

-- | Expand range to include new index
expandRange :: Int -> SelectionRange -> SelectionRange
expandRange i r = selectionRange (min i r.start) (max i r.end)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // single selection molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single item selection state
type SingleSelection =
  { selected :: Maybe Int
  , lastSelected :: Maybe Int  -- ^ Previous selection (for undo)
  }

-- | Create single selection
singleSelection :: Maybe Int -> SingleSelection
singleSelection idx = 
  { selected: idx
  , lastSelected: Nothing
  }

-- | No selection
noSelection :: SingleSelection
noSelection = singleSelection Nothing

-- | Select index
selectSingle :: Int -> SingleSelection -> SingleSelection
selectSingle i s = 
  { selected: Just i
  , lastSelected: s.selected
  }

-- | Clear selection
clearSingle :: SingleSelection -> SingleSelection
clearSingle s = 
  { selected: Nothing
  , lastSelected: s.selected
  }

-- | Get selected index
selectedIndex :: SingleSelection -> Maybe Int
selectedIndex s = s.selected

-- | Has selection?
hasSelection :: SingleSelection -> Boolean
hasSelection s = isJust s.selected

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // multi selection molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Multiple item selection state
type MultiSelection =
  { indices :: Array Int           -- ^ Currently selected indices
  , anchor :: SelectionAnchor      -- ^ Range selection anchor
  , lastToggled :: Maybe Int       -- ^ Last toggled index
  , totalCount :: Int              -- ^ Total items (for select all)
  }

-- | Create multi selection
multiSelection :: Array Int -> Int -> MultiSelection
multiSelection indices total =
  { indices: sort (nub indices)
  , anchor: noAnchor
  , lastToggled: Nothing
  , totalCount: total
  }

-- | Empty multi selection
emptyMultiSelection :: Int -> MultiSelection
emptyMultiSelection total = multiSelection [] total

-- | Select index (add to selection)
selectIndex :: Int -> MultiSelection -> MultiSelection
selectIndex i ms =
  ms { indices = sort (nub (concat [ms.indices, [i]]))
     , anchor = selectionAnchor i
     , lastToggled = Just i
     }

-- | Deselect index (remove from selection)
deselectIndex :: Int -> MultiSelection -> MultiSelection
deselectIndex i ms =
  ms { indices = filter (_ /= i) ms.indices
     , lastToggled = Just i
     }

-- | Toggle index selection
toggleIndex :: Int -> MultiSelection -> MultiSelection
toggleIndex i ms =
  if elem i ms.indices
    then deselectIndex i ms
    else selectIndex i ms

-- | Select all items
selectAll :: MultiSelection -> MultiSelection
selectAll ms =
  ms { indices = range 0 (ms.totalCount - 1) }

-- | Deselect all items
deselectAll :: MultiSelection -> MultiSelection
deselectAll ms =
  ms { indices = []
     , anchor = noAnchor
     }

-- | Select range from anchor to index
selectRange :: Int -> MultiSelection -> MultiSelection
selectRange i ms = case ms.anchor.index of
  Nothing -> selectIndex i ms
  Just anchor ->
    let r = selectionRange anchor i
        rangeIndices = r.start .. r.end
    in ms { indices = sort (nub (concat [ms.indices, rangeIndices]))
          , lastToggled = Just i
          }

-- | Get all selected indices
selectedIndices :: MultiSelection -> Array Int
selectedIndices ms = ms.indices

-- | Get selection count
selectionCount :: MultiSelection -> Int
selectionCount ms = length ms.indices

-- | Are all items selected?
isAllSelected :: MultiSelection -> Boolean
isAllSelected ms = length ms.indices == ms.totalCount && ms.totalCount > 0

-- | Are no items selected?
isNoneSelected :: MultiSelection -> Boolean
isNoneSelected ms = length ms.indices == 0

-- | Are some but not all items selected?
isSomeSelected :: MultiSelection -> Boolean
isSomeSelected ms = 
  let count = length ms.indices
  in count > 0 && count < ms.totalCount

-- ═════════════════════════════════════════════════════════════════════════════
--                                            // hierarchical selection compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hierarchical selection status (for tree structures)
data HierarchicalStatus
  = FullySelected      -- ^ Node and all descendants selected
  | PartiallySelected  -- ^ Some but not all descendants selected
  | NotSelected        -- ^ Node and all descendants unselected

derive instance eqHierarchicalStatus :: Eq HierarchicalStatus
derive instance ordHierarchicalStatus :: Ord HierarchicalStatus

instance showHierarchicalStatus :: Show HierarchicalStatus where
  show FullySelected = "fully-selected"
  show PartiallySelected = "partially-selected"
  show NotSelected = "not-selected"

isFullySelected :: HierarchicalStatus -> Boolean
isFullySelected FullySelected = true
isFullySelected _ = false

isPartiallySelected :: HierarchicalStatus -> Boolean
isPartiallySelected PartiallySelected = true
isPartiallySelected _ = false

isNotSelected :: HierarchicalStatus -> Boolean
isNotSelected NotSelected = true
isNotSelected _ = false

-- | Compute parent status from children statuses
computeParentStatus :: Array HierarchicalStatus -> HierarchicalStatus
computeParentStatus children
  | length children == 0 = NotSelected
  | length (filter isFullySelected children) == length children = FullySelected
  | length (filter isNotSelected children) == length children = NotSelected
  | otherwise = PartiallySelected
