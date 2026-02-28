-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // navigation // index
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Index - bounded position within a finite sequence.
-- |
-- | The foundational atom for any sequential navigation: carousels, tabs,
-- | accordions, steppers, playlists, galleries, pagination.
-- |
-- | ## Boundary Behavior
-- |
-- | When navigating past boundaries, two behaviors are possible:
-- |
-- | - **Clamp**: Stop at edges (0 or count-1)
-- | - **Wrap**: Loop around (going past end returns to start)
-- |
-- | The behavior is encoded in the type, making intentions explicit.
-- |
-- | ## Design Philosophy
-- |
-- | An index alone is meaningless — it requires a count (the sequence length).
-- | Together they form an `IndexedPosition` molecule that guarantees:
-- |
-- | - Index is always valid (0 <= index < count)
-- | - Navigation operations maintain validity
-- | - No array bounds exceptions possible
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, Ring)
-- | - Hydrogen.Schema.Bounded (clampInt)
-- |
-- | ## Dependents
-- | - Navigation.Pagination (uses IndexedPosition)
-- | - Component.Carousel (slide position)
-- | - Component.Tabs (active tab)
-- | - Component.Stepper (current step)
-- | - Component.Accordion (expanded panels)

module Hydrogen.Schema.Navigation.Index
  ( -- * Boundary Behavior
    BoundaryBehavior(Clamp, Wrap)
  , isClamp
  , isWrap
  
  -- * Count (Sequence Length)
  , Count(Count)
  , count
  , unwrapCount
  , countBounds
  , isEmpty
  , isSingleton
  
  -- * Index (Position)
  , Index(Index)
  , index
  , unsafeIndex
  , unwrapIndex
  , indexBounds
  , isFirst
  , isLast
  
  -- * Indexed Position (Molecule)
  , IndexedPosition
  , indexedPosition
  , position
  , total
  , behavior
  , atFirst
  , atLast
  , canGoNext
  , canGoPrev
  
  -- * Navigation Operations
  , next
  , prev
  , goTo
  , goToFirst
  , goToLast
  , advance
  , retreat
  
  -- * Computed Properties
  , progressRatio
  , remaining
  , distanceToEnd
  , distanceToStart
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , mod
  , (-)
  , (+)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Int (toNumber)
import Hydrogen.Schema.Bounded (IntBounds, intBounds, clampInt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // boundary behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to handle navigation past sequence boundaries
-- |
-- | - `Clamp`: Stop at edges — cannot go below 0 or above count-1
-- | - `Wrap`: Loop around — going past end returns to start, and vice versa
data BoundaryBehavior
  = Clamp
  | Wrap

derive instance eqBoundaryBehavior :: Eq BoundaryBehavior
derive instance ordBoundaryBehavior :: Ord BoundaryBehavior

instance showBoundaryBehavior :: Show BoundaryBehavior where
  show Clamp = "clamp"
  show Wrap = "wrap"

-- | Is behavior clamping?
isClamp :: BoundaryBehavior -> Boolean
isClamp Clamp = true
isClamp Wrap = false

-- | Is behavior wrapping?
isWrap :: BoundaryBehavior -> Boolean
isWrap Wrap = true
isWrap Clamp = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of items in a sequence [0, 10000]
-- |
-- | Upper bound prevents unbounded sequences that could cause performance issues.
-- | For larger datasets, use pagination or virtualization.
newtype Count = Count Int

derive instance eqCount :: Eq Count
derive instance ordCount :: Ord Count

instance showCount :: Show Count where
  show (Count n) = show n <> " items"

-- | Create a count value (clamps to [0, 10000])
count :: Int -> Count
count n = Count (clampInt 0 10000 n)

-- | Extract raw count value
unwrapCount :: Count -> Int
unwrapCount (Count n) = n

-- | Bounds for Count
countBounds :: IntBounds
countBounds = intBounds 0 10000 "count" "Number of items in sequence (0-10000)"

-- | Is the sequence empty?
isEmpty :: Count -> Boolean
isEmpty (Count n) = n == 0

-- | Does the sequence have exactly one item?
isSingleton :: Count -> Boolean
isSingleton (Count n) = n == 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero-based index into a sequence [0, 9999]
-- |
-- | An index alone is not meaningful — it must be paired with a Count
-- | to form an IndexedPosition that guarantees validity.
newtype Index = Index Int

derive instance eqIndex :: Eq Index
derive instance ordIndex :: Ord Index

instance showIndex :: Show Index where
  show (Index n) = "index " <> show n

-- | Create an index (clamps to [0, 9999])
-- |
-- | Note: This does not guarantee the index is valid for a given sequence.
-- | Use `indexedPosition` to create a validated position.
index :: Int -> Index
index n = Index (clampInt 0 9999 n)

-- | Create an index without bounds checking
-- |
-- | Only use when you've already validated the value.
unsafeIndex :: Int -> Index
unsafeIndex = Index

-- | Extract raw index value
unwrapIndex :: Index -> Int
unwrapIndex (Index n) = n

-- | Bounds for Index
indexBounds :: IntBounds
indexBounds = intBounds 0 9999 "index" "Zero-based position in sequence (0-9999)"

-- | Is this index 0?
isFirst :: Index -> Boolean
isFirst (Index n) = n == 0

-- | Is this index count-1?
-- |
-- | Requires the count to determine.
isLast :: Index -> Count -> Boolean
isLast (Index idx) (Count cnt) = cnt > 0 && idx == cnt - 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // indexed position
-- ═════════════════════════════════════════════════════════════════════════════

-- | A valid position within a sequence
-- |
-- | This molecule guarantees:
-- | - 0 <= index < count (when count > 0)
-- | - index == 0 (when count == 0, empty sequence)
-- | - Navigation operations maintain these invariants
type IndexedPosition =
  { index :: Index
  , count :: Count
  , behavior :: BoundaryBehavior
  }

-- | Create an indexed position, validating the index against the count
-- |
-- | If index >= count, it is clamped or wrapped based on behavior.
-- | If count == 0, index is always 0.
indexedPosition :: Int -> Int -> BoundaryBehavior -> IndexedPosition
indexedPosition idx cnt bhv =
  let
    validCount = clampInt 0 10000 cnt
    validIndex = 
      if validCount == 0 
        then 0
        else case bhv of
          Clamp -> clampInt 0 (validCount - 1) idx
          Wrap -> wrapIndex idx validCount
  in
    { index: Index validIndex
    , count: Count validCount
    , behavior: bhv
    }

-- | Get current index
position :: IndexedPosition -> Int
position ip = unwrapIndex ip.index

-- | Get total count
total :: IndexedPosition -> Int
total ip = unwrapCount ip.count

-- | Get boundary behavior
behavior :: IndexedPosition -> BoundaryBehavior
behavior ip = ip.behavior

-- | Is at first position?
atFirst :: IndexedPosition -> Boolean
atFirst ip = position ip == 0

-- | Is at last position?
atLast :: IndexedPosition -> Boolean
atLast ip = 
  let cnt = total ip
  in cnt > 0 && position ip == cnt - 1

-- | Can navigate to next item?
-- |
-- | Always true for Wrap behavior (unless empty).
-- | For Clamp, only true if not at last position.
canGoNext :: IndexedPosition -> Boolean
canGoNext ip = case ip.behavior of
  Wrap -> total ip > 0
  Clamp -> total ip > 0 && position ip < total ip - 1

-- | Can navigate to previous item?
-- |
-- | Always true for Wrap behavior (unless empty).
-- | For Clamp, only true if not at first position.
canGoPrev :: IndexedPosition -> Boolean
canGoPrev ip = case ip.behavior of
  Wrap -> total ip > 0
  Clamp -> position ip > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // navigation operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Move to next position
next :: IndexedPosition -> IndexedPosition
next ip = advance 1 ip

-- | Move to previous position
prev :: IndexedPosition -> IndexedPosition
prev ip = retreat 1 ip

-- | Go to specific index
goTo :: Int -> IndexedPosition -> IndexedPosition
goTo targetIdx ip = 
  indexedPosition targetIdx (total ip) ip.behavior

-- | Go to first position
goToFirst :: IndexedPosition -> IndexedPosition
goToFirst ip = goTo 0 ip

-- | Go to last position
goToLast :: IndexedPosition -> IndexedPosition
goToLast ip = goTo (total ip - 1) ip

-- | Advance by n positions (can be negative)
advance :: Int -> IndexedPosition -> IndexedPosition
advance n ip =
  let
    current = position ip
    cnt = total ip
  in
    if cnt == 0 
      then ip
      else indexedPosition (current + n) cnt ip.behavior

-- | Retreat by n positions (same as advance with negative n)
retreat :: Int -> IndexedPosition -> IndexedPosition
retreat n = advance (negate n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress through sequence as ratio (0.0 to 1.0)
-- |
-- | Returns 0.0 for empty sequences.
-- | Returns 1.0 when at last position.
progressRatio :: IndexedPosition -> Number
progressRatio ip =
  let cnt = total ip
  in if cnt <= 1 
    then 0.0
    else toNumber (position ip) / toNumber (cnt - 1)

-- | Number of items remaining after current position
remaining :: IndexedPosition -> Int
remaining ip = 
  let cnt = total ip
      idx = position ip
  in if cnt == 0 then 0 else cnt - idx - 1

-- | Distance to end (same as remaining)
distanceToEnd :: IndexedPosition -> Int
distanceToEnd = remaining

-- | Distance to start (same as current index)
distanceToStart :: IndexedPosition -> Int
distanceToStart = position

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wrap index to valid range [0, count)
-- |
-- | Handles negative indices correctly:
-- | wrapIndex (-1) 5 = 4
-- | wrapIndex 5 5 = 0
-- | wrapIndex 7 5 = 2
wrapIndex :: Int -> Int -> Int
wrapIndex idx cnt
  | cnt <= 0 = 0
  | otherwise = 
      let m = idx `mod` cnt
      in if m < 0 then m + cnt else m
