-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // layout // flex
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Flexbox Layout Engine — Pure Data Layout Computation
-- |
-- | Computes layout as pure data, independent of CSS or DOM.
-- | Given container dimensions and child constraints, produces
-- | absolute positions and sizes for each child.
-- |
-- | ## Architecture
-- |
-- | ```
-- | FlexContainer + Array FlexItem
-- |     ↓ computeLayout
-- | Array LayoutResult { x, y, width, height }
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Dimension (Pixel, sizing)
-- |
-- | ## Dependents
-- | - Hydrogen.GPU.Flatten (layout before flattening to DrawCommand)

module Hydrogen.Layout.Flex
  ( -- * Container
    FlexContainer
  , flexContainer
  
  -- * Items
  , FlexItem
  , flexItem
  
  -- * Direction
  , FlexDirection(Row, RowReverse, Column, ColumnReverse)
  
  -- * Alignment
  , FlexAlign(AlignStart, AlignCenter, AlignEnd, AlignStretch)
  , FlexJustify(JustifyStart, JustifyCenter, JustifyEnd, JustifySpaceBetween, JustifySpaceAround, JustifySpaceEvenly)
  
  -- * Layout Result
  , LayoutResult
  , computeLayout
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , otherwise
  , ($)
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (>)
  , (>=)
  , (<>)
  )

import Data.Array (length, take, drop) as Array

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flex direction — main axis orientation
data FlexDirection
  = Row
  | RowReverse
  | Column
  | ColumnReverse

derive instance eqFlexDirection :: Eq FlexDirection

-- | Is this a row direction?
isRow :: FlexDirection -> Boolean
isRow Row = true
isRow RowReverse = true
isRow _ = false

-- | Is this reversed?
isReversed :: FlexDirection -> Boolean
isReversed RowReverse = true
isReversed ColumnReverse = true
isReversed _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cross-axis alignment
data FlexAlign
  = AlignStart
  | AlignCenter
  | AlignEnd
  | AlignStretch

derive instance eqFlexAlign :: Eq FlexAlign

-- | Main-axis justification
data FlexJustify
  = JustifyStart
  | JustifyCenter
  | JustifyEnd
  | JustifySpaceBetween
  | JustifySpaceAround
  | JustifySpaceEvenly

derive instance eqFlexJustify :: Eq FlexJustify

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flex container configuration
type FlexContainer =
  { width :: Number
  , height :: Number
  , direction :: FlexDirection
  , justify :: FlexJustify
  , align :: FlexAlign
  , gap :: Number
  , padding :: Number
  }

-- | Create a flex container with defaults
flexContainer :: Number -> Number -> FlexContainer
flexContainer width height =
  { width
  , height
  , direction: Row
  , justify: JustifyStart
  , align: AlignStretch
  , gap: 0.0
  , padding: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // items
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flex item constraints
type FlexItem =
  { minWidth :: Number
  , minHeight :: Number
  , maxWidth :: Number
  , maxHeight :: Number
  , basis :: Number      -- ^ Preferred size on main axis
  , grow :: Number       -- ^ Flex grow factor
  , shrink :: Number     -- ^ Flex shrink factor
  , alignSelf :: FlexAlign
  }

-- | Create a flex item with defaults
flexItem :: Number -> Number -> FlexItem
flexItem basis size =
  { minWidth: 0.0
  , minHeight: 0.0
  , maxWidth: 99999.0
  , maxHeight: 99999.0
  , basis: basis
  , grow: 0.0
  , shrink: 1.0
  , alignSelf: AlignStretch
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layout result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout result for a single item
type LayoutResult =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute layout for all items in a flex container
computeLayout :: FlexContainer -> Array FlexItem -> Array LayoutResult
computeLayout container items =
  let
    n = Array.length items
    availableMain = mainAxisSize container - container.padding * 2.0
    availableCross = crossAxisSize container - container.padding * 2.0
    totalGap = container.gap * toNumber (maxInt 0 (n - 1))
    spaceForItems = availableMain - totalGap
    
    -- Compute main axis sizes
    mainSizes = computeMainSizes container.direction spaceForItems items
    
    -- Compute positions based on justification
    positions = computePositions container mainSizes
  in
    zipWithIndex (\i item -> 
      let
        mainSize = getAt i mainSizes
        crossSize = computeCrossSize container.align availableCross item
        pos = getAt i positions
      in
        if isRow container.direction
          then { x: pos + container.padding
               , y: computeCrossPosition container.align availableCross crossSize + container.padding
               , width: mainSize
               , height: crossSize
               }
          else { x: computeCrossPosition container.align availableCross crossSize + container.padding
               , y: pos + container.padding
               , width: crossSize
               , height: mainSize
               }
    ) items

-- | Get main axis size of container
mainAxisSize :: FlexContainer -> Number
mainAxisSize c = if isRow c.direction then c.width else c.height

-- | Get cross axis size of container
crossAxisSize :: FlexContainer -> Number
crossAxisSize c = if isRow c.direction then c.height else c.width

-- | Compute main axis sizes for items
computeMainSizes :: FlexDirection -> Number -> Array FlexItem -> Array Number
computeMainSizes _dir available items =
  let
    n = Array.length items
    totalBasis = sumArray (mapArray (\i -> i.basis) items)
    remaining = available - totalBasis
    totalGrow = sumArray (mapArray (\i -> i.grow) items)
  in
    if remaining > 0.0 && totalGrow > 0.0
      then mapArray (\i -> i.basis + remaining * i.grow / totalGrow) items
      else mapArray (\i -> i.basis) items

-- | Compute positions based on justify
computePositions :: FlexContainer -> Array Number -> Array Number
computePositions container sizes =
  let
    n = Array.length sizes
    totalSize = sumArray sizes
    totalGap = container.gap * toNumber (maxInt 0 (n - 1))
    used = totalSize + totalGap
    available = mainAxisSize container - container.padding * 2.0
    freeSpace = available - used
  in
    case container.justify of
      JustifyStart -> computeStartPositions container.gap sizes
      JustifyEnd -> computeEndPositions freeSpace container.gap sizes
      JustifyCenter -> computeCenterPositions (freeSpace / 2.0) container.gap sizes
      JustifySpaceBetween -> computeSpaceBetweenPositions available sizes
      JustifySpaceAround -> computeSpaceAroundPositions available sizes
      JustifySpaceEvenly -> computeSpaceEvenlyPositions available sizes

-- | Start-aligned positions
computeStartPositions :: Number -> Array Number -> Array Number
computeStartPositions gap sizes = scanl (\pos size -> pos + size + gap) 0.0 sizes

-- | End-aligned positions  
computeEndPositions :: Number -> Number -> Array Number -> Array Number
computeEndPositions offset gap sizes = 
  mapArray (\p -> p + offset) (computeStartPositions gap sizes)

-- | Center-aligned positions
computeCenterPositions :: Number -> Number -> Array Number -> Array Number
computeCenterPositions offset gap sizes =
  mapArray (\p -> p + offset) (computeStartPositions gap sizes)

-- | Space-between positions
computeSpaceBetweenPositions :: Number -> Array Number -> Array Number
computeSpaceBetweenPositions available sizes =
  let
    n = Array.length sizes
    totalSize = sumArray sizes
    gap = if n > 1 then (available - totalSize) / toNumber (n - 1) else 0.0
  in
    computeStartPositions gap sizes

-- | Space-around positions
computeSpaceAroundPositions :: Number -> Array Number -> Array Number
computeSpaceAroundPositions available sizes =
  let
    n = Array.length sizes
    totalSize = sumArray sizes
    gap = (available - totalSize) / toNumber (n * 2)
  in
    mapArray (\p -> p + gap) (computeStartPositions (gap * 2.0) sizes)

-- | Space-evenly positions
computeSpaceEvenlyPositions :: Number -> Array Number -> Array Number
computeSpaceEvenlyPositions available sizes =
  let
    n = Array.length sizes
    totalSize = sumArray sizes
    gap = (available - totalSize) / toNumber (n + 1)
  in
    mapArray (\p -> p + gap) (computeStartPositions gap sizes)

-- | Compute cross axis size for item
computeCrossSize :: FlexAlign -> Number -> FlexItem -> Number
computeCrossSize align available item = case align of
  AlignStretch -> clamp item.minHeight item.maxHeight available
  _ -> item.basis  -- Use basis as hint for non-stretch

-- | Compute cross axis position
computeCrossPosition :: FlexAlign -> Number -> Number -> Number
computeCrossPosition align available itemSize = case align of
  AlignStart -> 0.0
  AlignCenter -> (available - itemSize) / 2.0
  AlignEnd -> available - itemSize
  AlignStretch -> 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map over array
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f = foldlArray (\acc x -> acc <> [f x]) []

-- | Zip with index
zipWithIndex :: forall a b. (Int -> a -> b) -> Array a -> Array b
zipWithIndex f arr = zipWithIndexGo f arr 0 []

zipWithIndexGo :: forall a b. (Int -> a -> b) -> Array a -> Int -> Array b -> Array b
zipWithIndexGo f arr i acc = case Array.take 1 arr of
  [] -> acc
  [x] -> zipWithIndexGo f (Array.drop 1 arr) (i + 1) (acc <> [f i x])
  _ -> acc

-- | Scan left (prefix sums)
scanl :: forall a b. (b -> a -> b) -> b -> Array a -> Array b
scanl f init arr = scanlGo f init arr []

scanlGo :: forall a b. (b -> a -> b) -> b -> Array a -> Array b -> Array b
scanlGo f acc arr result = case Array.take 1 arr of
  [] -> result
  [x] -> scanlGo f (f acc x) (Array.drop 1 arr) (result <> [acc])
  _ -> result

-- | Fold left
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr = case Array.take 1 arr of
  [] -> init
  [x] -> foldlArray f (f init x) (Array.drop 1 arr)
  _ -> init

-- | Sum array of numbers
sumArray :: Array Number -> Number
sumArray = foldlArray (+) 0.0

-- | Get element at index (returns 0.0 for out of bounds)
getAt :: Int -> Array Number -> Number
getAt i arr = case Array.take 1 (Array.drop i arr) of
  [x] -> x
  _ -> 0.0

-- | Clamp value between min and max
clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val

-- | Convert Int to Number
toNumber :: Int -> Number
toNumber i = toNumberGo i 0.0

toNumberGo :: Int -> Number -> Number
toNumberGo i acc
  | i <= 0 = acc
  | otherwise = toNumberGo (i - 1) (acc + 1.0)

-- | Max of two ints
maxInt :: Int -> Int -> Int
maxInt a b = if a > b then a else b
