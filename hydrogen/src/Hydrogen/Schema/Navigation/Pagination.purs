-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // navigation // pagination
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pagination - atoms for paged navigation through sequences.
-- |
-- | Covers two use cases:
-- |
-- | ## 1. Viewport Pagination (Carousels, Galleries)
-- |
-- | Shows multiple items at once with sliding window:
-- | - `ItemsVisible`: How many items show simultaneously (1, 2, 3...)
-- | - `ItemsToScroll`: How many to advance per navigation action
-- | - `Gap`: Space between visible items
-- |
-- | ## 2. Page-Based Pagination (Data Tables, Search Results)
-- |
-- | Classic page numbers:
-- | - `PageSize`: Items per page (10, 25, 50, 100)
-- | - `PageNumber`: Current page (1-indexed for display)
-- | - `TotalItems`: Total result count
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Bounded (clampInt)
-- | - Hydrogen.Schema.Dimension.Device (Pixel)
-- |
-- | ## Dependents
-- | - Component.Carousel (viewport pagination)
-- | - Component.Pagination (page-based)
-- | - Component.DataGrid (page-based)

module Hydrogen.Schema.Navigation.Pagination
  ( -- * Items Visible (Viewport)
    ItemsVisible(ItemsVisible)
  , itemsVisible
  , unwrapItemsVisible
  , singleItem
  , doubleItem
  , tripleItem
  , itemsVisibleBounds
  
  -- * Items to Scroll
  , ItemsToScroll(ItemsToScroll)
  , itemsToScroll
  , unwrapItemsToScroll
  , scrollOne
  , scrollAll
  , itemsToScrollBounds
  
  -- * Item Gap
  , ItemGap(ItemGap)
  , itemGap
  , noGap
  , unwrapItemGap
  
  -- * Viewport State (Molecule)
  , ViewportState
  , viewportState
  , viewportPosition
  , viewportVisible
  , viewportScroll
  , viewportGap
  , viewportCanScroll
  , windowStart
  , windowEnd
  , isItemVisible
  
  -- * Page Size
  , PageSize(PageSize)
  , pageSize
  , unwrapPageSize
  , pageSize10
  , pageSize25
  , pageSize50
  , pageSize100
  , pageSizeBounds
  
  -- * Page Number
  , PageNumber(PageNumber)
  , pageNumber
  , unwrapPageNumber
  , firstPage
  , pageNumberBounds
  
  -- * Total Items
  , TotalItems(TotalItems)
  , totalItems
  , unwrapTotalItems
  , totalItemsBounds
  
  -- * Page State (Molecule)
  , PageState
  , pageState
  , currentPage
  , totalPages
  , pageItems
  , hasNextPage
  , hasPrevPage
  , itemRange
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , min
  , (-)
  , (+)
  , (/)
  , (*)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Int (ceil, toNumber)
import Hydrogen.Schema.Bounded (IntBounds, intBounds, clampInt)
import Hydrogen.Schema.Dimension.Device (Pixel, px)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // items visible
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of items visible simultaneously [1, 20]
-- |
-- | For carousels, galleries, and any sliding-window navigation.
-- | Minimum 1 (must show at least one item).
-- | Maximum 20 (practical limit for most UIs).
newtype ItemsVisible = ItemsVisible Int

derive instance eqItemsVisible :: Eq ItemsVisible
derive instance ordItemsVisible :: Ord ItemsVisible

instance showItemsVisible :: Show ItemsVisible where
  show (ItemsVisible n) = show n <> " visible"

-- | Create items visible (clamps to [1, 20])
itemsVisible :: Int -> ItemsVisible
itemsVisible n = ItemsVisible (clampInt 1 20 n)

-- | Extract raw value
unwrapItemsVisible :: ItemsVisible -> Int
unwrapItemsVisible (ItemsVisible n) = n

-- | Show one item at a time
singleItem :: ItemsVisible
singleItem = ItemsVisible 1

-- | Show two items at a time
doubleItem :: ItemsVisible
doubleItem = ItemsVisible 2

-- | Show three items at a time
tripleItem :: ItemsVisible
tripleItem = ItemsVisible 3

-- | Bounds for ItemsVisible
itemsVisibleBounds :: IntBounds
itemsVisibleBounds = intBounds 1 20 "itemsVisible" "Items visible at once (1-20)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // items to scroll
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of items to advance per navigation action [1, 20]
-- |
-- | Typically 1 (scroll one item at a time) or equal to ItemsVisible
-- | (scroll an entire "page" at a time).
newtype ItemsToScroll = ItemsToScroll Int

derive instance eqItemsToScroll :: Eq ItemsToScroll
derive instance ordItemsToScroll :: Ord ItemsToScroll

instance showItemsToScroll :: Show ItemsToScroll where
  show (ItemsToScroll n) = "scroll " <> show n

-- | Create items to scroll (clamps to [1, 20])
itemsToScroll :: Int -> ItemsToScroll
itemsToScroll n = ItemsToScroll (clampInt 1 20 n)

-- | Extract raw value
unwrapItemsToScroll :: ItemsToScroll -> Int
unwrapItemsToScroll (ItemsToScroll n) = n

-- | Scroll one item at a time
scrollOne :: ItemsToScroll
scrollOne = ItemsToScroll 1

-- | Scroll all visible items (creates "page" scrolling)
-- |
-- | Takes ItemsVisible to match the visible count
scrollAll :: ItemsVisible -> ItemsToScroll
scrollAll (ItemsVisible n) = ItemsToScroll n

-- | Bounds for ItemsToScroll
itemsToScrollBounds :: IntBounds
itemsToScrollBounds = intBounds 1 20 "itemsToScroll" "Items to advance per action (1-20)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // item gap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gap between visible items in pixels
-- |
-- | Uses Pixel from Dimension schema for proper unit typing.
newtype ItemGap = ItemGap Pixel

derive instance eqItemGap :: Eq ItemGap
derive instance ordItemGap :: Ord ItemGap

instance showItemGap :: Show ItemGap where
  show (ItemGap p) = "gap " <> show p

-- | Create item gap from pixel value
itemGap :: Number -> ItemGap
itemGap n = ItemGap (px n)

-- | No gap between items
noGap :: ItemGap
noGap = ItemGap (px 0.0)

-- | Extract pixel value
unwrapItemGap :: ItemGap -> Pixel
unwrapItemGap (ItemGap p) = p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // viewport state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete viewport pagination state
-- |
-- | Combines position with viewport settings for carousel-style navigation.
type ViewportState =
  { position :: Int           -- ^ First visible item index (0-based)
  , count :: Int              -- ^ Total items
  , visible :: ItemsVisible   -- ^ Items visible at once
  , scroll :: ItemsToScroll   -- ^ Items to scroll per action
  , gap :: ItemGap            -- ^ Gap between items
  }

-- | Create viewport state
viewportState :: Int -> Int -> ItemsVisible -> ItemsToScroll -> ItemGap -> ViewportState
viewportState pos cnt vis scr gp =
  let
    maxPos = if cnt <= unwrapItemsVisible vis then 0 else cnt - unwrapItemsVisible vis
    clampedPos = clampInt 0 maxPos pos
  in
    { position: clampedPos
    , count: cnt
    , visible: vis
    , scroll: scr
    , gap: gp
    }

-- | Get current position (first visible item index)
viewportPosition :: ViewportState -> Int
viewportPosition vs = vs.position

-- | Get items visible setting
viewportVisible :: ViewportState -> Int
viewportVisible vs = unwrapItemsVisible vs.visible

-- | Get items to scroll setting
viewportScroll :: ViewportState -> Int
viewportScroll vs = unwrapItemsToScroll vs.scroll

-- | Get gap setting
viewportGap :: ViewportState -> ItemGap
viewportGap vs = vs.gap

-- | Can scroll further in either direction?
viewportCanScroll :: ViewportState -> Boolean
viewportCanScroll vs = vs.count > unwrapItemsVisible vs.visible

-- | Get index of first visible item
windowStart :: ViewportState -> Int
windowStart vs = vs.position

-- | Get index of last visible item (exclusive)
windowEnd :: ViewportState -> Int
windowEnd vs = min (vs.position + unwrapItemsVisible vs.visible) vs.count

-- | Is a specific item index currently visible?
isItemVisible :: Int -> ViewportState -> Boolean
isItemVisible idx vs = idx >= windowStart vs && idx < windowEnd vs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // page size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of items per page [1, 500]
-- |
-- | For traditional pagination (data tables, search results).
newtype PageSize = PageSize Int

derive instance eqPageSize :: Eq PageSize
derive instance ordPageSize :: Ord PageSize

instance showPageSize :: Show PageSize where
  show (PageSize n) = show n <> " per page"

-- | Create page size (clamps to [1, 500])
pageSize :: Int -> PageSize
pageSize n = PageSize (clampInt 1 500 n)

-- | Extract raw value
unwrapPageSize :: PageSize -> Int
unwrapPageSize (PageSize n) = n

-- | 10 items per page
pageSize10 :: PageSize
pageSize10 = PageSize 10

-- | 25 items per page
pageSize25 :: PageSize
pageSize25 = PageSize 25

-- | 50 items per page
pageSize50 :: PageSize
pageSize50 = PageSize 50

-- | 100 items per page
pageSize100 :: PageSize
pageSize100 = PageSize 100

-- | Bounds for PageSize
pageSizeBounds :: IntBounds
pageSizeBounds = intBounds 1 500 "pageSize" "Items per page (1-500)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // page number
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current page number [1, 100000]
-- |
-- | 1-indexed for display purposes (users see "Page 1", not "Page 0").
newtype PageNumber = PageNumber Int

derive instance eqPageNumber :: Eq PageNumber
derive instance ordPageNumber :: Ord PageNumber

instance showPageNumber :: Show PageNumber where
  show (PageNumber n) = "page " <> show n

-- | Create page number (clamps to [1, 100000])
pageNumber :: Int -> PageNumber
pageNumber n = PageNumber (clampInt 1 100000 n)

-- | Extract raw value
unwrapPageNumber :: PageNumber -> Int
unwrapPageNumber (PageNumber n) = n

-- | First page
firstPage :: PageNumber
firstPage = PageNumber 1

-- | Bounds for PageNumber
pageNumberBounds :: IntBounds
pageNumberBounds = intBounds 1 100000 "pageNumber" "Page number (1-100000)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // total items
-- ═════════════════════════════════════════════════════════════════════════════

-- | Total number of items in dataset [0, MAX_INT]
-- |
-- | For calculating total pages.
newtype TotalItems = TotalItems Int

derive instance eqTotalItems :: Eq TotalItems
derive instance ordTotalItems :: Ord TotalItems

instance showTotalItems :: Show TotalItems where
  show (TotalItems n) = show n <> " total"

-- | Create total items count
totalItems :: Int -> TotalItems
totalItems n = TotalItems (if n < 0 then 0 else n)

-- | Extract raw value
unwrapTotalItems :: TotalItems -> Int
unwrapTotalItems (TotalItems n) = n

-- | Bounds for TotalItems (practical upper limit)
totalItemsBounds :: IntBounds
totalItemsBounds = intBounds 0 2147483647 "totalItems" "Total items in dataset (0-MAX_INT)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // page state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete page-based pagination state
type PageState =
  { page :: PageNumber       -- ^ Current page (1-indexed)
  , size :: PageSize         -- ^ Items per page
  , total :: TotalItems      -- ^ Total items in dataset
  }

-- | Create page state
pageState :: Int -> Int -> Int -> PageState
pageState pg sz tot =
  let
    validTotal = if tot < 0 then 0 else tot
    validSize = clampInt 1 500 sz
    maxPage = calcTotalPages validTotal validSize
    validPage = clampInt 1 (if maxPage == 0 then 1 else maxPage) pg
  in
    { page: PageNumber validPage
    , size: PageSize validSize
    , total: TotalItems validTotal
    }

-- | Get current page number
currentPage :: PageState -> Int
currentPage ps = unwrapPageNumber ps.page

-- | Calculate total number of pages
totalPages :: PageState -> Int
totalPages ps = calcTotalPages (unwrapTotalItems ps.total) (unwrapPageSize ps.size)

-- | Get page size
pageItems :: PageState -> Int
pageItems ps = unwrapPageSize ps.size

-- | Is there a next page?
hasNextPage :: PageState -> Boolean
hasNextPage ps = currentPage ps < totalPages ps

-- | Is there a previous page?
hasPrevPage :: PageState -> Boolean
hasPrevPage ps = currentPage ps > 1

-- | Get item index range for current page (start, end exclusive)
-- |
-- | Returns 0-indexed range: page 1 with size 10 returns (0, 10)
itemRange :: PageState -> { start :: Int, end :: Int }
itemRange ps =
  let
    pg = currentPage ps
    sz = pageItems ps
    tot = unwrapTotalItems ps.total
    start = (pg - 1) * sz
    end = min (start + sz) tot
  in
    { start, end }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total pages from items and page size
calcTotalPages :: Int -> Int -> Int
calcTotalPages tot sz
  | tot <= 0 = 0
  | sz <= 0 = 0
  | tot <= sz = 1
  | true = ceil (toNumber tot / toNumber sz)
