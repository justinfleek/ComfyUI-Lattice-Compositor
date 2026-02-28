-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // element // pagination
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Pagination Component
-- |
-- | Page navigation controls for paginated content.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Pagination as Pagination
-- |
-- | -- Basic pagination
-- | Pagination.pagination
-- |   [ Pagination.currentPage 3
-- |   , Pagination.totalPages 10
-- |   , Pagination.onPageChange SetPage
-- |   ]
-- |
-- | -- With first/last buttons
-- | Pagination.pagination
-- |   [ Pagination.currentPage 5
-- |   , Pagination.totalPages 20
-- |   , Pagination.showFirstLast true
-- |   ]
-- |
-- | -- Compact mode for mobile
-- | Pagination.pagination
-- |   [ Pagination.currentPage 1
-- |   , Pagination.totalPages 10
-- |   , Pagination.compact true
-- |   ]
-- | ```
module Hydrogen.Element.Compound.Pagination
  ( -- * Pagination Components
    pagination
  , paginationWithInfo
  , paginationButton
  , paginationEllipsis
    -- * Props
  , PaginationProps
  , PaginationProp
  , PaginationInfo
  , defaultProps
    -- * Prop Builders
  , currentPage
  , totalPages
  , siblingCount
  , showFirstLast
  , compact
  , paginationDisabled
  , paginationClassName
  , onPageChange
    -- * Types
  , PageItem(Page, Ellipsis)
  ) where

import Prelude
  ( show
  , map
  , min
  , max
  , (<>)
  , (-)
  , (+)
  , (*)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (||)
  )

import Data.Array (foldl, range, filter, nub, sort, length)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

type PaginationProps msg =
  { currentPage :: Int
  , totalPages :: Int
  , siblingCount :: Int   -- Pages to show on each side of current
  , showFirstLast :: Boolean
  , compact :: Boolean
  , disabled :: Boolean
  , className :: String
  , onPageChange :: Maybe (Int -> msg)
  }

type PaginationProp msg = PaginationProps msg -> PaginationProps msg

defaultProps :: forall msg. PaginationProps msg
defaultProps =
  { currentPage: 1
  , totalPages: 1
  , siblingCount: 1
  , showFirstLast: false
  , compact: false
  , disabled: false
  , className: ""
  , onPageChange: Nothing
  }

-- | Set current page (1-indexed)
currentPage :: forall msg. Int -> PaginationProp msg
currentPage p props = props { currentPage = p }

-- | Set total number of pages
totalPages :: forall msg. Int -> PaginationProp msg
totalPages t props = props { totalPages = t }

-- | Set number of sibling pages to show
siblingCount :: forall msg. Int -> PaginationProp msg
siblingCount s props = props { siblingCount = s }

-- | Show first/last page buttons
showFirstLast :: forall msg. Boolean -> PaginationProp msg
showFirstLast s props = props { showFirstLast = s }

-- | Compact mode (prev/next only)
compact :: forall msg. Boolean -> PaginationProp msg
compact c props = props { compact = c }

-- | Set disabled state
paginationDisabled :: forall msg. Boolean -> PaginationProp msg
paginationDisabled d props = props { disabled = d }

-- | Add custom class
paginationClassName :: forall msg. String -> PaginationProp msg
paginationClassName c props = props { className = props.className <> " " <> c }

-- | Set page change handler
onPageChange :: forall msg. (Int -> msg) -> PaginationProp msg
onPageChange handler props = props { onPageChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pagination info
-- ═════════════════════════════════════════════════════════════════════════════

type PaginationInfo msg =
  { currentPage :: Int
  , totalPages :: Int
  , totalItems :: Int
  , pageSize :: Int
  , pageSizeOptions :: Array Int
  , onPageChange :: Int -> msg
  , onPageSizeChange :: Int -> msg
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // page range calc
-- ═════════════════════════════════════════════════════════════════════════════

data PageItem
  = Page Int
  | Ellipsis

-- | Generate page range with ellipsis
generatePageRange :: Int -> Int -> Int -> Array PageItem
generatePageRange current total siblings =
  let
    -- Always show first, last, and pages around current
    firstPage = 1
    lastPage = total
    
    -- Calculate range around current page
    rangeStart = max 2 (current - siblings)
    rangeEnd = min (total - 1) (current + siblings)
    
    -- Build array of page numbers to show
    pageNumbers = 
      [firstPage] 
      <> range rangeStart rangeEnd 
      <> (if total > 1 then [lastPage] else [])
    
    -- Sort and dedupe
    uniquePages = sort (nub pageNumbers)
    
    -- Add ellipsis where there are gaps
    addEllipsis :: Array Int -> Array PageItem
    addEllipsis pages = go pages [] Nothing
      where
        go :: Array Int -> Array PageItem -> Maybe Int -> Array PageItem
        go arr acc prevPage = case length arr of
          0 -> acc
          _ -> 
            let 
              currentVal = case take1 arr of
                Just v -> v
                Nothing -> 0
              rest = drop1 arr
              needsEllipsis = case prevPage of
                Just p -> currentVal - p > 1
                Nothing -> false
              newAcc = if needsEllipsis
                then acc <> [Ellipsis, Page currentVal]
                else acc <> [Page currentVal]
            in go rest newAcc (Just currentVal)
  in
    addEllipsis uniquePages
  where
    take1 :: Array Int -> Maybe Int
    take1 arr = case filter (\_ -> true) arr of
      [] -> Nothing
      xs -> 
        let result = foldl (\acc x -> case acc of
              Nothing -> Just x
              Just _ -> acc
            ) Nothing xs
        in result
    
    drop1 :: Array Int -> Array Int
    drop1 arr = 
      let indexed = foldl (\{ result, idx } x -> 
            if idx == 0 
              then { result, idx: idx + 1 }
              else { result: result <> [x], idx: idx + 1 }
          ) { result: [], idx: 0 } arr
      in indexed.result

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Main pagination component
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
pagination :: forall msg. Array (PaginationProp msg) -> E.Element msg
pagination propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Generate page numbers with ellipsis
    pages = generatePageRange props.currentPage props.totalPages props.siblingCount
  in
    E.nav_
      [ E.classes [ "flex items-center gap-1", props.className ]
      , E.ariaLabel "Pagination"
      ]
      (if props.compact
        then compactPagination props
        else fullPagination props pages
      )

-- | Full pagination with page numbers
fullPagination :: forall msg. PaginationProps msg -> Array PageItem -> Array (E.Element msg)
fullPagination props pages =
  -- First button
  (if props.showFirstLast
    then [ firstButton props ]
    else []
  )
  -- Previous button
  <> [ prevButton props ]
  -- Page numbers
  <> map (renderPageItem props) pages
  -- Next button
  <> [ nextButton props ]
  -- Last button
  <> (if props.showFirstLast
       then [ lastButton props ]
       else []
     )

-- | Compact pagination (prev/next only)
compactPagination :: forall msg. PaginationProps msg -> Array (E.Element msg)
compactPagination props =
  [ prevButton props
  , E.span_
      [ E.class_ "text-sm text-muted-foreground px-2" ]
      [ E.text (show props.currentPage <> " / " <> show props.totalPages) ]
  , nextButton props
  ]

-- | Pagination with info text and page size selector
paginationWithInfo :: forall msg. PaginationInfo msg -> E.Element msg
paginationWithInfo info =
  let
    startItem = (info.currentPage - 1) * info.pageSize + 1
    endItem = min (info.currentPage * info.pageSize) info.totalItems
  in
    E.div_
      [ E.class_ "flex flex-col sm:flex-row items-center justify-between gap-4" ]
      [ -- Info text
        E.div_
          [ E.class_ "text-sm text-muted-foreground" ]
          [ E.text ("Showing " <> show startItem <> "-" <> show endItem <> " of " <> show info.totalItems) ]
      , -- Controls row
        E.div_
          [ E.class_ "flex items-center gap-4" ]
          [ -- Page size selector
            pageSizeSelector info
          , -- Pagination
            pagination
              [ currentPage info.currentPage
              , totalPages info.totalPages
              , onPageChange info.onPageChange
              ]
          ]
      ]

-- | Page size selector
pageSizeSelector :: forall msg. PaginationInfo msg -> E.Element msg
pageSizeSelector info =
  E.div_
    [ E.class_ "flex items-center gap-2" ]
    [ E.span_
        [ E.class_ "text-sm text-muted-foreground" ]
        [ E.text "Per page:" ]
    , E.element "select"
        [ E.classes 
            [ "h-9 rounded-md border border-input bg-background px-3 py-1 text-sm"
            , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
            ]
        ]
        (map (renderPageSizeOption info.pageSize) info.pageSizeOptions)
    ]

renderPageSizeOption :: forall msg. Int -> Int -> E.Element msg
renderPageSizeOption current sizeVal =
  E.element "option"
    [ E.value (show sizeVal)
    , E.selected (sizeVal == current)
    ]
    [ E.text (show sizeVal) ]

-- | Individual pagination button
paginationButton :: forall msg. 
  { page :: Int
  , current :: Boolean
  , disabled :: Boolean
  , onClick :: Maybe msg
  } -> 
  Array (E.Element msg) -> 
  E.Element msg
paginationButton opts children =
  let
    baseClasses = 
      "inline-flex items-center justify-center rounded-md text-sm font-medium ring-offset-background transition-colors h-9 w-9"
    
    stateClasses =
      if opts.current
        then "bg-primary text-primary-foreground"
        else "hover:bg-accent hover:text-accent-foreground"
    
    disabledClasses =
      "disabled:pointer-events-none disabled:opacity-50"
    
    clickHandler = case opts.onClick of
      Just h -> [ E.onClick h ]
      Nothing -> []
  in
    E.button_
      ([ E.classes [ baseClasses, stateClasses, disabledClasses ]
      , E.disabled opts.disabled
      , E.attr "aria-current" (if opts.current then "page" else "false")
      ] <> clickHandler)
      children

-- | Pagination ellipsis
paginationEllipsis :: forall msg. E.Element msg
paginationEllipsis =
  E.span_
    [ E.class_ "flex h-9 w-9 items-center justify-center"
    , E.ariaHidden true
    ]
    [ E.text "…" ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // navigation btns
-- ═════════════════════════════════════════════════════════════════════════════

-- | Previous page button
prevButton :: forall msg. PaginationProps msg -> E.Element msg
prevButton props =
  let
    clickHandler = case props.onPageChange of
      Just handler -> [ E.onClick (handler (props.currentPage - 1)) ]
      Nothing -> []
  in
    E.button_
      ([ E.classes 
          [ "inline-flex items-center justify-center rounded-md text-sm font-medium"
          , "ring-offset-background transition-colors h-9 px-3"
          , "hover:bg-accent hover:text-accent-foreground"
          , "disabled:pointer-events-none disabled:opacity-50"
          ]
      , E.disabled (props.disabled || props.currentPage <= 1)
      , E.ariaLabel "Previous page"
      ] <> clickHandler)
      [ chevronLeftIcon
      , E.span_ [ E.class_ "sr-only sm:not-sr-only sm:ml-1" ] [ E.text "Prev" ]
      ]

-- | Next page button
nextButton :: forall msg. PaginationProps msg -> E.Element msg
nextButton props =
  let
    clickHandler = case props.onPageChange of
      Just handler -> [ E.onClick (handler (props.currentPage + 1)) ]
      Nothing -> []
  in
    E.button_
      ([ E.classes 
          [ "inline-flex items-center justify-center rounded-md text-sm font-medium"
          , "ring-offset-background transition-colors h-9 px-3"
          , "hover:bg-accent hover:text-accent-foreground"
          , "disabled:pointer-events-none disabled:opacity-50"
          ]
      , E.disabled (props.disabled || props.currentPage >= props.totalPages)
      , E.ariaLabel "Next page"
      ] <> clickHandler)
      [ E.span_ [ E.class_ "sr-only sm:not-sr-only sm:mr-1" ] [ E.text "Next" ]
      , chevronRightIcon
      ]

-- | First page button
firstButton :: forall msg. PaginationProps msg -> E.Element msg
firstButton props =
  let
    clickHandler = case props.onPageChange of
      Just handler -> [ E.onClick (handler 1) ]
      Nothing -> []
  in
    E.button_
      ([ E.classes 
          [ "inline-flex items-center justify-center rounded-md text-sm font-medium"
          , "ring-offset-background transition-colors h-9 w-9"
          , "hover:bg-accent hover:text-accent-foreground"
          , "disabled:pointer-events-none disabled:opacity-50"
          ]
      , E.disabled (props.disabled || props.currentPage <= 1)
      , E.ariaLabel "First page"
      ] <> clickHandler)
      [ chevronsLeftIcon ]

-- | Last page button
lastButton :: forall msg. PaginationProps msg -> E.Element msg
lastButton props =
  let
    clickHandler = case props.onPageChange of
      Just handler -> [ E.onClick (handler props.totalPages) ]
      Nothing -> []
  in
    E.button_
      ([ E.classes 
          [ "inline-flex items-center justify-center rounded-md text-sm font-medium"
          , "ring-offset-background transition-colors h-9 w-9"
          , "hover:bg-accent hover:text-accent-foreground"
          , "disabled:pointer-events-none disabled:opacity-50"
          ]
      , E.disabled (props.disabled || props.currentPage >= props.totalPages)
      , E.ariaLabel "Last page"
      ] <> clickHandler)
      [ chevronsRightIcon ]

-- | Render a page item (number or ellipsis)
renderPageItem :: forall msg. PaginationProps msg -> PageItem -> E.Element msg
renderPageItem props item = case item of
  Page n ->
    paginationButton
      { page: n
      , current: n == props.currentPage
      , disabled: props.disabled
      , onClick: case props.onPageChange of
          Just handler -> Just (handler n)
          Nothing -> Nothing
      }
      [ E.text (show n) ]
  Ellipsis ->
    paginationEllipsis

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

chevronLeftIcon :: forall msg. E.Element msg
chevronLeftIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.svgElement "polyline"
        [ E.attr "points" "15 18 9 12 15 6" ]
        []
    ]

chevronRightIcon :: forall msg. E.Element msg
chevronRightIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.svgElement "polyline"
        [ E.attr "points" "9 18 15 12 9 6" ]
        []
    ]

chevronsLeftIcon :: forall msg. E.Element msg
chevronsLeftIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.svgElement "polyline"
        [ E.attr "points" "11 17 6 12 11 7" ]
        []
    , E.svgElement "polyline"
        [ E.attr "points" "18 17 13 12 18 7" ]
        []
    ]

chevronsRightIcon :: forall msg. E.Element msg
chevronsRightIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.svgElement "polyline"
        [ E.attr "points" "13 17 18 12 13 7" ]
        []
    , E.svgElement "polyline"
        [ E.attr "points" "6 17 11 12 6 7" ]
        []
    ]
