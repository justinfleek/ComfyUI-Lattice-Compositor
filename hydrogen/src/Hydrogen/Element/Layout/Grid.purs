-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // layout // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grid Layout — Pure Element CSS Grid primitives with responsive support.
-- |
-- | ## Design Philosophy
-- |
-- | CSS Grid is the foundation for complex layouts. This module provides
-- | type-safe, responsive grid primitives that integrate with the Viewport
-- | schema atoms.
-- |
-- | Unlike Tailwind string-based classes, this uses proper typed values:
-- | - `ResponsiveValue Int` for column counts
-- | - `Spacing` atoms for gaps
-- | - Strongly-typed grid item positioning
-- |
-- | ## Frame.io-Level Responsiveness
-- |
-- | Grids respond to **viewport** AND **container** size:
-- |
-- | ```purescript
-- | -- Viewport-responsive grid (responds to window size)
-- | grid
-- |   [ columns (responsive { base: 1, sm: Just 2, lg: Just 4, ... })
-- |   , gap (Spacing.px 16)
-- |   ]
-- |   children
-- |
-- | -- Container-responsive grid (responds to parent size)
-- | containerGrid "dashboard-panel"
-- |   [ columns (containerResponsive { base: 1, lg: Just 3, ... })
-- |   ]
-- |   children
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Layout.Grid as Grid
-- |
-- | -- Simple grid with fixed columns
-- | Grid.grid [ Grid.cols 3, Grid.gap (Spacing.px 16) ]
-- |   [ item1, item2, item3 ]
-- |
-- | -- Responsive grid
-- | Grid.grid
-- |   [ Grid.columns (Grid.responsive { base: 1, sm: Just 2, lg: Just 4 })
-- |   , Grid.gap (Spacing.px 24)
-- |   ]
-- |   items
-- |
-- | -- Grid item with span
-- | Grid.gridItem [ Grid.colSpan 2, Grid.rowSpan 1 ]
-- |   [ content ]
-- | ```

module Hydrogen.Element.Layout.Grid
  ( -- * Grid Components
    grid
  , gridItem
  , containerGrid
  
  -- * Types
  , GridProps
  , GridProp
  , GridItemProps
  , GridItemProp
  
  -- * Column Props
  , cols
  , columns
  , rows
  , rowCount
  
  -- * Gap Props
  , gap
  , gapX
  , gapY
  , gapSpacing
  , gapXSpacing
  , gapYSpacing
  
  -- * Alignment Props
  , alignItems
  , justifyItems
  , alignContent
  , justifyContent
  , placeItems
  , placeContent
  
  -- * Grid Item Position Props
  , colSpan
  , colStart
  , colEnd
  , rowSpan
  , rowStart
  , rowEnd
  , area
  
  -- * Grid Item Alignment
  , alignSelf
  , justifySelf
  , placeSelf
  
  -- * Styling Props
  , padding
  , bgColor
  , className
  
  -- * Alignment Types
  , GridAlignment(AlignStart, AlignCenter, AlignEnd, AlignStretch)
  , GridJustify(JustifyStart, JustifyCenter, JustifyEnd, JustifyStretch, SpaceBetween, SpaceAround, SpaceEvenly)
  
  -- * Responsive Helpers
  , responsive
  , static
  , containerResponsive
  , containerStatic
  
  -- * Default Props
  , defaultGridProps
  , defaultGridItemProps
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (==)
  , ($)
  )

import Data.Array (foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Spacing (SpacingValue)
import Hydrogen.Schema.Geometry.Spacing as Spacing
import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Reactive.Viewport 
  ( Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl)
  , ResponsiveSpec
  , ResponsiveValue
  , breakpointClass
  )
import Hydrogen.Schema.Reactive.Viewport as Viewport
import Hydrogen.Schema.Reactive.ContainerQuery
  ( ContainerResponsiveSpec
  , ContainerResponsive
  )
import Hydrogen.Schema.Reactive.ContainerQuery as CQ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // alignment types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid alignment for items within their cells.
data GridAlignment
  = AlignStart    -- ^ Align to start of cell
  | AlignCenter   -- ^ Center within cell
  | AlignEnd      -- ^ Align to end of cell
  | AlignStretch  -- ^ Stretch to fill cell (default)

derive instance eqGridAlignment :: Eq GridAlignment

instance showGridAlignment :: Show GridAlignment where
  show AlignStart = "start"
  show AlignCenter = "center"
  show AlignEnd = "end"
  show AlignStretch = "stretch"

-- | Convert alignment to CSS value.
alignmentToCss :: GridAlignment -> String
alignmentToCss = show

-- | Grid justification for distributing content.
data GridJustify
  = JustifyStart     -- ^ Pack items to start
  | JustifyCenter    -- ^ Center items
  | JustifyEnd       -- ^ Pack items to end
  | JustifyStretch   -- ^ Stretch items to fill
  | SpaceBetween     -- ^ Even space between items
  | SpaceAround      -- ^ Even space around items
  | SpaceEvenly      -- ^ Even space between and around

derive instance eqGridJustify :: Eq GridJustify

instance showGridJustify :: Show GridJustify where
  show JustifyStart = "start"
  show JustifyCenter = "center"
  show JustifyEnd = "end"
  show JustifyStretch = "stretch"
  show SpaceBetween = "space-between"
  show SpaceAround = "space-around"
  show SpaceEvenly = "space-evenly"

-- | Convert justification to CSS value.
justifyToCss :: GridJustify -> String
justifyToCss = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // grid props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid container properties.
type GridProps =
  { -- Column/Row configuration
    columns :: Maybe (ResponsiveValue Int)
  , colsStatic :: Maybe Int
  , rowsVal :: Maybe (ResponsiveValue Int)
  , rowsStatic :: Maybe Int
  
  -- Gap configuration
  , gapVal :: Maybe SpacingValue
  , gapXVal :: Maybe SpacingValue
  , gapYVal :: Maybe SpacingValue
  
  -- Alignment
  , alignItemsVal :: Maybe GridAlignment
  , justifyItemsVal :: Maybe GridJustify
  , alignContentVal :: Maybe GridAlignment
  , justifyContentVal :: Maybe GridJustify
  
  -- Styling
  , paddingVal :: Maybe SpacingValue
  , bgColorVal :: Maybe RGB
  , classNameVal :: String
  
  -- Container query mode
  , containerName :: Maybe String
  , containerColumns :: Maybe (ContainerResponsive Int)
  }

-- | Grid property modifier.
type GridProp = GridProps -> GridProps

-- | Default grid props.
defaultGridProps :: GridProps
defaultGridProps =
  { columns: Nothing
  , colsStatic: Nothing
  , rowsVal: Nothing
  , rowsStatic: Nothing
  , gapVal: Nothing
  , gapXVal: Nothing
  , gapYVal: Nothing
  , alignItemsVal: Nothing
  , justifyItemsVal: Nothing
  , alignContentVal: Nothing
  , justifyContentVal: Nothing
  , paddingVal: Nothing
  , bgColorVal: Nothing
  , classNameVal: ""
  , containerName: Nothing
  , containerColumns: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // grid prop setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set static column count.
cols :: Int -> GridProp
cols n props = props { colsStatic = Just n }

-- | Set responsive column count.
columns :: ResponsiveValue Int -> GridProp
columns rv props = props { columns = Just rv }

-- | Set static row count.
rows :: Int -> GridProp
rows n props = props { rowsStatic = Just n }

-- | Set responsive row count.
rowCount :: ResponsiveValue Int -> GridProp
rowCount rv props = props { rowsVal = Just rv }

-- | Set gap as integer (pixel value).
gap :: Int -> GridProp
gap n props = props { gapVal = Just (Spacing.spacingValue (toNumber n)) }

-- | Set horizontal gap.
gapX :: Int -> GridProp
gapX n props = props { gapXVal = Just (Spacing.spacingValue (toNumber n)) }

-- | Set vertical gap.
gapY :: Int -> GridProp
gapY n props = props { gapYVal = Just (Spacing.spacingValue (toNumber n)) }

-- | Set gap with Spacing atom.
gapSpacing :: SpacingValue -> GridProp
gapSpacing s props = props { gapVal = Just s }

-- | Set horizontal gap with Spacing atom.
gapXSpacing :: SpacingValue -> GridProp
gapXSpacing s props = props { gapXVal = Just s }

-- | Set vertical gap with Spacing atom.
gapYSpacing :: SpacingValue -> GridProp
gapYSpacing s props = props { gapYVal = Just s }

-- | Set align-items.
alignItems :: GridAlignment -> GridProp
alignItems a props = props { alignItemsVal = Just a }

-- | Set justify-items.
justifyItems :: GridJustify -> GridProp
justifyItems j props = props { justifyItemsVal = Just j }

-- | Set align-content.
alignContent :: GridAlignment -> GridProp
alignContent a props = props { alignContentVal = Just a }

-- | Set justify-content.
justifyContent :: GridJustify -> GridProp
justifyContent j props = props { justifyContentVal = Just j }

-- | Set place-items (align + justify).
placeItems :: GridAlignment -> GridJustify -> GridProp
placeItems a j props = props 
  { alignItemsVal = Just a
  , justifyItemsVal = Just j 
  }

-- | Set place-content (align + justify content).
placeContent :: GridAlignment -> GridJustify -> GridProp
placeContent a j props = props
  { alignContentVal = Just a
  , justifyContentVal = Just j
  }

-- | Set padding.
padding :: SpacingValue -> GridProp
padding s props = props { paddingVal = Just s }

-- | Set background color.
bgColor :: RGB -> GridProp
bgColor c props = props { bgColorVal = Just c }

-- | Add custom CSS class.
className :: String -> GridProp
className c props = props { classNameVal = props.classNameVal <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // grid item props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid item properties.
type GridItemProps =
  { colSpanVal :: Maybe Int
  , colStartVal :: Maybe Int
  , colEndVal :: Maybe Int
  , rowSpanVal :: Maybe Int
  , rowStartVal :: Maybe Int
  , rowEndVal :: Maybe Int
  , areaVal :: Maybe String
  , alignSelfVal :: Maybe GridAlignment
  , justifySelfVal :: Maybe GridJustify
  , classNameVal :: String
  }

-- | Grid item property modifier.
type GridItemProp = GridItemProps -> GridItemProps

-- | Default grid item props.
defaultGridItemProps :: GridItemProps
defaultGridItemProps =
  { colSpanVal: Nothing
  , colStartVal: Nothing
  , colEndVal: Nothing
  , rowSpanVal: Nothing
  , rowStartVal: Nothing
  , rowEndVal: Nothing
  , areaVal: Nothing
  , alignSelfVal: Nothing
  , justifySelfVal: Nothing
  , classNameVal: ""
  }

-- | Set column span.
colSpan :: Int -> GridItemProp
colSpan n props = props { colSpanVal = Just n }

-- | Set column start.
colStart :: Int -> GridItemProp
colStart n props = props { colStartVal = Just n }

-- | Set column end.
colEnd :: Int -> GridItemProp
colEnd n props = props { colEndVal = Just n }

-- | Set row span.
rowSpan :: Int -> GridItemProp
rowSpan n props = props { rowSpanVal = Just n }

-- | Set row start.
rowStart :: Int -> GridItemProp
rowStart n props = props { rowStartVal = Just n }

-- | Set row end.
rowEnd :: Int -> GridItemProp
rowEnd n props = props { rowEndVal = Just n }

-- | Set grid area name.
area :: String -> GridItemProp
area a props = props { areaVal = Just a }

-- | Set align-self for item.
alignSelf :: GridAlignment -> GridItemProp
alignSelf a props = props { alignSelfVal = Just a }

-- | Set justify-self for item.
justifySelf :: GridJustify -> GridItemProp
justifySelf j props = props { justifySelfVal = Just j }

-- | Set place-self for item.
placeSelf :: GridAlignment -> GridJustify -> GridItemProp
placeSelf a j props = props
  { alignSelfVal = Just a
  , justifySelfVal = Just j
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // responsive helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create responsive value from spec.
-- |
-- | ```purescript
-- | columns (responsive { base: 1, sm: Just 2, lg: Just 4, xl: Nothing, xxl: Nothing })
-- | ```
responsive :: forall a. ResponsiveSpec a -> ResponsiveValue a
responsive = Viewport.responsive

-- | Create static responsive value.
static :: forall a. a -> ResponsiveValue a
static = Viewport.static

-- | Create container-responsive value.
containerResponsive :: forall a. ContainerResponsiveSpec a -> ContainerResponsive a
containerResponsive = CQ.containerResponsive

-- | Create static container-responsive value.
containerStatic :: forall a. a -> ContainerResponsive a
containerStatic = CQ.containerStatic

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // grid component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid container component.
-- |
-- | Creates a CSS Grid container with optional responsive column configuration.
grid :: forall msg. Array GridProp -> Array (E.Element msg) -> E.Element msg
grid propMods children =
  let
    props = foldl (\p f -> f p) defaultGridProps propMods
    attrs = buildGridAttributes props
  in
    E.div_ attrs children

-- | Grid with container queries.
-- |
-- | Creates a grid that responds to its container size, not viewport.
-- | Requires a container name for CSS container query targeting.
containerGrid :: forall msg. String -> Array GridProp -> Array (E.Element msg) -> E.Element msg
containerGrid name propMods children =
  let
    props = (foldl (\p f -> f p) defaultGridProps propMods) { containerName = Just name }
    attrs = buildContainerGridAttributes props
  in
    E.div_ attrs children

-- | Grid item component.
-- |
-- | Positions a child within the grid.
gridItem :: forall msg. Array GridItemProp -> Array (E.Element msg) -> E.Element msg
gridItem propMods children =
  let
    props = foldl (\p f -> f p) defaultGridItemProps propMods
    attrs = buildGridItemAttributes props
  in
    E.div_ attrs children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // attribute builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build grid container attributes.
buildGridAttributes :: forall msg. GridProps -> Array (E.Attribute msg)
buildGridAttributes props =
  [ E.style "display" "grid" ]
  <> buildColumnStyles props
  <> buildRowStyles props
  <> buildGapStyles props
  <> buildAlignmentStyles props
  <> buildPaddingStyles props
  <> buildBgColorStyles props
  <> buildClassNameAttr props.classNameVal

-- | Build container grid attributes (with container-type).
buildContainerGridAttributes :: forall msg. GridProps -> Array (E.Attribute msg)
buildContainerGridAttributes props =
  [ E.style "display" "grid"
  , E.style "container-type" "inline-size"
  ]
  <> case props.containerName of
       Nothing -> []
       Just name -> [ E.style "container-name" name ]
  <> buildColumnStyles props
  <> buildRowStyles props
  <> buildGapStyles props
  <> buildAlignmentStyles props
  <> buildPaddingStyles props
  <> buildBgColorStyles props
  <> buildClassNameAttr props.classNameVal

-- | Build column styles.
buildColumnStyles :: forall msg. GridProps -> Array (E.Attribute msg)
buildColumnStyles props = case props.colsStatic of
  Just n -> [ E.style "grid-template-columns" (repeatCols n) ]
  Nothing -> case props.columns of
    Nothing -> []
    Just rv -> buildResponsiveColumnClasses rv

-- | Build row styles.
buildRowStyles :: forall msg. GridProps -> Array (E.Attribute msg)
buildRowStyles props = case props.rowsStatic of
  Just n -> [ E.style "grid-template-rows" (repeatRows n) ]
  Nothing -> case props.rowsVal of
    Nothing -> []
    Just rv -> buildResponsiveRowClasses rv

-- | Build gap styles.
buildGapStyles :: forall msg. GridProps -> Array (E.Attribute msg)
buildGapStyles props =
  case props.gapVal of
    Just g -> [ E.style "gap" (Spacing.toLegacyCss g) ]
    Nothing ->
      case props.gapXVal of
        Just gx -> [ E.style "column-gap" (Spacing.toLegacyCss gx) ]
        Nothing -> []
      <>
      case props.gapYVal of
        Just gy -> [ E.style "row-gap" (Spacing.toLegacyCss gy) ]
        Nothing -> []

-- | Build alignment styles.
buildAlignmentStyles :: forall msg. GridProps -> Array (E.Attribute msg)
buildAlignmentStyles props =
  maybeStyle "align-items" alignmentToCss props.alignItemsVal
  <> maybeStyle "justify-items" justifyToCss props.justifyItemsVal
  <> maybeStyle "align-content" alignmentToCss props.alignContentVal
  <> maybeStyle "justify-content" justifyToCss props.justifyContentVal

-- | Build padding styles.
buildPaddingStyles :: forall msg. GridProps -> Array (E.Attribute msg)
buildPaddingStyles props = case props.paddingVal of
  Nothing -> []
  Just p -> [ E.style "padding" (Spacing.toLegacyCss p) ]

-- | Build background color styles.
buildBgColorStyles :: forall msg. GridProps -> Array (E.Attribute msg)
buildBgColorStyles props = case props.bgColorVal of
  Nothing -> []
  Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]

-- | Build className attribute.
buildClassNameAttr :: forall msg. String -> Array (E.Attribute msg)
buildClassNameAttr "" = []
buildClassNameAttr cls = [ E.class_ cls ]

-- | Build grid item attributes.
buildGridItemAttributes :: forall msg. GridItemProps -> Array (E.Attribute msg)
buildGridItemAttributes props =
  maybeStyleInt "grid-column" spanToCss props.colSpanVal
  <> maybeStyleInt "grid-column-start" show props.colStartVal
  <> maybeStyleInt "grid-column-end" show props.colEndVal
  <> maybeStyleInt "grid-row" spanToCss props.rowSpanVal
  <> maybeStyleInt "grid-row-start" show props.rowStartVal
  <> maybeStyleInt "grid-row-end" show props.rowEndVal
  <> case props.areaVal of
       Nothing -> []
       Just a -> [ E.style "grid-area" a ]
  <> maybeStyle "align-self" alignmentToCss props.alignSelfVal
  <> maybeStyle "justify-self" justifyToCss props.justifySelfVal
  <> buildClassNameAttr props.classNameVal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate repeat() for columns.
repeatCols :: Int -> String
repeatCols n = "repeat(" <> show n <> ", minmax(0, 1fr))"

-- | Generate repeat() for rows.
repeatRows :: Int -> String
repeatRows n = "repeat(" <> show n <> ", minmax(0, 1fr))"

-- | Convert span to CSS grid-column/grid-row value.
spanToCss :: Int -> String
spanToCss n = "span " <> show n

-- | Build responsive column classes (using CSS classes for breakpoints).
-- |
-- | Since Element uses inline styles, we generate Tailwind-compatible classes
-- | for responsive behavior. The runtime CSS must include these.
buildResponsiveColumnClasses :: forall msg. ResponsiveValue Int -> Array (E.Attribute msg)
buildResponsiveColumnClasses rv =
  [ E.class_ (buildResponsiveGridColsClass rv) ]

-- | Build responsive row classes.
buildResponsiveRowClasses :: forall msg. ResponsiveValue Int -> Array (E.Attribute msg)
buildResponsiveRowClasses rv =
  [ E.class_ (buildResponsiveGridRowsClass rv) ]

-- | Build Tailwind-style responsive grid-cols classes.
buildResponsiveGridColsClass :: ResponsiveValue Int -> String
buildResponsiveGridColsClass rv =
  "grid-cols-" <> show rv.xs
  <> maybeBreakpointClass Sm "grid-cols-" rv.xs rv.sm
  <> maybeBreakpointClass Md "grid-cols-" rv.sm rv.md
  <> maybeBreakpointClass Lg "grid-cols-" rv.md rv.lg
  <> maybeBreakpointClass Xl "grid-cols-" rv.lg rv.xl
  <> maybeBreakpointClass Xxl "grid-cols-" rv.xl rv.xxl

-- | Build Tailwind-style responsive grid-rows classes.
buildResponsiveGridRowsClass :: ResponsiveValue Int -> String
buildResponsiveGridRowsClass rv =
  "grid-rows-" <> show rv.xs
  <> maybeBreakpointClass Sm "grid-rows-" rv.xs rv.sm
  <> maybeBreakpointClass Md "grid-rows-" rv.sm rv.md
  <> maybeBreakpointClass Lg "grid-rows-" rv.md rv.lg
  <> maybeBreakpointClass Xl "grid-rows-" rv.lg rv.xl
  <> maybeBreakpointClass Xxl "grid-rows-" rv.xl rv.xxl

-- | Add breakpoint class only if value changes.
maybeBreakpointClass :: Breakpoint -> String -> Int -> Int -> String
maybeBreakpointClass bp prefix prev curr
  | prev == curr = ""
  | otherwise = " " <> breakpointClass bp (prefix <> show curr)

-- | Build optional style from Maybe.
maybeStyle :: forall msg a. String -> (a -> String) -> Maybe a -> Array (E.Attribute msg)
maybeStyle _ _ Nothing = []
maybeStyle prop toStr (Just a) = [ E.style prop (toStr a) ]

-- | Build optional style from Maybe Int.
maybeStyleInt :: forall msg. String -> (Int -> String) -> Maybe Int -> Array (E.Attribute msg)
maybeStyleInt _ _ Nothing = []
maybeStyleInt prop toStr (Just n) = [ E.style prop (toStr n) ]
