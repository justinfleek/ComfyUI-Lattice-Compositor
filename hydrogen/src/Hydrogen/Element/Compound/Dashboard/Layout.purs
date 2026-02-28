-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // component // dashboard // layout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dashboard Layout — Bento-box grid for arranging dashboard widgets.
-- |
-- | ## Design Philosophy
-- |
-- | A dashboard is a grid of widgets that adapts to available space.
-- | Each widget occupies a cell (or spans multiple cells) in the grid.
-- | The layout responds to container size using Schema breakpoints.

module Hydrogen.Element.Compound.Dashboard.Layout
  ( -- * Component
    dashboard
    
  -- * Widget Positioning
  , WidgetPosition
  , widgetPosition
  , cell
  , wideCell
  , tallCell
  , largeCell
  
  -- * Dashboard Widget
  , DashboardWidget
  , widget
  
  -- * Props
  , DashboardProps
  , DashboardProp
  , defaultProps
  , columns
  , gap
  , rowHeight
  , padding
  , className
  ) where

import Prelude
  ( (<>)
  , ($)
  , show
  )

import Data.Array (foldl, mapWithIndex)
import Data.Maybe (Maybe(Just))

import Hydrogen.Render.Element (Element)
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Spacing (SpacingValue)
import Hydrogen.Schema.Geometry.Spacing as Spacing
import Hydrogen.Schema.Reactive.Viewport (ResponsiveValue)
import Hydrogen.Schema.Reactive.Viewport as Viewport

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // widget position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Widget position in the dashboard grid.
-- |
-- | Uses 1-based grid coordinates for intuitive placement.
type WidgetPosition =
  { column :: Int       -- ^ Starting column (1-based)
  , row :: Int          -- ^ Starting row (1-based)
  , columnSpan :: Int   -- ^ Number of columns to span
  , rowSpan :: Int      -- ^ Number of rows to span
  }

-- | Create a widget position.
widgetPosition :: Int -> Int -> Int -> Int -> WidgetPosition
widgetPosition col row colSpan rowSpan =
  { column: col
  , row: row
  , columnSpan: colSpan
  , rowSpan: rowSpan
  }

-- | Single cell position.
cell :: Int -> Int -> WidgetPosition
cell col row = widgetPosition col row 1 1

-- | Wide widget (spans 2 columns).
wideCell :: Int -> Int -> WidgetPosition
wideCell col row = widgetPosition col row 2 1

-- | Tall widget (spans 2 rows).
tallCell :: Int -> Int -> WidgetPosition
tallCell col row = widgetPosition col row 1 2

-- | Large widget (spans 2x2).
largeCell :: Int -> Int -> WidgetPosition
largeCell col row = widgetPosition col row 2 2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // dashboard widget
-- ═════════════════════════════════════════════════════════════════════════════

-- | A widget with its position in the dashboard.
type DashboardWidget msg =
  { position :: WidgetPosition
  , element :: Element msg
  }

-- | Create a dashboard widget.
widget :: forall msg. WidgetPosition -> Element msg -> DashboardWidget msg
widget pos el = { position: pos, element: el }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // dashboard props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dashboard configuration.
type DashboardProps =
  { columns :: ResponsiveValue Int  -- ^ Number of columns at each breakpoint
  , gap :: SpacingValue             -- ^ Gap between widgets
  , rowHeight :: SpacingValue       -- ^ Base row height
  , padding :: SpacingValue         -- ^ Dashboard padding
  , className :: String
  }

-- | Property modifier.
type DashboardProp = DashboardProps -> DashboardProps

-- | Default dashboard configuration.
-- |
-- | - 1 column on mobile, 2 on tablet, 4 on desktop
-- | - 16px gap
-- | - 120px row height
defaultProps :: DashboardProps
defaultProps =
  { columns: Viewport.responsive
      { base: 1
      , sm: Just 2
      , md: Just 2
      , lg: Just 3
      , xl: Just 4
      , xxl: Just 4
      }
  , gap: Spacing.spacingMd
  , rowHeight: Spacing.spacingValue 120.0
  , padding: Spacing.spacingMd
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // prop setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set responsive column count.
columns :: ResponsiveValue Int -> DashboardProp
columns c props = props { columns = c }

-- | Set gap between widgets.
gap :: SpacingValue -> DashboardProp
gap g props = props { gap = g }

-- | Set base row height.
rowHeight :: SpacingValue -> DashboardProp
rowHeight h props = props { rowHeight = h }

-- | Set dashboard padding.
padding :: SpacingValue -> DashboardProp
padding p props = props { padding = p }

-- | Add custom CSS class.
className :: String -> DashboardProp
className c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dashboard grid layout.
-- |
-- | Arranges widgets in a responsive bento-box grid.
-- | Widgets can span multiple columns and rows.
dashboard :: forall msg. Array DashboardProp -> Array (DashboardWidget msg) -> Element msg
dashboard propMods widgets =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.div_
      [ E.class_ $ "dashboard-grid " <> props.className
      , E.style "display" "grid"
      , E.style "grid-template-columns" (responsiveColumns props.columns)
      , E.style "gap" (Spacing.toLegacyCss props.gap)
      , E.style "padding" (Spacing.toLegacyCss props.padding)
      , E.style "grid-auto-rows" (Spacing.toLegacyCss props.rowHeight)
      , E.dataAttr "dashboard" "true"
      ]
      (mapWithIndex (renderWidget) widgets)

-- | Render a single widget in the grid.
renderWidget :: forall msg. Int -> DashboardWidget msg -> Element msg
renderWidget idx w =
  E.div_
    [ E.class_ "dashboard-widget"
    , E.style "grid-column" (gridSpan w.position.column w.position.columnSpan)
    , E.style "grid-row" (gridSpan w.position.row w.position.rowSpan)
    , E.dataAttr "widget-index" (show idx)
    ]
    [ w.element ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // css helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate grid span CSS value.
-- |
-- | `gridSpan 2 3` -> "2 / span 3"
gridSpan :: Int -> Int -> String
gridSpan start span' = show start <> " / span " <> show span'

-- | Generate responsive columns CSS.
-- |
-- | Uses CSS custom properties or generates a fixed value for base.
responsiveColumns :: ResponsiveValue Int -> String
responsiveColumns rv = "repeat(" <> show rv.xs <> ", 1fr)"
