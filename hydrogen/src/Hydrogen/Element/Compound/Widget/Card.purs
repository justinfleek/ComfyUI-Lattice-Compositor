-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // widget // card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Widget Card — Standard KPI container with header, value, and chart area.
-- |
-- | ## Design Philosophy
-- |
-- | Based on COMPASS bento reference images, the standard widget layout is:
-- |
-- | ```
-- | ┌─────────────────────────────────────┐
-- | │ Category Label               [⋮]   │  <- 11px, muted, uppercase
-- | │ $32,134  +2.5%                      │  <- 28px bold + 13px trend
-- | │ Compared to $21,340 last month     │  <- 12px muted description
-- | │                                     │
-- | │ ┌─────────────────────────────┐    │
-- | │ │                             │    │
-- | │ │      CHART AREA             │    │  <- Any chart component
-- | │ │                             │    │
-- | │ └─────────────────────────────┘    │
-- | └─────────────────────────────────────┘
-- | ```
-- |
-- | The Card wraps any chart Element, providing consistent styling.

module Hydrogen.Element.Compound.Widget.Card
  ( -- * Widget Card
    widgetCard
  , WidgetCardData
  , TrendData
  , defaultCardData
  
  -- * Card Variants
  , kpiCard
  , chartCard
  , sparklineCard
  
  -- * Value Formatting
  , TrendDirection(..)
  , formatValue
  , formatPercent
  , formatCurrency
  ) where

import Prelude
  ( class Show
  , class Eq
  , show
  , (==)
  , (&&)
  , (<>)
  , (<)
  , (>)
  , (-)
  , (/)
  , (*)
  , negate
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Element.Compound.Widget.Theme 
  ( ThemeMode(..)
  , GlowIntensity(..)
  , containerBackground
  , textPrimary
  , textSecondary
  , textMuted
  , textGlow
  , neonGreen
  , neonRed
  )
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // widget card
-- ═════════════════════════════════════════════════════════════════════════════

-- | Widget card data.
type WidgetCardData =
  { title :: String                  -- ^ Category/metric name
  , value :: String                  -- ^ Primary value (formatted)
  , trend :: Maybe TrendData         -- ^ Optional trend indicator
  , description :: Maybe String      -- ^ Optional secondary description
  , themeMode :: ThemeMode           -- ^ Dark or light mode
  , className :: String              -- ^ Additional CSS classes
  }

-- | Trend data for value changes.
type TrendData =
  { percent :: Number
  , direction :: TrendDirection
  , comparison :: Maybe String       -- ^ e.g., "vs last month"
  }

-- | Trend direction.
data TrendDirection
  = TrendUp
  | TrendDown
  | TrendFlat

derive instance eqTrendDirection :: Eq TrendDirection

instance showTrendDirection :: Show TrendDirection where
  show TrendUp = "up"
  show TrendDown = "down"
  show TrendFlat = "flat"

-- | Default card data.
defaultCardData :: WidgetCardData
defaultCardData =
  { title: "Metric"
  , value: "0"
  , trend: Nothing
  , description: Nothing
  , themeMode: ModeDark
  , className: ""
  }

-- | Render a widget card with chart content.
-- |
-- | The card provides the container and header; you provide the chart Element.
widgetCard :: forall msg. WidgetCardData -> E.Element msg -> E.Element msg
widgetCard cardData chartElement =
  let
    bgColor = containerBackground cardData.themeMode
    primaryColor = textPrimary cardData.themeMode
    secondaryColor = textSecondary cardData.themeMode
    mutedColor = textMuted cardData.themeMode
  in
    E.div_
      [ E.class_ ("widget-card rounded-xl p-5 " <> cardData.className)
      , E.style "background" bgColor
      , E.style "box-shadow" "0 4px 12px rgba(0, 0, 0, 0.3)"
      ]
      [ -- Header section
        E.div_
          [ E.class_ "widget-card-header flex justify-between items-start mb-4" ]
          [ -- Title
            E.div_
              [ E.class_ "flex-1" ]
              [ E.span_
                  [ E.class_ "text-xs font-medium uppercase tracking-wider"
                  , E.style "color" mutedColor
                  ]
                  [ E.text cardData.title ]
              ]
          -- Menu dots (optional)
          , E.div_
              [ E.class_ "w-6 h-6 flex items-center justify-center cursor-pointer"
              , E.style "color" mutedColor
              ]
              [ E.text "⋮" ]
          ]
      
      -- Value section
      , E.div_
          [ E.class_ "widget-card-value mb-2" ]
          [ E.span_
              [ E.class_ "text-3xl font-bold"
              , E.style "color" primaryColor
              ]
              [ E.text cardData.value ]
          -- Trend indicator
          , renderTrend cardData.trend cardData.themeMode
          ]
      
      -- Description
      , renderDescription cardData.description mutedColor
      
      -- Chart area
      , E.div_
          [ E.class_ "widget-card-chart mt-4" ]
          [ chartElement ]
      ]

-- | Render trend indicator.
renderTrend :: forall msg. Maybe TrendData -> ThemeMode -> E.Element msg
renderTrend maybeTrend themeMode =
  case maybeTrend of
    Nothing -> E.text ""
    Just trend ->
      let
        color = case trend.direction of
          TrendUp -> neonGreen
          TrendDown -> neonRed
          TrendFlat -> textSecondary themeMode
        
        arrow = case trend.direction of
          TrendUp -> "↑"
          TrendDown -> "↓"
          TrendFlat -> "→"
        
        sign = case trend.direction of
          TrendUp -> "+"
          TrendDown -> ""
          TrendFlat -> ""
        
        glowStyle = textGlow color GlowSubtle
      in
        E.span_
          [ E.class_ "text-sm font-medium ml-2"
          , E.style "color" color
          , E.style "text-shadow" glowStyle
          ]
          [ E.text (arrow <> " " <> sign <> formatPercent trend.percent <> "%") ]

-- | Render description line.
renderDescription :: forall msg. Maybe String -> String -> E.Element msg
renderDescription maybeDesc color =
  case maybeDesc of
    Nothing -> E.text ""
    Just desc ->
      E.p_
        [ E.class_ "text-xs"
        , E.style "color" color
        ]
        [ E.text desc ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // card variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | KPI card without chart (just value and trend).
kpiCard :: forall msg. WidgetCardData -> E.Element msg
kpiCard cardData =
  widgetCard cardData (E.text "")

-- | Chart card with default styling.
chartCard :: forall msg. String -> String -> E.Element msg -> E.Element msg
chartCard title value chartElement =
  widgetCard
    { title: title
    , value: value
    , trend: Nothing
    , description: Nothing
    , themeMode: ModeDark
    , className: ""
    }
    chartElement

-- | Sparkline card (compact with inline chart).
sparklineCard :: forall msg. 
  String -> 
  String -> 
  Number -> 
  TrendDirection -> 
  E.Element msg -> 
  E.Element msg
sparklineCard title value trendPercent direction sparkElement =
  let
    cardData =
      { title: title
      , value: value
      , trend: Just
          { percent: trendPercent
          , direction: direction
          , comparison: Nothing
          }
      , description: Nothing
      , themeMode: ModeDark
      , className: "widget-card--sparkline"
      }
  in
    E.div_
      [ E.class_ "widget-card widget-card--sparkline rounded-lg p-4"
      , E.style "background" (containerBackground ModeDark)
      ]
      [ E.div_
          [ E.class_ "flex items-center justify-between" ]
          [ E.div_
              [ E.class_ "flex-1" ]
              [ E.span_
                  [ E.class_ "text-xs font-medium uppercase tracking-wider"
                  , E.style "color" (textMuted ModeDark)
                  ]
                  [ E.text title ]
              , E.div_
                  [ E.class_ "flex items-baseline gap-2 mt-1" ]
                  [ E.span_
                      [ E.class_ "text-xl font-bold"
                      , E.style "color" (textPrimary ModeDark)
                      ]
                      [ E.text value ]
                  , renderTrend (Just { percent: trendPercent, direction: direction, comparison: Nothing }) ModeDark
                  ]
              ]
          , E.div_
              [ E.class_ "w-24 h-12" ]
              [ sparkElement ]
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // value formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format a numeric value for display.
-- |
-- | Uses K/M/B suffixes for large numbers.
formatValue :: Number -> String
formatValue v
  | v > 999999999.0 = show (Math.floor (v / 100000000.0) / 10.0) <> "B"
  | v > 999999.0 = show (Math.floor (v / 100000.0) / 10.0) <> "M"
  | v > 999.0 = show (Math.floor (v / 100.0) / 10.0) <> "K"
  | v < 0.0 && v > (negate 1000.0) = show (Math.floor v)
  | v < (negate 999.0) = show (Math.floor (v / 100.0) / 10.0) <> "K"
  | v < (negate 999999.0) = show (Math.floor (v / 100000.0) / 10.0) <> "M"
  | true = show (Math.floor v)

-- | Format a percentage value.
formatPercent :: Number -> String
formatPercent p =
  let
    rounded = Math.floor (p * 10.0) / 10.0
  in
    show rounded

-- | Format a currency value.
formatCurrency :: String -> Number -> String
formatCurrency symbol v =
  symbol <> formatValue v
