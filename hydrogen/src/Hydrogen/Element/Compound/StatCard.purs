-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // stat-card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen StatCard Component
-- |
-- | Display statistics and metrics with optional trend indicators.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.StatCard as StatCard
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic stat card
-- | StatCard.statCard []
-- |   { label: "Total Users"
-- |   , value: "12,345"
-- |   , trend: Nothing
-- |   , description: Nothing
-- |   }
-- |
-- | -- With trend indicator
-- | StatCard.statCard []
-- |   { label: "Revenue"
-- |   , value: "$54,321"
-- |   , trend: Just { value: 12.5, direction: StatCard.Up }
-- |   , description: Just "vs last month"
-- |   }
-- |
-- | -- With icon
-- | StatCard.statCardWithIcon []
-- |   { label: "Active Sessions"
-- |   , value: "1,234"
-- |   , icon: usersIcon
-- |   , trend: Nothing
-- |   }
-- |
-- | -- Stats grid
-- | StatCard.statGrid []
-- |   [ StatCard.statCard [] { label: "Users", value: "10k", trend: Nothing, description: Nothing }
-- |   , StatCard.statCard [] { label: "Revenue", value: "$50k", trend: Nothing, description: Nothing }
-- |   ]
-- | ```
module Hydrogen.Element.Compound.StatCard
  ( -- * StatCard Components
    statCard
  , statCardWithIcon
  , statGrid
  , miniStat
    -- * Types
  , StatCardConfig
  , StatTrend
  , TrendDirection(Up, Down, Neutral)
  , Size(Small, Medium, Large)
  , Variant(Default, Filled, Outlined, Ghost)
    -- * Props
  , StatCardProps
  , StatCardProp
  , StatGridProps
  , StatGridProp
  , defaultProps
  , defaultGridProps
    -- * Prop Builders
  , variant
  , size
  , bordered
  , hoverable
  , className
  , columns
  , gap
  ) where

import Prelude
  ( class Eq
  , show
  , (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Trend direction
data TrendDirection
  = Up
  | Down
  | Neutral

derive instance eqTrendDirection :: Eq TrendDirection

-- | Trend indicator
type StatTrend =
  { value :: Number
  , direction :: TrendDirection
  }

-- | StatCard configuration
type StatCardConfig msg =
  { label :: String
  , value :: String
  , trend :: Maybe StatTrend
  , description :: Maybe String
  , icon :: Maybe (E.Element msg)
  }

-- | Size variants
data Size
  = Small
  | Medium
  | Large

derive instance eqSize :: Eq Size

-- | Card variants
data Variant
  = Default
  | Filled
  | Outlined
  | Ghost

derive instance eqVariant :: Eq Variant

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | StatCard properties
type StatCardProps =
  { variant :: Variant
  , size :: Size
  , bordered :: Boolean
  , hoverable :: Boolean
  , className :: String
  }

-- | Property modifier
type StatCardProp = StatCardProps -> StatCardProps

-- | Default properties
defaultProps :: StatCardProps
defaultProps =
  { variant: Default
  , size: Medium
  , bordered: true
  , hoverable: false
  , className: ""
  }

-- | Grid properties
type StatGridProps =
  { columns :: Int
  , gap :: String
  , className :: String
  }

type StatGridProp = StatGridProps -> StatGridProps

defaultGridProps :: StatGridProps
defaultGridProps =
  { columns: 4
  , gap: "gap-4"
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set variant
variant :: Variant -> StatCardProp
variant v props = props { variant = v }

-- | Set size
size :: Size -> StatCardProp
size s props = props { size = s }

-- | Show border
bordered :: Boolean -> StatCardProp
bordered b props = props { bordered = b }

-- | Make hoverable
hoverable :: Boolean -> StatCardProp
hoverable h props = props { hoverable = h }

-- | Add custom class
className :: String -> StatCardProp
className c props = props { className = props.className <> " " <> c }

-- | Set columns
columns :: Int -> StatGridProp
columns c props = props { columns = c }

-- | Set gap
gap :: String -> StatGridProp
gap g props = props { gap = g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get variant classes
variantClasses :: Variant -> String
variantClasses = case _ of
  Default -> "bg-card text-card-foreground"
  Filled -> "bg-primary/10 text-foreground"
  Outlined -> "bg-transparent border-2"
  Ghost -> "bg-transparent"

-- | Get size classes
sizeClasses :: Size -> { container :: String, value :: String, label :: String }
sizeClasses = case _ of
  Small ->
    { container: "p-4"
    , value: "text-xl font-bold"
    , label: "text-xs text-muted-foreground"
    }
  Medium ->
    { container: "p-6"
    , value: "text-2xl font-bold"
    , label: "text-sm text-muted-foreground"
    }
  Large ->
    { container: "p-8"
    , value: "text-4xl font-bold"
    , label: "text-base text-muted-foreground"
    }

-- | Card base classes
cardBaseClasses :: String
cardBaseClasses =
  "rounded-lg"

-- | Trend classes based on direction
trendClasses :: TrendDirection -> String
trendClasses = case _ of
  Up -> "text-green-500"
  Down -> "text-red-500"
  Neutral -> "text-muted-foreground"

-- | Trend container classes
trendContainerClasses :: String
trendContainerClasses =
  "flex items-center text-sm"

-- | Description classes
descriptionClasses :: String
descriptionClasses =
  "text-xs text-muted-foreground mt-1"

-- | Icon container classes
iconContainerClasses :: String
iconContainerClasses =
  "flex items-center justify-center w-12 h-12 rounded-lg bg-primary/10 text-primary"

-- | Columns classes for grid
columnsClasses :: Int -> String
columnsClasses n = case n of
  1 -> "grid-cols-1"
  2 -> "grid-cols-1 sm:grid-cols-2"
  3 -> "grid-cols-1 sm:grid-cols-2 lg:grid-cols-3"
  4 -> "grid-cols-1 sm:grid-cols-2 lg:grid-cols-4"
  5 -> "grid-cols-2 sm:grid-cols-3 lg:grid-cols-5"
  6 -> "grid-cols-2 sm:grid-cols-3 lg:grid-cols-6"
  _ -> "grid-cols-1 sm:grid-cols-2 lg:grid-cols-4"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Trend indicator
-- |
-- | Displays an up/down trend with percentage value.
trendIndicator :: forall msg. StatTrend -> E.Element msg
trendIndicator trend =
  E.span_
    [ E.classes [ trendContainerClasses, trendClasses trend.direction ] ]
    [ case trend.direction of
        Up -> trendUpIcon
        Down -> trendDownIcon
        Neutral -> E.text ""
    , E.text (show trend.value <> "%")
    ]

-- | Basic stat card
-- |
-- | Displays a label, value, optional trend, and optional description.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
statCard :: forall msg. 
  Array StatCardProp -> 
  { label :: String, value :: String, trend :: Maybe StatTrend, description :: Maybe String } -> 
  E.Element msg
statCard propMods config =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    sizes = sizeClasses props.size
    
    cardCls = 
      cardBaseClasses 
      <> " " <> variantClasses props.variant
      <> " " <> sizes.container
      <> (if props.bordered then " border" else "")
      <> (if props.hoverable then " hover:shadow-md transition-shadow cursor-pointer" else "")
      <> " " <> props.className
  in
    E.div_
      [ E.class_ cardCls ]
      [ E.p_
          [ E.class_ sizes.label ]
          [ E.text config.label ]
      , E.div_
          [ E.class_ "flex items-baseline gap-2 mt-2" ]
          [ E.p_
              [ E.class_ sizes.value ]
              [ E.text config.value ]
          , case config.trend of
              Just t -> trendIndicator t
              Nothing -> E.text ""
          ]
      , case config.description of
          Just desc ->
            E.p_
              [ E.class_ descriptionClasses ]
              [ E.text desc ]
          Nothing -> E.text ""
      ]

-- | Stat card with icon
-- |
-- | Displays a stat card with an icon on the left.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
statCardWithIcon :: forall msg. 
  Array StatCardProp -> 
  { label :: String, value :: String, icon :: E.Element msg, trend :: Maybe StatTrend } -> 
  E.Element msg
statCardWithIcon propMods config =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    sizes = sizeClasses props.size
    
    cardCls = 
      cardBaseClasses 
      <> " " <> variantClasses props.variant
      <> " " <> sizes.container
      <> (if props.bordered then " border" else "")
      <> (if props.hoverable then " hover:shadow-md transition-shadow cursor-pointer" else "")
      <> " " <> props.className
  in
    E.div_
      [ E.classes [ cardCls, "flex items-start gap-4" ] ]
      [ E.div_
          [ E.class_ iconContainerClasses ]
          [ config.icon ]
      , E.div_
          [ E.class_ "flex-1" ]
          [ E.p_
              [ E.class_ sizes.label ]
              [ E.text config.label ]
          , E.div_
              [ E.class_ "flex items-baseline gap-2 mt-1" ]
              [ E.p_
                  [ E.class_ sizes.value ]
                  [ E.text config.value ]
              , case config.trend of
                  Just t -> trendIndicator t
                  Nothing -> E.text ""
              ]
          ]
      ]

-- | Mini stat (compact inline display)
-- |
-- | A compact inline stat display for dense layouts.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
miniStat :: forall msg. 
  { label :: String, value :: String } -> 
  E.Element msg
miniStat config =
  E.div_
    [ E.class_ "flex items-center gap-2" ]
    [ E.span_
        [ E.class_ "text-sm text-muted-foreground" ]
        [ E.text config.label ]
    , E.span_
        [ E.class_ "text-sm font-semibold" ]
        [ E.text config.value ]
    ]

-- | Stats grid container
-- |
-- | A responsive grid layout for multiple stat cards.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
statGrid :: forall msg. Array StatGridProp -> Array (E.Element msg) -> E.Element msg
statGrid propMods children =
  let
    props = foldl (\p f -> f p) defaultGridProps propMods
    gridCls = "grid " <> columnsClasses props.columns <> " " <> props.gap <> " " <> props.className
  in
    E.div_
      [ E.class_ gridCls ]
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Trend up icon
trendUpIcon :: forall msg. E.Element msg
trendUpIcon =
  E.svg_
    [ E.class_ "h-4 w-4"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.path_
        [ E.attr "stroke-linecap" "round"
        , E.attr "stroke-linejoin" "round"
        , E.attr "d" "M7 17l9.2-9.2M17 17V7H7"
        ]
    ]

-- | Trend down icon
trendDownIcon :: forall msg. E.Element msg
trendDownIcon =
  E.svg_
    [ E.class_ "h-4 w-4"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.path_
        [ E.attr "stroke-linecap" "round"
        , E.attr "stroke-linejoin" "round"
        , E.attr "d" "M17 7l-9.2 9.2M7 7v10h10"
        ]
    ]
