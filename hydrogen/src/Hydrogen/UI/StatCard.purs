-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // ui // stat-card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | StatCard Component — Pure Element Version
-- |
-- | Statistic display cards for dashboards.
module Hydrogen.UI.StatCard
  ( statCard
  , statCardWithTrend
  , TrendDirection(Up, Down, Neutral)
  , className
  ) where

import Prelude (class Eq, (<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

data TrendDirection = Up | Down | Neutral

derive instance eqTrendDirection :: Eq TrendDirection

trendClasses :: TrendDirection -> String
trendClasses = case _ of
  Up -> "text-green-600"
  Down -> "text-red-600"
  Neutral -> "text-muted-foreground"

trendIcon :: TrendDirection -> String
trendIcon = case _ of
  Up -> "↑"
  Down -> "↓"
  Neutral -> "→"

type StatCardConfig = { className :: String }
type ConfigMod = StatCardConfig -> StatCardConfig

defaultConfig :: StatCardConfig
defaultConfig = { className: "" }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

-- | Simple stat card
statCard :: forall msg. Array ConfigMod -> String -> String -> E.Element msg
statCard mods label value =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = "rounded-lg border bg-card p-6 text-card-foreground shadow-sm " <> config.className
  in
    E.div_ 
      [ E.class_ allClasses ]
      [ E.p_ 
          [ E.class_ "text-sm font-medium text-muted-foreground" ] 
          [ E.text label ]
      , E.p_ 
          [ E.class_ "text-2xl font-bold" ] 
          [ E.text value ]
      ]

-- | Stat card with trend indicator
statCardWithTrend :: forall msg. Array ConfigMod -> String -> String -> TrendDirection -> String -> E.Element msg
statCardWithTrend mods label value trend trendText =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = "rounded-lg border bg-card p-6 text-card-foreground shadow-sm " <> config.className
  in
    E.div_ 
      [ E.class_ allClasses ]
      [ E.p_ 
          [ E.class_ "text-sm font-medium text-muted-foreground" ] 
          [ E.text label ]
      , E.div_
          [ E.class_ "flex items-baseline gap-2" ]
          [ E.p_ 
              [ E.class_ "text-2xl font-bold" ] 
              [ E.text value ]
          , E.span_ 
              [ E.class_ ("text-sm font-medium " <> trendClasses trend) ]
              [ E.text (trendIcon trend <> " " <> trendText) ]
          ]
      ]
