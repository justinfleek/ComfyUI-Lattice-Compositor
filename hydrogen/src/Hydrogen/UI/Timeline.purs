-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // ui // timeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timeline Component — Pure Element Version
-- |
-- | Vertical timelines for activity feeds and histories.
module Hydrogen.UI.Timeline
  ( timeline
  , timelineItem
  , timelineDot
  , timelineContent
  , timelineTitle
  , timelineDescription
  , timelineTime
  , TimelineDotVariant(..)
  , dotVariant
  ) where

import Prelude (class Eq, (<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

data TimelineDotVariant = Default | Success | Warning | Danger | Info

derive instance eqTimelineDotVariant :: Eq TimelineDotVariant

dotVariantClasses :: TimelineDotVariant -> String
dotVariantClasses = case _ of
  Default -> "bg-border"
  Success -> "bg-green-500"
  Warning -> "bg-yellow-500"
  Danger -> "bg-red-500"
  Info -> "bg-blue-500"

type TimelineItemConfig = { dotVariant :: TimelineDotVariant }
type ConfigMod = TimelineItemConfig -> TimelineItemConfig

defaultConfig :: TimelineItemConfig
defaultConfig = { dotVariant: Default }

dotVariant :: TimelineDotVariant -> ConfigMod
dotVariant v config = config { dotVariant = v }

-- | Timeline container
timeline :: forall msg. Array (E.Element msg) -> E.Element msg
timeline children =
  E.div_ [ E.class_ "relative space-y-4 pl-6 before:absolute before:left-0 before:top-0 before:h-full before:w-px before:bg-border" ] children

-- | Timeline item wrapper
timelineItem :: forall msg. Array ConfigMod -> Array (E.Element msg) -> E.Element msg
timelineItem mods children =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    dotClasses = "absolute -left-[5px] h-2.5 w-2.5 rounded-full " <> dotVariantClasses config.dotVariant
  in
    E.div_ 
      [ E.class_ "relative" ]
      [ E.div_ [ E.class_ dotClasses ] []
      , E.div_ [ E.class_ "space-y-1" ] children
      ]

-- | Custom timeline dot
timelineDot :: forall msg. Array (E.Element msg) -> E.Element msg
timelineDot children =
  E.div_ 
    [ E.class_ "absolute -left-3 flex h-6 w-6 items-center justify-center rounded-full bg-background ring-2 ring-border" ] 
    children

-- | Timeline content wrapper
timelineContent :: forall msg. Array (E.Element msg) -> E.Element msg
timelineContent children =
  E.div_ [ E.class_ "space-y-1" ] children

-- | Timeline item title
timelineTitle :: forall msg. String -> E.Element msg
timelineTitle text =
  E.p_ [ E.class_ "text-sm font-medium leading-none" ] [ E.text text ]

-- | Timeline item description
timelineDescription :: forall msg. String -> E.Element msg
timelineDescription text =
  E.p_ [ E.class_ "text-sm text-muted-foreground" ] [ E.text text ]

-- | Timeline timestamp
timelineTime :: forall msg. String -> E.Element msg
timelineTime text =
  E.span_ [ E.class_ "text-xs text-muted-foreground" ] [ E.text text ]
