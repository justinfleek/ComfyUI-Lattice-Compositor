-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // ui // skeleton
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Skeleton Component — Pure Element Version
-- |
-- | Loading placeholder skeletons.
module Hydrogen.UI.Skeleton
  ( skeleton
  , skeletonText
  , skeletonCircle
  , skeletonCard
  , className
  ) where

import Prelude ((<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

type SkeletonConfig = { className :: String }
type ConfigMod = SkeletonConfig -> SkeletonConfig

defaultConfig :: SkeletonConfig
defaultConfig = { className: "" }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

baseClasses :: String
baseClasses = "animate-pulse rounded-md bg-muted"

-- | Basic skeleton block
skeleton :: forall msg. Array ConfigMod -> E.Element msg
skeleton mods =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = baseClasses <> " " <> config.className
  in
    E.div_ [ E.class_ allClasses ] []

-- | Text line skeleton
skeletonText :: forall msg. String -> E.Element msg
skeletonText width =
  E.div_ [ E.class_ (baseClasses <> " h-4 " <> width) ] []

-- | Circular skeleton (for avatars)
skeletonCircle :: forall msg. String -> E.Element msg
skeletonCircle size =
  E.div_ [ E.class_ ("animate-pulse rounded-full bg-muted " <> size) ] []

-- | Card skeleton with multiple lines
skeletonCard :: forall msg. E.Element msg
skeletonCard =
  E.div_
    [ E.class_ "space-y-3" ]
    [ skeletonText "w-3/4"
    , skeletonText "w-full"
    , skeletonText "w-5/6"
    ]
