-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // ui // separator
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Separator Component — Pure Element Version
-- |
-- | Visual dividers for content sections.
module Hydrogen.UI.Separator
  ( separator
  , Orientation(Horizontal, Vertical)
  , orientation
  , className
  ) where

import Prelude (class Eq, (<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

data Orientation = Horizontal | Vertical

derive instance eqOrientation :: Eq Orientation

orientationClasses :: Orientation -> String
orientationClasses = case _ of
  Horizontal -> "h-[1px] w-full"
  Vertical -> "h-full w-[1px]"

type SeparatorConfig = { orientation :: Orientation, className :: String }
type ConfigMod = SeparatorConfig -> SeparatorConfig

defaultConfig :: SeparatorConfig
defaultConfig = { orientation: Horizontal, className: "" }

orientation :: Orientation -> ConfigMod
orientation o config = config { orientation = o }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

baseClasses :: String
baseClasses = "shrink-0 bg-border"

separator :: forall msg. Array ConfigMod -> E.Element msg
separator mods =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = baseClasses <> " " <> orientationClasses config.orientation <> " " <> config.className
  in
    E.div_ 
      [ E.class_ allClasses
      , E.role "separator"
      ] 
      []
