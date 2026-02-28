-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // ui // avatar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Avatar Component — Pure Element Version
-- |
-- | User avatars with image or fallback initials.
module Hydrogen.UI.Avatar
  ( avatar
  , avatarImage
  , avatarFallback
  , AvatarSize(Sm, Md, Lg, Xl)
  , size
  , className
  ) where

import Prelude (class Eq, (<>))

import Data.Array (foldl)
import Hydrogen.Render.Element as E

data AvatarSize = Sm | Md | Lg | Xl

derive instance eqAvatarSize :: Eq AvatarSize

sizeClasses :: AvatarSize -> String
sizeClasses = case _ of
  Sm -> "h-8 w-8 text-xs"
  Md -> "h-10 w-10 text-sm"
  Lg -> "h-12 w-12 text-base"
  Xl -> "h-16 w-16 text-lg"

type AvatarConfig = { size :: AvatarSize, className :: String }
type ConfigMod = AvatarConfig -> AvatarConfig

defaultConfig :: AvatarConfig
defaultConfig = { size: Md, className: "" }

size :: AvatarSize -> ConfigMod
size s config = config { size = s }

className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

baseClasses :: String
baseClasses = "relative flex shrink-0 overflow-hidden rounded-full"

avatar :: forall msg. Array ConfigMod -> Array (E.Element msg) -> E.Element msg
avatar mods children =
  let 
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = baseClasses <> " " <> sizeClasses config.size <> " " <> config.className
  in
    E.div_ [ E.class_ allClasses ] children

avatarImage :: forall msg. String -> String -> E.Element msg
avatarImage src altText =
  E.img_ 
    [ E.class_ "aspect-square h-full w-full object-cover"
    , E.src src
    , E.alt altText
    ]

avatarFallback :: forall msg. String -> E.Element msg
avatarFallback initials =
  E.div_
    [ E.class_ "flex h-full w-full items-center justify-center rounded-full bg-muted font-medium" ]
    [ E.text initials ]
