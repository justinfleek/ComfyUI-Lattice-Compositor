-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // brand // token // radius
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Radius Token molecule.
-- |
-- | A RadiusToken binds a semantic name to a corner radius value.
-- | Radius tokens ensure consistent roundedness across UI components.
-- |
-- | ## Structure
-- |
-- | ```
-- | RadiusToken = TokenMeta + RadiusValue + RadiusStyle
-- | ```
-- |
-- | ## Standard Scale
-- |
-- | - `radius.none` = 0px (sharp corners)
-- | - `radius.sm` = 2px (subtle rounding)
-- | - `radius.md` = 4px (default)
-- | - `radius.lg` = 8px (prominent rounding)
-- | - `radius.xl` = 12px (very rounded)
-- | - `radius.2xl` = 16px (highly rounded)
-- | - `radius.full` = 9999px (pill/circle)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Corner radius is a key brand differentiator. Sharp corners feel
-- | technical, large radii feel friendly. Consistent radius tokens
-- | ensure brand personality is maintained across agent-generated UI.

module Hydrogen.Schema.Brand.Token.Radius
  ( -- * RadiusToken Type
    RadiusToken
  , mkRadiusToken
  , mkRadiusTokenPx
  
  -- * Accessors
  , radiusTokenName
  , radiusTokenDesc
  , radiusTokenValue
  , radiusTokenStyle
  , radiusTokenMeta
  
  -- * Radius Value
  , RadiusValue
  , mkRadiusValue
  , radiusValuePx
  , isCircular
  
  -- * Radius Style
  , RadiusStyle(..)
  , radiusStyleToString
  , radiusStyleFromString
  
  -- * Radius Scale
  , RadiusScale(..)
  , radiusScaleToString
  , radiusScaleFromString
  , radiusScaleToPx
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (>=)
  , (<)
  , (<>)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower, trim)

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(CategoryRadius)
  , TokenMeta
  , mkTokenMeta
  , mkTokenDesc
  , unTokenName
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // radius // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radius value in pixels.
-- |
-- | Non-negative corner radius. Values >= 9999 are treated as "full" (circular).
newtype RadiusValue = RadiusValue Number

derive instance eqRadiusValue :: Eq RadiusValue
derive instance ordRadiusValue :: Ord RadiusValue

instance showRadiusValue :: Show RadiusValue where
  show (RadiusValue n)
    | n >= 9999.0 = "full"
    | otherwise = show n <> "px"

-- | Create a radius value in pixels.
mkRadiusValue :: Number -> RadiusValue
mkRadiusValue n
  | n < 0.0 = RadiusValue 0.0
  | otherwise = RadiusValue n

-- | Get radius value in pixels.
radiusValuePx :: RadiusValue -> Number
radiusValuePx (RadiusValue n) = n

-- | Check if radius is circular (full/pill).
isCircular :: RadiusValue -> Boolean
isCircular (RadiusValue n) = n >= 9999.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // radius // style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual style of corners.
data RadiusStyle
  = StyleSharp      -- ^ No rounding (0px)
  | StyleSubtle     -- ^ Minimal rounding
  | StyleRounded    -- ^ Standard rounding
  | StylePill       -- ^ Fully rounded ends (buttons, badges)
  | StyleCircle     -- ^ Perfect circle (avatars, icons)
  | StyleSquircle   -- ^ Superellipse (iOS-style)

derive instance eqRadiusStyle :: Eq RadiusStyle
derive instance ordRadiusStyle :: Ord RadiusStyle

instance showRadiusStyle :: Show RadiusStyle where
  show = radiusStyleToString

-- | Convert style to string.
radiusStyleToString :: RadiusStyle -> String
radiusStyleToString = case _ of
  StyleSharp -> "sharp"
  StyleSubtle -> "subtle"
  StyleRounded -> "rounded"
  StylePill -> "pill"
  StyleCircle -> "circle"
  StyleSquircle -> "squircle"

-- | Parse style from string.
radiusStyleFromString :: String -> Maybe RadiusStyle
radiusStyleFromString s = case toLower (trim s) of
  "sharp" -> Just StyleSharp
  "none" -> Just StyleSharp
  "square" -> Just StyleSharp
  "subtle" -> Just StyleSubtle
  "soft" -> Just StyleSubtle
  "rounded" -> Just StyleRounded
  "default" -> Just StyleRounded
  "pill" -> Just StylePill
  "capsule" -> Just StylePill
  "circle" -> Just StyleCircle
  "circular" -> Just StyleCircle
  "round" -> Just StyleCircle
  "squircle" -> Just StyleSquircle
  "ios" -> Just StyleSquircle
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // radius // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named radius scale levels.
data RadiusScale
  = RadiusNone   -- ^ 0px
  | RadiusSm     -- ^ 2px
  | RadiusMd     -- ^ 4px
  | RadiusLg     -- ^ 8px
  | RadiusXl     -- ^ 12px
  | Radius2xl    -- ^ 16px
  | Radius3xl    -- ^ 24px
  | RadiusFull   -- ^ 9999px

derive instance eqRadiusScale :: Eq RadiusScale
derive instance ordRadiusScale :: Ord RadiusScale

instance showRadiusScale :: Show RadiusScale where
  show = radiusScaleToString

-- | Convert scale to string.
radiusScaleToString :: RadiusScale -> String
radiusScaleToString = case _ of
  RadiusNone -> "none"
  RadiusSm -> "sm"
  RadiusMd -> "md"
  RadiusLg -> "lg"
  RadiusXl -> "xl"
  Radius2xl -> "2xl"
  Radius3xl -> "3xl"
  RadiusFull -> "full"

-- | Parse scale from string.
radiusScaleFromString :: String -> Maybe RadiusScale
radiusScaleFromString s = case toLower (trim s) of
  "none" -> Just RadiusNone
  "0" -> Just RadiusNone
  "sm" -> Just RadiusSm
  "small" -> Just RadiusSm
  "md" -> Just RadiusMd
  "medium" -> Just RadiusMd
  "base" -> Just RadiusMd
  "lg" -> Just RadiusLg
  "large" -> Just RadiusLg
  "xl" -> Just RadiusXl
  "2xl" -> Just Radius2xl
  "3xl" -> Just Radius3xl
  "full" -> Just RadiusFull
  "pill" -> Just RadiusFull
  "circle" -> Just RadiusFull
  _ -> Nothing

-- | Get pixel value for scale.
radiusScaleToPx :: RadiusScale -> Number
radiusScaleToPx = case _ of
  RadiusNone -> 0.0
  RadiusSm -> 2.0
  RadiusMd -> 4.0
  RadiusLg -> 8.0
  RadiusXl -> 12.0
  Radius2xl -> 16.0
  Radius3xl -> 24.0
  RadiusFull -> 9999.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // radius // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radius design token.
-- |
-- | Binds a semantic name to a radius value with style metadata.
type RadiusToken =
  { meta :: TokenMeta
  , value :: RadiusValue
  , style :: RadiusStyle
  }

-- | Create a radius token with full metadata.
mkRadiusToken :: TokenName -> TokenDesc -> RadiusValue -> RadiusStyle -> RadiusToken
mkRadiusToken name desc value style =
  { meta: mkTokenMeta name desc CategoryRadius
  , value: value
  , style: style
  }

-- | Create a radius token from pixel value.
mkRadiusTokenPx :: TokenName -> Number -> RadiusStyle -> RadiusToken
mkRadiusTokenPx name px style =
  let
    desc = mkTokenDesc ("Radius token: " <> unTokenName name)
    value = mkRadiusValue px
  in
    { meta: mkTokenMeta name desc CategoryRadius
    , value: value
    , style: style
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the token name.
radiusTokenName :: RadiusToken -> TokenName
radiusTokenName t = t.meta.name

-- | Get the token description.
radiusTokenDesc :: RadiusToken -> TokenDesc
radiusTokenDesc t = t.meta.description

-- | Get the radius value.
radiusTokenValue :: RadiusToken -> RadiusValue
radiusTokenValue t = t.value

-- | Get the radius style.
radiusTokenStyle :: RadiusToken -> RadiusStyle
radiusTokenStyle t = t.style

-- | Get the full metadata.
radiusTokenMeta :: RadiusToken -> TokenMeta
radiusTokenMeta t = t.meta
