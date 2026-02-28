-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // brand // token // type
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Typography Token molecule.
-- |
-- | A TypeToken binds a semantic name to a typography style definition.
-- | Typography tokens define consistent text styles across the design system.
-- |
-- | ## Structure
-- |
-- | ```
-- | TypeToken = TokenMeta + TypeStyle
-- | ```
-- |
-- | ## Type Scale
-- |
-- | Standard semantic names for typography:
-- | - `type.display` — Large hero text
-- | - `type.h1` through `type.h6` — Heading hierarchy
-- | - `type.body.lg` / `type.body.md` / `type.body.sm` — Body text
-- | - `type.caption` — Small supporting text
-- | - `type.overline` — Label/category text
-- | - `type.code` — Monospace code text
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Typography creates visual hierarchy. When agents use semantic
-- | type tokens, the reading experience remains consistent across
-- | all generated content.

module Hydrogen.Schema.Brand.Token.Type
  ( -- * TypeToken Type
    TypeToken
  , mkTypeToken
  , mkTypeTokenSimple
  
  -- * Accessors
  , typeTokenName
  , typeTokenDesc
  , typeTokenStyle
  , typeTokenRole
  , typeTokenMeta
  
  -- * Type Style Value
  , TypeStyle
  , mkTypeStyle
  , typeStyleFamily
  , typeStyleSize
  , typeStyleWeight
  , typeStyleLineHeight
  , typeStyleLetterSpacing
  
  -- * Type Role
  , TypeRole(..)
  , typeRoleToString
  , typeRoleFromString
  , allTypeRoles
  
  -- * Font Family
  , FontFamily
  , mkFontFamily
  , unFontFamily
  , systemSans
  , systemSerif
  , systemMono
  
  -- * Font Weight
  , FontWeight
  , mkFontWeight
  , fontWeightValue
  , weightThin
  , weightLight
  , weightRegular
  , weightMedium
  , weightSemibold
  , weightBold
  , weightBlack
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (>=)
  , (<=)
  , (<<<)
  , (/)
  , (*)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower, trim)

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(CategoryType)
  , TokenMeta
  , mkTokenMeta
  , mkTokenDesc
  , unTokenName
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // font // family
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font family name (single family or stack).
newtype FontFamily = FontFamily String

derive instance eqFontFamily :: Eq FontFamily
derive instance ordFontFamily :: Ord FontFamily

instance showFontFamily :: Show FontFamily where
  show (FontFamily f) = show f

-- | Create a font family.
mkFontFamily :: String -> FontFamily
mkFontFamily = FontFamily <<< trim

-- | Extract the family name.
unFontFamily :: FontFamily -> String
unFontFamily (FontFamily f) = f

-- | System sans-serif stack.
systemSans :: FontFamily
systemSans = FontFamily "system-ui, -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif"

-- | System serif stack.
systemSerif :: FontFamily
systemSerif = FontFamily "Georgia, 'Times New Roman', Times, serif"

-- | System monospace stack.
systemMono :: FontFamily
systemMono = FontFamily "ui-monospace, SFMono-Regular, 'SF Mono', Menlo, Consolas, monospace"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // font // weight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font weight (100-900).
newtype FontWeight = FontWeight Int

derive instance eqFontWeight :: Eq FontWeight
derive instance ordFontWeight :: Ord FontWeight

instance showFontWeight :: Show FontWeight where
  show (FontWeight w) = show w

-- | Create a font weight (clamped to 100-900).
mkFontWeight :: Int -> FontWeight
mkFontWeight w
  | w <= 100 = FontWeight 100
  | w >= 900 = FontWeight 900
  | otherwise = FontWeight (roundToHundred w)
  where
  roundToHundred :: Int -> Int
  roundToHundred n = (n / 100) * 100

-- | Get the numeric weight value.
fontWeightValue :: FontWeight -> Int
fontWeightValue (FontWeight w) = w

-- | Thin (100)
weightThin :: FontWeight
weightThin = FontWeight 100

-- | Light (300)
weightLight :: FontWeight
weightLight = FontWeight 300

-- | Regular (400)
weightRegular :: FontWeight
weightRegular = FontWeight 400

-- | Medium (500)
weightMedium :: FontWeight
weightMedium = FontWeight 500

-- | Semibold (600)
weightSemibold :: FontWeight
weightSemibold = FontWeight 600

-- | Bold (700)
weightBold :: FontWeight
weightBold = FontWeight 700

-- | Black (900)
weightBlack :: FontWeight
weightBlack = FontWeight 900

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // type // style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete typography style definition.
type TypeStyle =
  { family :: FontFamily         -- ^ Font family/stack
  , size :: Number               -- ^ Font size in pixels
  , weight :: FontWeight         -- ^ Font weight (100-900)
  , lineHeight :: Number         -- ^ Line height (unitless or pixels)
  , letterSpacing :: Number      -- ^ Letter spacing in em
  }

-- | Create a type style.
mkTypeStyle
  :: FontFamily    -- ^ Font family
  -> Number        -- ^ Size in pixels
  -> FontWeight    -- ^ Weight
  -> Number        -- ^ Line height
  -> Number        -- ^ Letter spacing in em
  -> TypeStyle
mkTypeStyle family size weight lineHeight letterSpacing =
  { family: family
  , size: size
  , weight: weight
  , lineHeight: lineHeight
  , letterSpacing: letterSpacing
  }

-- | Get font family.
typeStyleFamily :: TypeStyle -> FontFamily
typeStyleFamily s = s.family

-- | Get font size.
typeStyleSize :: TypeStyle -> Number
typeStyleSize s = s.size

-- | Get font weight.
typeStyleWeight :: TypeStyle -> FontWeight
typeStyleWeight s = s.weight

-- | Get line height.
typeStyleLineHeight :: TypeStyle -> Number
typeStyleLineHeight s = s.lineHeight

-- | Get letter spacing.
typeStyleLetterSpacing :: TypeStyle -> Number
typeStyleLetterSpacing s = s.letterSpacing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // type // role
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic role of typography in the design system.
data TypeRole
  = RoleDisplay      -- ^ Large hero/display text
  | RoleHeading1     -- ^ H1 heading
  | RoleHeading2     -- ^ H2 heading
  | RoleHeading3     -- ^ H3 heading
  | RoleHeading4     -- ^ H4 heading
  | RoleHeading5     -- ^ H5 heading
  | RoleHeading6     -- ^ H6 heading
  | RoleBodyLarge    -- ^ Large body text
  | RoleBodyMedium   -- ^ Default body text
  | RoleBodySmall    -- ^ Small body text
  | RoleCaption      -- ^ Caption/small text
  | RoleOverline     -- ^ Overline/label text
  | RoleCode         -- ^ Monospace code
  | RoleQuote        -- ^ Block quote
  | RoleLabel        -- ^ Form label

derive instance eqTypeRole :: Eq TypeRole
derive instance ordTypeRole :: Ord TypeRole

instance showTypeRole :: Show TypeRole where
  show = typeRoleToString

-- | Convert role to string.
typeRoleToString :: TypeRole -> String
typeRoleToString = case _ of
  RoleDisplay -> "display"
  RoleHeading1 -> "h1"
  RoleHeading2 -> "h2"
  RoleHeading3 -> "h3"
  RoleHeading4 -> "h4"
  RoleHeading5 -> "h5"
  RoleHeading6 -> "h6"
  RoleBodyLarge -> "body-lg"
  RoleBodyMedium -> "body-md"
  RoleBodySmall -> "body-sm"
  RoleCaption -> "caption"
  RoleOverline -> "overline"
  RoleCode -> "code"
  RoleQuote -> "quote"
  RoleLabel -> "label"

-- | Parse role from string.
typeRoleFromString :: String -> Maybe TypeRole
typeRoleFromString s = case toLower (trim s) of
  "display" -> Just RoleDisplay
  "hero" -> Just RoleDisplay
  "h1" -> Just RoleHeading1
  "heading1" -> Just RoleHeading1
  "h2" -> Just RoleHeading2
  "heading2" -> Just RoleHeading2
  "h3" -> Just RoleHeading3
  "heading3" -> Just RoleHeading3
  "h4" -> Just RoleHeading4
  "heading4" -> Just RoleHeading4
  "h5" -> Just RoleHeading5
  "heading5" -> Just RoleHeading5
  "h6" -> Just RoleHeading6
  "heading6" -> Just RoleHeading6
  "body-lg" -> Just RoleBodyLarge
  "body-large" -> Just RoleBodyLarge
  "body-md" -> Just RoleBodyMedium
  "body" -> Just RoleBodyMedium
  "body-sm" -> Just RoleBodySmall
  "body-small" -> Just RoleBodySmall
  "caption" -> Just RoleCaption
  "small" -> Just RoleCaption
  "overline" -> Just RoleOverline
  "eyebrow" -> Just RoleOverline
  "code" -> Just RoleCode
  "mono" -> Just RoleCode
  "quote" -> Just RoleQuote
  "blockquote" -> Just RoleQuote
  "label" -> Just RoleLabel
  _ -> Nothing

-- | All type roles.
allTypeRoles :: Array TypeRole
allTypeRoles =
  [ RoleDisplay
  , RoleHeading1
  , RoleHeading2
  , RoleHeading3
  , RoleHeading4
  , RoleHeading5
  , RoleHeading6
  , RoleBodyLarge
  , RoleBodyMedium
  , RoleBodySmall
  , RoleCaption
  , RoleOverline
  , RoleCode
  , RoleQuote
  , RoleLabel
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // type // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Typography design token.
-- |
-- | Binds a semantic name to a type style with role metadata.
type TypeToken =
  { meta :: TokenMeta
  , style :: TypeStyle
  , role :: TypeRole
  }

-- | Create a type token with full metadata.
mkTypeToken :: TokenName -> TokenDesc -> TypeStyle -> TypeRole -> TypeToken
mkTypeToken name desc style role =
  { meta: mkTokenMeta name desc CategoryType
  , style: style
  , role: role
  }

-- | Create a type token with minimal metadata.
mkTypeTokenSimple :: TokenName -> TypeStyle -> TypeRole -> TypeToken
mkTypeTokenSimple name style role =
  let
    desc = mkTokenDesc ("Type token: " <> unTokenName name)
  in
    { meta: mkTokenMeta name desc CategoryType
    , style: style
    , role: role
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the token name.
typeTokenName :: TypeToken -> TokenName
typeTokenName t = t.meta.name

-- | Get the token description.
typeTokenDesc :: TypeToken -> TokenDesc
typeTokenDesc t = t.meta.description

-- | Get the type style.
typeTokenStyle :: TypeToken -> TypeStyle
typeTokenStyle t = t.style

-- | Get the type role.
typeTokenRole :: TypeToken -> TypeRole
typeTokenRole t = t.role

-- | Get the full metadata.
typeTokenMeta :: TypeToken -> TokenMeta
typeTokenMeta t = t.meta
