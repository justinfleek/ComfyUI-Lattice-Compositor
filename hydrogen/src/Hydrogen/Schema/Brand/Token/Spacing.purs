-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // brand // token // spacing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spacing Token molecule.
-- |
-- | A SpacingToken binds a semantic name to a spacing value. Spacing tokens
-- | define consistent padding, margin, and gap values across a design system.
-- |
-- | ## Structure
-- |
-- | ```
-- | SpacingToken = TokenMeta + SpacingValue + SpacingPurpose
-- | ```
-- |
-- | ## Standard Scale
-- |
-- | Most design systems use a scale multiplied by a base unit:
-- | - `spacing.0` = 0px (none)
-- | - `spacing.1` = 4px (xs)
-- | - `spacing.2` = 8px (sm)
-- | - `spacing.3` = 12px
-- | - `spacing.4` = 16px (md, base)
-- | - `spacing.6` = 24px (lg)
-- | - `spacing.8` = 32px (xl)
-- | - `spacing.12` = 48px (2xl)
-- | - `spacing.16` = 64px (3xl)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Consistent spacing enables visual harmony across agent-generated UIs.
-- | When all agents use `spacing.4` for standard padding, the result is
-- | coherent even when components are composed from different sources.

module Hydrogen.Schema.Brand.Token.Spacing
  ( -- * SpacingToken Type
    SpacingToken
  , mkSpacingToken
  , mkSpacingTokenPx
  
  -- * Accessors
  , spacingTokenName
  , spacingTokenDesc
  , spacingTokenValue
  , spacingTokenPurpose
  , spacingTokenMeta
  
  -- * Spacing Value
  , SpacingValue
  , mkSpacingValue
  , spacingValuePx
  , spacingValueRem
  
  -- * Spacing Purpose
  , SpacingPurpose(..)
  , purposeToString
  , purposeFromString
  
  -- * Spacing Scale
  , SpacingScale(..)
  , scaleToString
  , scaleFromString
  , scaleToMultiplier
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (<)
  , (/)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower, trim)

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(CategorySpacing)
  , TokenMeta
  , mkTokenMeta
  , mkTokenDesc
  , unTokenName
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // spacing // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spacing value in pixels.
-- |
-- | Internally stored as pixels for precision. Can be converted to rem
-- | using a base font size (typically 16px).
newtype SpacingValue = SpacingValue Number

derive instance eqSpacingValue :: Eq SpacingValue
derive instance ordSpacingValue :: Ord SpacingValue

instance showSpacingValue :: Show SpacingValue where
  show (SpacingValue n) = show n <> "px"

-- | Create a spacing value in pixels.
mkSpacingValue :: Number -> SpacingValue
mkSpacingValue n
  | n < 0.0 = SpacingValue 0.0
  | otherwise = SpacingValue n

-- | Get spacing value in pixels.
spacingValuePx :: SpacingValue -> Number
spacingValuePx (SpacingValue n) = n

-- | Get spacing value in rem (assumes 16px base).
spacingValueRem :: SpacingValue -> Number
spacingValueRem (SpacingValue n) = n / 16.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // spacing // purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Purpose of spacing in the design system.
-- |
-- | Defines how the spacing is intended to be used.
data SpacingPurpose
  = PurposePadding     -- ^ Internal spacing (content from edge)
  | PurposeMargin      -- ^ External spacing (between elements)
  | PurposeGap         -- ^ Grid/flex gap between children
  | PurposeInset       -- ^ Equal padding on all sides
  | PurposeStack       -- ^ Vertical spacing between stacked items
  | PurposeInline      -- ^ Horizontal spacing between inline items
  | PurposeSection     -- ^ Large spacing between page sections
  | PurposeComponent   -- ^ Internal component spacing
  | PurposeLayout      -- ^ Page/container spacing

derive instance eqSpacingPurpose :: Eq SpacingPurpose
derive instance ordSpacingPurpose :: Ord SpacingPurpose

instance showSpacingPurpose :: Show SpacingPurpose where
  show = purposeToString

-- | Convert purpose to string.
purposeToString :: SpacingPurpose -> String
purposeToString = case _ of
  PurposePadding -> "padding"
  PurposeMargin -> "margin"
  PurposeGap -> "gap"
  PurposeInset -> "inset"
  PurposeStack -> "stack"
  PurposeInline -> "inline"
  PurposeSection -> "section"
  PurposeComponent -> "component"
  PurposeLayout -> "layout"

-- | Parse purpose from string.
purposeFromString :: String -> Maybe SpacingPurpose
purposeFromString s = case toLower (trim s) of
  "padding" -> Just PurposePadding
  "margin" -> Just PurposeMargin
  "gap" -> Just PurposeGap
  "inset" -> Just PurposeInset
  "stack" -> Just PurposeStack
  "vertical" -> Just PurposeStack
  "inline" -> Just PurposeInline
  "horizontal" -> Just PurposeInline
  "section" -> Just PurposeSection
  "component" -> Just PurposeComponent
  "layout" -> Just PurposeLayout
  "page" -> Just PurposeLayout
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // spacing // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named spacing scale levels.
-- |
-- | Standard semantic names for spacing sizes.
data SpacingScale
  = ScaleNone    -- ^ 0px
  | ScaleXs      -- ^ Extra small (4px)
  | ScaleSm      -- ^ Small (8px)
  | ScaleMd      -- ^ Medium (16px) - base
  | ScaleLg      -- ^ Large (24px)
  | ScaleXl      -- ^ Extra large (32px)
  | Scale2xl     -- ^ 2x extra large (48px)
  | Scale3xl     -- ^ 3x extra large (64px)
  | Scale4xl     -- ^ 4x extra large (96px)

derive instance eqSpacingScale :: Eq SpacingScale
derive instance ordSpacingScale :: Ord SpacingScale

instance showSpacingScale :: Show SpacingScale where
  show = scaleToString

-- | Convert scale to string.
scaleToString :: SpacingScale -> String
scaleToString = case _ of
  ScaleNone -> "none"
  ScaleXs -> "xs"
  ScaleSm -> "sm"
  ScaleMd -> "md"
  ScaleLg -> "lg"
  ScaleXl -> "xl"
  Scale2xl -> "2xl"
  Scale3xl -> "3xl"
  Scale4xl -> "4xl"

-- | Parse scale from string.
scaleFromString :: String -> Maybe SpacingScale
scaleFromString s = case toLower (trim s) of
  "none" -> Just ScaleNone
  "0" -> Just ScaleNone
  "xs" -> Just ScaleXs
  "sm" -> Just ScaleSm
  "small" -> Just ScaleSm
  "md" -> Just ScaleMd
  "medium" -> Just ScaleMd
  "base" -> Just ScaleMd
  "lg" -> Just ScaleLg
  "large" -> Just ScaleLg
  "xl" -> Just ScaleXl
  "2xl" -> Just Scale2xl
  "3xl" -> Just Scale3xl
  "4xl" -> Just Scale4xl
  _ -> Nothing

-- | Get multiplier for scale (base = 16px).
scaleToMultiplier :: SpacingScale -> Number
scaleToMultiplier = case _ of
  ScaleNone -> 0.0
  ScaleXs -> 0.25
  ScaleSm -> 0.5
  ScaleMd -> 1.0
  ScaleLg -> 1.5
  ScaleXl -> 2.0
  Scale2xl -> 3.0
  Scale3xl -> 4.0
  Scale4xl -> 6.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // spacing // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spacing design token.
-- |
-- | Binds a semantic name to a spacing value with purpose metadata.
type SpacingToken =
  { meta :: TokenMeta
  , value :: SpacingValue
  , purpose :: SpacingPurpose
  }

-- | Create a spacing token with full metadata.
mkSpacingToken :: TokenName -> TokenDesc -> SpacingValue -> SpacingPurpose -> SpacingToken
mkSpacingToken name desc value purpose =
  { meta: mkTokenMeta name desc CategorySpacing
  , value: value
  , purpose: purpose
  }

-- | Create a spacing token from pixel value.
mkSpacingTokenPx :: TokenName -> Number -> SpacingPurpose -> SpacingToken
mkSpacingTokenPx name px purpose =
  let
    desc = mkTokenDesc ("Spacing token: " <> unTokenName name)
    value = mkSpacingValue px
  in
    { meta: mkTokenMeta name desc CategorySpacing
    , value: value
    , purpose: purpose
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the token name.
spacingTokenName :: SpacingToken -> TokenName
spacingTokenName t = t.meta.name

-- | Get the token description.
spacingTokenDesc :: SpacingToken -> TokenDesc
spacingTokenDesc t = t.meta.description

-- | Get the spacing value.
spacingTokenValue :: SpacingToken -> SpacingValue
spacingTokenValue t = t.value

-- | Get the spacing purpose.
spacingTokenPurpose :: SpacingToken -> SpacingPurpose
spacingTokenPurpose t = t.purpose

-- | Get the full metadata.
spacingTokenMeta :: SpacingToken -> TokenMeta
spacingTokenMeta t = t.meta
