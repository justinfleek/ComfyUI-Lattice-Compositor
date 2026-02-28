-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // brand // token // size
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Size Token molecule.
-- |
-- | A SizeToken binds a semantic name to a dimension value. Size tokens
-- | define widths, heights, and other dimensional values.
-- |
-- | ## Structure
-- |
-- | ```
-- | SizeToken = TokenMeta + SizeValue + SizePurpose
-- | ```
-- |
-- | ## Common Use Cases
-- |
-- | - Icon sizes (16, 20, 24, 32, 48px)
-- | - Avatar sizes (sm, md, lg)
-- | - Button heights
-- | - Input heights
-- | - Container max-widths
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Consistent sizing enables visual rhythm. When agents use `size.icon.md`
-- | instead of magic numbers, components maintain proportional harmony.

module Hydrogen.Schema.Brand.Token.Size
  ( -- * SizeToken Type
    SizeToken
  , mkSizeToken
  , mkSizeTokenPx
  
  -- * Accessors
  , sizeTokenName
  , sizeTokenDesc
  , sizeTokenValue
  , sizeTokenPurpose
  , sizeTokenMeta
  
  -- * Size Value
  , SizeValue
  , mkSizeValue
  , sizeValuePx
  
  -- * Size Purpose
  , SizePurpose(..)
  , sizePurposeToString
  , sizePurposeFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (<)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower, trim)

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(CategorySize)
  , TokenMeta
  , mkTokenMeta
  , mkTokenDesc
  , unTokenName
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // size // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Size value in pixels.
-- |
-- | Non-negative dimension value.
newtype SizeValue = SizeValue Number

derive instance eqSizeValue :: Eq SizeValue
derive instance ordSizeValue :: Ord SizeValue

instance showSizeValue :: Show SizeValue where
  show (SizeValue n) = show n <> "px"

-- | Create a size value in pixels.
mkSizeValue :: Number -> SizeValue
mkSizeValue n
  | n < 0.0 = SizeValue 0.0
  | otherwise = SizeValue n

-- | Get size value in pixels.
sizeValuePx :: SizeValue -> Number
sizeValuePx (SizeValue n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // size // purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Purpose of size in the design system.
data SizePurpose
  = PurposeIcon       -- ^ Icon dimensions
  | PurposeAvatar     -- ^ Avatar/profile image sizes
  | PurposeButton     -- ^ Button height
  | PurposeInput      -- ^ Input/control height
  | PurposeTouch      -- ^ Minimum touch target
  | PurposeContainer  -- ^ Container max-width
  | PurposeBreakpoint -- ^ Responsive breakpoint
  | PurposeFixed      -- ^ Fixed dimension
  | PurposeMinimum    -- ^ Minimum constraint
  | PurposeMaximum    -- ^ Maximum constraint

derive instance eqSizePurpose :: Eq SizePurpose
derive instance ordSizePurpose :: Ord SizePurpose

instance showSizePurpose :: Show SizePurpose where
  show = sizePurposeToString

-- | Convert purpose to string.
sizePurposeToString :: SizePurpose -> String
sizePurposeToString = case _ of
  PurposeIcon -> "icon"
  PurposeAvatar -> "avatar"
  PurposeButton -> "button"
  PurposeInput -> "input"
  PurposeTouch -> "touch"
  PurposeContainer -> "container"
  PurposeBreakpoint -> "breakpoint"
  PurposeFixed -> "fixed"
  PurposeMinimum -> "min"
  PurposeMaximum -> "max"

-- | Parse purpose from string.
sizePurposeFromString :: String -> Maybe SizePurpose
sizePurposeFromString s = case toLower (trim s) of
  "icon" -> Just PurposeIcon
  "avatar" -> Just PurposeAvatar
  "profile" -> Just PurposeAvatar
  "button" -> Just PurposeButton
  "input" -> Just PurposeInput
  "control" -> Just PurposeInput
  "touch" -> Just PurposeTouch
  "tap" -> Just PurposeTouch
  "container" -> Just PurposeContainer
  "breakpoint" -> Just PurposeBreakpoint
  "responsive" -> Just PurposeBreakpoint
  "fixed" -> Just PurposeFixed
  "min" -> Just PurposeMinimum
  "minimum" -> Just PurposeMinimum
  "max" -> Just PurposeMaximum
  "maximum" -> Just PurposeMaximum
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // size // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Size design token.
-- |
-- | Binds a semantic name to a size value with purpose metadata.
type SizeToken =
  { meta :: TokenMeta
  , value :: SizeValue
  , purpose :: SizePurpose
  }

-- | Create a size token with full metadata.
mkSizeToken :: TokenName -> TokenDesc -> SizeValue -> SizePurpose -> SizeToken
mkSizeToken name desc value purpose =
  { meta: mkTokenMeta name desc CategorySize
  , value: value
  , purpose: purpose
  }

-- | Create a size token from pixel value.
mkSizeTokenPx :: TokenName -> Number -> SizePurpose -> SizeToken
mkSizeTokenPx name px purpose =
  let
    desc = mkTokenDesc ("Size token: " <> unTokenName name)
    value = mkSizeValue px
  in
    { meta: mkTokenMeta name desc CategorySize
    , value: value
    , purpose: purpose
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the token name.
sizeTokenName :: SizeToken -> TokenName
sizeTokenName t = t.meta.name

-- | Get the token description.
sizeTokenDesc :: SizeToken -> TokenDesc
sizeTokenDesc t = t.meta.description

-- | Get the size value.
sizeTokenValue :: SizeToken -> SizeValue
sizeTokenValue t = t.value

-- | Get the size purpose.
sizeTokenPurpose :: SizeToken -> SizePurpose
sizeTokenPurpose t = t.purpose

-- | Get the full metadata.
sizeTokenMeta :: SizeToken -> TokenMeta
sizeTokenMeta t = t.meta
