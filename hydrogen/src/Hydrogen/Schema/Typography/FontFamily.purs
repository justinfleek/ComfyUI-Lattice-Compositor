-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // typography // font-family
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FontFamily - typeface identification.
-- |
-- | A font family name as a String. Font families are NOT enumerable —
-- | there are infinite possibilities (custom fonts, variable fonts, etc.).
-- |
-- | The FontFamily type is opaque to prevent invalid CSS font-family values.
-- | Font stacks (fallback chains) are handled separately in TypeStyle.
-- |
-- | Examples:
-- | - "Archivo" — Custom font (requires import)
-- | - "Poppins" — Custom font (requires import)
-- | - "system-ui" — System font stack keyword
-- | - "Georgia" — Web-safe font

module Hydrogen.Schema.Typography.FontFamily
  ( FontFamily
  , fontFamily
  , unwrap
  , toLegacyCss
  -- Generic families (CSS keywords)
  , serif
  , sansSerif
  , monospace
  , cursive
  , fantasy
  , systemUi
  , uiSerif
  , uiSansSerif
  , uiMonospace
  , uiRounded
  , emoji
  , math
  , fangsong
  ) where

import Prelude

import Data.String (contains, Pattern(Pattern))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // font family
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font family name
-- |
-- | Represents a single typeface. Use FontStack for fallback chains.
-- | The name is stored as provided — CSS quoting is handled at render time.
newtype FontFamily = FontFamily String

derive instance eqFontFamily :: Eq FontFamily
derive instance ordFontFamily :: Ord FontFamily

instance showFontFamily :: Show FontFamily where
  show (FontFamily f) = "FontFamily " <> show f

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a font family from a name
-- |
-- | The name should be the exact font family name as it appears in the
-- | font file or CSS @font-face declaration.
fontFamily :: String -> FontFamily
fontFamily = FontFamily

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // generic families
-- ═════════════════════════════════════════════════════════════════════════════

-- These are CSS generic family keywords. They don't require quotes in CSS
-- and map to system-appropriate fonts.

-- | Generic serif family
serif :: FontFamily
serif = FontFamily "serif"

-- | Generic sans-serif family
sansSerif :: FontFamily
sansSerif = FontFamily "sans-serif"

-- | Generic monospace family
monospace :: FontFamily
monospace = FontFamily "monospace"

-- | Generic cursive family
cursive :: FontFamily
cursive = FontFamily "cursive"

-- | Generic fantasy family
fantasy :: FontFamily
fantasy = FontFamily "fantasy"

-- | System UI font stack
-- |
-- | Uses the operating system's default UI font. Best for interfaces
-- | that should feel native to the platform.
systemUi :: FontFamily
systemUi = FontFamily "system-ui"

-- | System UI serif font
uiSerif :: FontFamily
uiSerif = FontFamily "ui-serif"

-- | System UI sans-serif font
uiSansSerif :: FontFamily
uiSansSerif = FontFamily "ui-sans-serif"

-- | System UI monospace font
uiMonospace :: FontFamily
uiMonospace = FontFamily "ui-monospace"

-- | System UI rounded font
uiRounded :: FontFamily
uiRounded = FontFamily "ui-rounded"

-- | Emoji font
emoji :: FontFamily
emoji = FontFamily "emoji"

-- | Mathematical notation font
math :: FontFamily
math = FontFamily "math"

-- | Chinese Fangsong style
fangsong :: FontFamily
fangsong = FontFamily "fangsong"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw String value
unwrap :: FontFamily -> String
unwrap (FontFamily f) = f

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS font-family value
-- |
-- | Adds quotes if the family name contains spaces or special characters.
-- | Generic family names (serif, sans-serif, etc.) are not quoted.
toLegacyCss :: FontFamily -> String
toLegacyCss (FontFamily f)
  | isGenericFamily f = f
  | needsQuotes f = "\"" <> f <> "\""
  | otherwise = f

-- | Check if a font family name is a CSS generic family keyword
isGenericFamily :: String -> Boolean
isGenericFamily name = name == "serif"
  || name == "sans-serif"
  || name == "monospace"
  || name == "cursive"
  || name == "fantasy"
  || name == "system-ui"
  || name == "ui-serif"
  || name == "ui-sans-serif"
  || name == "ui-monospace"
  || name == "ui-rounded"
  || name == "emoji"
  || name == "math"
  || name == "fangsong"

-- | Check if a font family name needs quotes in CSS
needsQuotes :: String -> Boolean
needsQuotes name = contains (Pattern " ") name
  || contains (Pattern "-") name
  || contains (Pattern ".") name
