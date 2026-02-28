-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // typography // font-width
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FontWidth - horizontal scaling of letterforms (CSS font-stretch).
-- |
-- | Controls the width of glyphs from ultra-condensed to ultra-expanded.
-- | Modern variable fonts support continuous values; traditional fonts
-- | have discrete width variants.
-- |
-- | ## CSS Mapping
-- | Maps to `font-stretch` property as a percentage (50%-200%).
-- |
-- | ## Named Widths (CSS standard)
-- | - ultra-condensed: 50%
-- | - extra-condensed: 62.5%
-- | - condensed: 75%
-- | - semi-condensed: 87.5%
-- | - normal: 100%
-- | - semi-expanded: 112.5%
-- | - expanded: 125%
-- | - extra-expanded: 150%
-- | - ultra-expanded: 200%
-- |
-- | ## Variable Font Axis
-- | Corresponds to the 'wdth' axis in OpenType variable fonts.

module Hydrogen.Schema.Typography.FontWidth
  ( -- * Type
    FontWidth(..)
    
  -- * Constructor
  , fontWidth
  
  -- * Predefined Widths
  , ultraCondensed
  , extraCondensed
  , condensed
  , semiCondensed
  , normal
  , semiExpanded
  , expanded
  , extraExpanded
  , ultraExpanded
  
  -- * Accessors
  , unwrap
  , toPercentage
  , toLegacyCSSValue
  
  -- * Operations
  , clamp
  , lerp
  
  -- * Bounds
  , bounds
  ) where

import Prelude

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | FontWidth represents the horizontal scaling of letterforms.
-- | Bounded to [50, 200] representing percentage of normal width.
-- | Values outside this range are clamped.
newtype FontWidth = FontWidth Int

derive instance eqFontWidth :: Eq FontWidth
derive instance ordFontWidth :: Ord FontWidth

instance showFontWidth :: Show FontWidth where
  show (FontWidth n) = show n <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a FontWidth from an integer percentage.
-- | Values are clamped to the valid range [50, 200].
fontWidth :: Int -> FontWidth
fontWidth n
  | n < 50 = FontWidth 50
  | n > 200 = FontWidth 200
  | otherwise = FontWidth n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predefined
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ultra-condensed width (50%)
ultraCondensed :: FontWidth
ultraCondensed = FontWidth 50

-- | Extra-condensed width (62.5%, rounded to 63%)
extraCondensed :: FontWidth
extraCondensed = FontWidth 63

-- | Condensed width (75%)
condensed :: FontWidth
condensed = FontWidth 75

-- | Semi-condensed width (87.5%, rounded to 88%)
semiCondensed :: FontWidth
semiCondensed = FontWidth 88

-- | Normal width (100%)
normal :: FontWidth
normal = FontWidth 100

-- | Semi-expanded width (112.5%, rounded to 113%)
semiExpanded :: FontWidth
semiExpanded = FontWidth 113

-- | Expanded width (125%)
expanded :: FontWidth
expanded = FontWidth 125

-- | Extra-expanded width (150%)
extraExpanded :: FontWidth
extraExpanded = FontWidth 150

-- | Ultra-expanded width (200%)
ultraExpanded :: FontWidth
ultraExpanded = FontWidth 200

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw integer value
unwrap :: FontWidth -> Int
unwrap (FontWidth n) = n

-- | Convert to a percentage Number (for CSS)
toPercentage :: FontWidth -> Number
toPercentage (FontWidth n) = Int.toNumber n

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS value string
toLegacyCSSValue :: FontWidth -> String
toLegacyCSSValue (FontWidth n) = show n <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a FontWidth to valid range (identity, as constructor already clamps)
clamp :: FontWidth -> FontWidth
clamp = identity

-- | Linear interpolation between two font widths
-- | t = 0 returns the first width, t = 1 returns the second
lerp :: Number -> FontWidth -> FontWidth -> FontWidth
lerp t (FontWidth a) (FontWidth b) =
  let result = Int.toNumber a + t * (Int.toNumber b - Int.toNumber a)
  in fontWidth (Int.round result)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds documentation for FontWidth
-- |
-- | Min: 50 (ultra-condensed)
-- | Max: 200 (ultra-expanded)
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 50 200 "fontWidth" "Font stretch percentage (50-200)"
