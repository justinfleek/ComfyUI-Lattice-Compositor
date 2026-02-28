-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // typography // font-weight
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FontWeight - typographic stroke thickness.
-- |
-- | A numeric value from 1 to 1000 following the CSS font-weight specification:
-- | - **100**: Thin (Hairline)
-- | - **200**: Extra Light (Ultra Light)
-- | - **300**: Light
-- | - **400**: Normal (Regular)
-- | - **500**: Medium
-- | - **600**: Semi Bold (Demi Bold)
-- | - **700**: Bold
-- | - **800**: Extra Bold (Ultra Bold)
-- | - **900**: Black (Heavy)
-- |
-- | Variable fonts support any integer value in this range. Named constants
-- | are provided for the standard 9 weights.

module Hydrogen.Schema.Typography.FontWeight
  ( FontWeight
  , fontWeight
  , unsafeFontWeight
  , unwrap
  , toNumber
  , toLegacyCss
  , bounds
  -- Named weights
  , thin
  , extraLight
  , light
  , normal
  , medium
  , semiBold
  , bold
  , extraBold
  , black
  -- Named weight predicates
  , isThin
  , isLight
  , isNormal
  , isMedium
  , isBold
  , isBlack
  ) where

import Prelude

import Data.Int (toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // font weight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font weight value (1-1000)
-- |
-- | Represents stroke thickness in the CSS font-weight scale.
-- | Standard fonts support 9 named weights (100-900 in increments of 100).
-- | Variable fonts support any integer value from 1-1000.
newtype FontWeight = FontWeight Int

derive instance eqFontWeight :: Eq FontWeight
derive instance ordFontWeight :: Ord FontWeight

instance showFontWeight :: Show FontWeight where
  show (FontWeight w) = "FontWeight " <> show w

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a font weight, clamping to 1-1000
fontWeight :: Int -> FontWeight
fontWeight n = FontWeight (Bounded.clampInt 1 1000 n)

-- | Create a font weight without clamping
-- |
-- | Use only when you know the value is valid.
unsafeFontWeight :: Int -> FontWeight
unsafeFontWeight = FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // named weights
-- ═════════════════════════════════════════════════════════════════════════════

-- | Thin / Hairline (100)
thin :: FontWeight
thin = FontWeight 100

-- | Extra Light / Ultra Light (200)
extraLight :: FontWeight
extraLight = FontWeight 200

-- | Light (300)
light :: FontWeight
light = FontWeight 300

-- | Normal / Regular (400) - the default weight
normal :: FontWeight
normal = FontWeight 400

-- | Medium (500)
medium :: FontWeight
medium = FontWeight 500

-- | Semi Bold / Demi Bold (600)
semiBold :: FontWeight
semiBold = FontWeight 600

-- | Bold (700)
bold :: FontWeight
bold = FontWeight 700

-- | Extra Bold / Ultra Bold (800)
extraBold :: FontWeight
extraBold = FontWeight 800

-- | Black / Heavy (900)
black :: FontWeight
black = FontWeight 900

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this weight in the thin range (1-199)?
isThin :: FontWeight -> Boolean
isThin (FontWeight w) = w < 200

-- | Is this weight in the light range (200-399)?
isLight :: FontWeight -> Boolean
isLight (FontWeight w) = w >= 200 && w < 400

-- | Is this weight in the normal range (400-499)?
isNormal :: FontWeight -> Boolean
isNormal (FontWeight w) = w >= 400 && w < 500

-- | Is this weight in the medium range (500-599)?
isMedium :: FontWeight -> Boolean
isMedium (FontWeight w) = w >= 500 && w < 600

-- | Is this weight in the bold range (600-799)?
isBold :: FontWeight -> Boolean
isBold (FontWeight w) = w >= 600 && w < 800

-- | Is this weight in the black range (800-1000)?
isBlack :: FontWeight -> Boolean
isBlack (FontWeight w) = w >= 800

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: FontWeight -> Int
unwrap (FontWeight w) = w

-- | Convert to Number for calculations
toNumber :: FontWeight -> Number
toNumber (FontWeight w) = Int.toNumber w

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS font-weight value
toLegacyCss :: FontWeight -> String
toLegacyCss (FontWeight w) = show w

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 1 1000 "fontWeight" "Font stroke thickness (1-1000)"
