-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // typography // word-spacing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WordSpacing - adjustment to space between words.
-- |
-- | Controls the additional spacing added between words beyond the normal
-- | space character width. Useful for display typography, justified text
-- | tuning, and readability adjustments.
-- |
-- | ## CSS Mapping
-- | Maps to `word-spacing` property. Values are additive to the normal
-- | word space (typically 0.25em for most fonts).
-- |
-- | ## Units
-- | Stored as per mille (thousandths) of an em for precision.
-- | Allows both positive (wider) and negative (tighter) spacing.

module Hydrogen.Schema.Typography.WordSpacing
  ( -- * Type
    WordSpacing(..)
    
  -- * Constructors
  , wordSpacing
  , fromEm
  , fromPixels
  
  -- * Predefined Values
  , normal
  , tight
  , loose
  , veryTight
  , veryLoose
  
  -- * Accessors
  , unwrap
  , toEm
  , toLegacyCSSValue
  
  -- * Operations
  , scale
  , negate
  , add
  ) where

import Prelude hiding (negate, add)
import Prelude (negate) as P

import Data.Int (round, toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | WordSpacing represents adjustment to space between words.
-- | Stored as per mille (thousandths of an em) for precision.
-- | Negative values tighten, positive values loosen.
newtype WordSpacing = WordSpacing Int

derive instance eqWordSpacing :: Eq WordSpacing
derive instance ordWordSpacing :: Ord WordSpacing

instance showWordSpacing :: Show WordSpacing where
  show ws = show (toEm ws) <> "em"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create WordSpacing from per mille (thousandths of em)
wordSpacing :: Int -> WordSpacing
wordSpacing = WordSpacing

-- | Create WordSpacing from em value
fromEm :: Number -> WordSpacing
fromEm em = WordSpacing (Int.round (em * 1000.0))

-- | Create WordSpacing from pixels (requires font size context)
-- | fontSize is the current font size in pixels
fromPixels :: Number -> Number -> WordSpacing
fromPixels fontSize pixels =
  let em = pixels / fontSize
  in fromEm em

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predefined
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normal word spacing (no adjustment)
normal :: WordSpacing
normal = WordSpacing 0

-- | Tight word spacing (-50 per mille = -0.05em)
tight :: WordSpacing
tight = WordSpacing (P.negate 50)

-- | Loose word spacing (100 per mille = 0.1em)
loose :: WordSpacing
loose = WordSpacing 100

-- | Very tight word spacing (-100 per mille = -0.1em)
veryTight :: WordSpacing
veryTight = WordSpacing (P.negate 100)

-- | Very loose word spacing (250 per mille = 0.25em)
veryLoose :: WordSpacing
veryLoose = WordSpacing 250

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw per mille value
unwrap :: WordSpacing -> Int
unwrap (WordSpacing n) = n

-- | Convert to em value
toEm :: WordSpacing -> Number
toEm (WordSpacing n) = Int.toNumber n / 1000.0

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS value string
toLegacyCSSValue :: WordSpacing -> String
toLegacyCSSValue ws
  | unwrap ws == 0 = "normal"
  | otherwise = show (toEm ws) <> "em"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale word spacing by a factor
scale :: Number -> WordSpacing -> WordSpacing
scale factor (WordSpacing n) = WordSpacing (Int.round (Int.toNumber n * factor))

-- | Negate word spacing (tight becomes loose, loose becomes tight)
negate :: WordSpacing -> WordSpacing
negate (WordSpacing n) = WordSpacing (P.negate n)

-- | Add two word spacing values
add :: WordSpacing -> WordSpacing -> WordSpacing
add (WordSpacing a) (WordSpacing b) = WordSpacing (a + b)
