-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // typography // letter-spacing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LetterSpacing - horizontal space between characters (tracking).
-- |
-- | Expressed as thousandths of an em (per mille). This is the professional
-- | typographic convention used in design tools:
-- | - **0**: Normal spacing (font's default metrics)
-- | - **25-50**: Light tracking - uppercase headings
-- | - **100+**: Loose tracking - display text, all-caps
-- | - **-25 to -50**: Tight tracking - large display text
-- |
-- | Note: In brand guides, "tracking 25" means 0.025em = 25/1000em.
-- | This module uses the same convention.
-- |
-- | Letter spacing affects text density and readability:
-- | - Uppercase text NEEDS positive tracking to breathe
-- | - Body text usually looks best at 0 (font's designed spacing)
-- | - Large display sizes can use negative tracking

module Hydrogen.Schema.Typography.LetterSpacing
  ( LetterSpacing
  , letterSpacing
  , unsafeLetterSpacing
  , fromEm
  , unwrap
  , toEm
  , toLegacyCss
  , bounds
  -- Common values
  , none
  , tight
  , normal
  , loose
  , uppercase
  -- Operations
  , blend
  , lerp
  , scale
  , add
  , subtract
  , invert
  , toNumber
  -- Predicates
  , isTight
  , isNone
  , isLoose
  , isNegative
  , isPositive
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (==)
  )

import Prelude (negate) as P
import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // letter spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Letter spacing in thousandths of an em (per mille)
-- |
-- | Professional typographic convention. A value of 25 means 0.025em
-- | of additional space between each character.
newtype LetterSpacing = LetterSpacing Int

derive instance eqLetterSpacing :: Eq LetterSpacing
derive instance ordLetterSpacing :: Ord LetterSpacing

instance showLetterSpacing :: Show LetterSpacing where
  show (LetterSpacing s) = show s <> "‰"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create letter spacing in per mille (thousandths of em)
-- |
-- | Range: -500 to 1000 (practical limits)
-- | - Negative values tighten spacing
-- | - Positive values loosen spacing
letterSpacing :: Int -> LetterSpacing
letterSpacing n = LetterSpacing (Bounded.clampInt (-500) 1000 n)

-- | Create letter spacing without clamping
-- |
-- | Use only when you know the value is valid.
unsafeLetterSpacing :: Int -> LetterSpacing
unsafeLetterSpacing = LetterSpacing

-- | Create letter spacing from em value
-- |
-- | Converts em to per mille: 0.025em → 25
fromEm :: Number -> LetterSpacing
fromEm em = letterSpacing (Int.round (em * 1000.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common values
-- ═════════════════════════════════════════════════════════════════════════════

-- | No additional spacing (0)
-- |
-- | Font's designed character spacing. Best for body text.
none :: LetterSpacing
none = LetterSpacing 0

-- | Tight spacing (-25)
-- |
-- | Subtle tightening for large display text where the optical spacing
-- | appears too loose.
tight :: LetterSpacing
tight = LetterSpacing (-25)

-- | Normal positive spacing (20)
-- |
-- | Slight expansion for improved readability in some contexts.
normal :: LetterSpacing
normal = LetterSpacing 20

-- | Loose spacing (50)
-- |
-- | Noticeable expansion for stylistic effect.
loose :: LetterSpacing
loose = LetterSpacing 50

-- | Uppercase tracking (25)
-- |
-- | Standard tracking for uppercase text. ALL-CAPS needs more space
-- | because uppercase letters have uniform height and no descenders.
uppercase :: LetterSpacing
uppercase = LetterSpacing 25

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two letter spacings with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation for animated typography:
-- | ```purescript
-- | blend 0.5 tight loose  -- LetterSpacing ~13 (midpoint of -25 and 50)
-- | ```
blend :: Number -> LetterSpacing -> LetterSpacing -> LetterSpacing
blend weight (LetterSpacing a) (LetterSpacing b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
      result = Int.toNumber a * (1.0 - w) + Int.toNumber b * w
  in letterSpacing (Int.round result)

-- | Linear interpolation (standard lerp signature)
lerp :: LetterSpacing -> LetterSpacing -> Number -> LetterSpacing
lerp from to t = blend t from to

-- | Scale letter spacing by a factor
-- |
-- | Useful for responsive adjustments:
-- | ```purescript
-- | scale 2.0 uppercase  -- LetterSpacing 50
-- | scale 0.5 loose      -- LetterSpacing 25
-- | ```
scale :: Number -> LetterSpacing -> LetterSpacing
scale factor (LetterSpacing s) = letterSpacing (Int.round (Int.toNumber s * factor))

-- | Add to letter spacing (clamped)
add :: Int -> LetterSpacing -> LetterSpacing
add amount (LetterSpacing s) = letterSpacing (s + amount)

-- | Subtract from letter spacing (clamped)
subtract :: Int -> LetterSpacing -> LetterSpacing
subtract amount (LetterSpacing s) = letterSpacing (s - amount)

-- | Invert letter spacing (negate)
-- |
-- | Flips tight to loose and vice versa:
-- | ```purescript
-- | invert tight  -- LetterSpacing 25 (was -25)
-- | invert loose  -- LetterSpacing -50 (was 50)
-- | ```
invert :: LetterSpacing -> LetterSpacing
invert (LetterSpacing s) = letterSpacing (P.negate s)

-- | Convert to Number for calculations
toNumber :: LetterSpacing -> Number
toNumber (LetterSpacing s) = Int.toNumber s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if letter spacing is tight (negative)
-- |
-- | Negative tracking brings letters closer together:
-- | ```purescript
-- | isTight tight  -- true (-25)
-- | isTight none   -- false (0)
-- | ```
isTight :: LetterSpacing -> Boolean
isTight (LetterSpacing s) = s < 0

-- | Check if letter spacing is none (0)
-- |
-- | Font's default spacing with no adjustment:
-- | ```purescript
-- | isNone none      -- true
-- | isNone tight     -- false
-- | isNone uppercase -- false
-- | ```
isNone :: LetterSpacing -> Boolean
isNone (LetterSpacing s) = s == 0

-- | Check if letter spacing is loose (positive)
-- |
-- | Positive tracking spreads letters apart:
-- | ```purescript
-- | isLoose loose     -- true (50)
-- | isLoose uppercase -- true (25)
-- | isLoose none      -- false (0)
-- | ```
isLoose :: LetterSpacing -> Boolean
isLoose (LetterSpacing s) = s > 0

-- | Check if letter spacing is negative
-- |
-- | Alias for isTight, for semantic clarity.
isNegative :: LetterSpacing -> Boolean
isNegative = isTight

-- | Check if letter spacing is positive
-- |
-- | Alias for isLoose, for semantic clarity.
isPositive :: LetterSpacing -> Boolean
isPositive = isLoose

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value (per mille)
unwrap :: LetterSpacing -> Int
unwrap (LetterSpacing s) = s

-- | Convert to em value for calculations
-- |
-- | 25 per mille → 0.025em
toEm :: LetterSpacing -> Number
toEm (LetterSpacing s) = Int.toNumber s / 1000.0

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS letter-spacing value
-- |
-- | Outputs in em units for proper scaling with font size.
toLegacyCss :: LetterSpacing -> String
toLegacyCss ls = show (toEm ls) <> "em"

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds (-500) 1000 "letterSpacing" "Letter spacing in per mille"
