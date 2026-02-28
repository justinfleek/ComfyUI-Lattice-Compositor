-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // dimension // relative
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Relative units - typography and element-relative measurements.
-- |
-- | These units are relative to some reference (font size, line height,
-- | viewport dimension, container dimension). They enable responsive design
-- | and fluid typography.
-- |
-- | ## Type Safety
-- |
-- | Each unit is a distinct newtype. You cannot add Em to Pixel without
-- | explicit conversion through the reference context.
-- |
-- | ## Dependencies
-- | - Prelude
-- |
-- | ## Dependents
-- | - Style.Typography (font-size, line-height, letter-spacing)
-- | - Layout.Flex (flex-grow, flex-shrink)
-- | - Layout.Grid (column-width, row-height)

module Hydrogen.Schema.Dimension.Relative
  ( -- * Em Units (relative to font-size)
    Em(Em)
  , em
  , ems
  , unwrapEm
  
  -- * Rem Units (relative to root font-size)
  , Rem(Rem)
  , rem
  , rems
  , unwrapRem
  
  -- * Ex Units (relative to x-height)
  , Ex(Ex)
  , ex
  , exs
  , unwrapEx
  
  -- * Ch Units (relative to zero character width)
  , Ch(Ch)
  , ch
  , chs
  , unwrapCh
  
  -- * Cap Height Units
  , Cap(Cap)
  , cap
  , caps
  , unwrapCap
  
  -- * CJK Ideograph Width
  , Ic(Ic)
  , ic
  , ics
  , unwrapIc
  
  -- * Line Height Units
  , Lh(Lh)
  , lh
  , lhs
  , unwrapLh
  
  -- * Root Line Height Units
  , Rlh(Rlh)
  , rlh
  , rlhs
  , unwrapRlh
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // em // units
-- ═════════════════════════════════════════════════════════════════════════════

-- | Em unit - relative to element's font-size.
-- |
-- | 1em = the font-size of the element. If font-size is 16px, then 2em = 32px.
-- | Useful for element-specific scaling.
newtype Em = Em Number

derive instance eqEm :: Eq Em
derive instance ordEm :: Ord Em

instance showEm :: Show Em where
  show (Em v) = show v <> "em"

-- | Create Em from Number
em :: Number -> Em
em = Em

-- | Create Em (plural alias)
ems :: Number -> Em
ems = em

-- | Unwrap Em to raw Number
unwrapEm :: Em -> Number
unwrapEm (Em v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // rem // units
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rem unit - relative to root (document) font-size.
-- |
-- | 1rem = the font-size of the root element (html). If root font-size
-- | is 16px, then 2rem = 32px regardless of element's local font-size.
-- | Preferred for consistent scaling across the document.
newtype Rem = Rem Number

derive instance eqRem :: Eq Rem
derive instance ordRem :: Ord Rem

instance showRem :: Show Rem where
  show (Rem v) = show v <> "rem"

-- | Create Rem from Number
rem :: Number -> Rem
rem = Rem

-- | Create Rem (plural alias)
rems :: Number -> Rem
rems = rem

-- | Unwrap Rem to raw Number
unwrapRem :: Rem -> Number
unwrapRem (Rem v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // ex // units
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ex unit - relative to x-height of the font.
-- |
-- | 1ex = the x-height of the font (height of lowercase 'x').
-- | Less predictable than em because x-height varies by typeface.
newtype Ex = Ex Number

derive instance eqEx :: Eq Ex
derive instance ordEx :: Ord Ex

instance showEx :: Show Ex where
  show (Ex v) = show v <> "ex"

-- | Create Ex from Number
ex :: Number -> Ex
ex = Ex

-- | Create Ex (plural alias)
exs :: Number -> Ex
exs = ex

-- | Unwrap Ex to raw Number
unwrapEx :: Ex -> Number
unwrapEx (Ex v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // ch // units
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ch unit - relative to width of the '0' (zero) character.
-- |
-- | 1ch = the width of the '0' glyph in the element's font.
-- | Useful for sizing text inputs to fit a known number of characters.
newtype Ch = Ch Number

derive instance eqCh :: Eq Ch
derive instance ordCh :: Ord Ch

instance showCh :: Show Ch where
  show (Ch v) = show v <> "ch"

-- | Create Ch from Number
ch :: Number -> Ch
ch = Ch

-- | Create Ch (plural alias)
chs :: Number -> Ch
chs = ch

-- | Unwrap Ch to raw Number
unwrapCh :: Ch -> Number
unwrapCh (Ch v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cap // units
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cap unit - relative to capital letter height.
-- |
-- | 1cap = the cap-height of the font (height of capital letters).
-- | Useful for sizing elements to match capital letter proportions.
newtype Cap = Cap Number

derive instance eqCap :: Eq Cap
derive instance ordCap :: Ord Cap

instance showCap :: Show Cap where
  show (Cap v) = show v <> "cap"

-- | Create Cap from Number
cap :: Number -> Cap
cap = Cap

-- | Create Cap (plural alias)
caps :: Number -> Cap
caps = cap

-- | Unwrap Cap to raw Number
unwrapCap :: Cap -> Number
unwrapCap (Cap v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // ic // units
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ic unit - CJK water ideograph width.
-- |
-- | 1ic = the width of a CJK water ideograph (水) in the font.
-- | Used for CJK typography sizing.
newtype Ic = Ic Number

derive instance eqIc :: Eq Ic
derive instance ordIc :: Ord Ic

instance showIc :: Show Ic where
  show (Ic v) = show v <> "ic"

-- | Create Ic from Number
ic :: Number -> Ic
ic = Ic

-- | Create Ic (plural alias)
ics :: Number -> Ic
ics = ic

-- | Unwrap Ic to raw Number
unwrapIc :: Ic -> Number
unwrapIc (Ic v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // lh // units
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lh unit - relative to line-height of the element.
-- |
-- | 1lh = the line-height of the element (computed value).
-- | Useful for vertical rhythm based on line height.
newtype Lh = Lh Number

derive instance eqLh :: Eq Lh
derive instance ordLh :: Ord Lh

instance showLh :: Show Lh where
  show (Lh v) = show v <> "lh"

-- | Create Lh from Number
lh :: Number -> Lh
lh = Lh

-- | Create Lh (plural alias)
lhs :: Number -> Lh
lhs = lh

-- | Unwrap Lh to raw Number
unwrapLh :: Lh -> Number
unwrapLh (Lh v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // rlh // units
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rlh unit - relative to root line-height.
-- |
-- | 1rlh = the line-height of the root element.
-- | Like rem but for line-height.
newtype Rlh = Rlh Number

derive instance eqRlh :: Eq Rlh
derive instance ordRlh :: Ord Rlh

instance showRlh :: Show Rlh where
  show (Rlh v) = show v <> "rlh"

-- | Create Rlh from Number
rlh :: Number -> Rlh
rlh = Rlh

-- | Create Rlh (plural alias)
rlhs :: Number -> Rlh
rlhs = rlh

-- | Unwrap Rlh to raw Number
unwrapRlh :: Rlh -> Number
unwrapRlh (Rlh v) = v
