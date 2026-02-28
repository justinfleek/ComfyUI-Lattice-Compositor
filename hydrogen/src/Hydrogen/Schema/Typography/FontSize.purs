-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // typography // font-size
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FontSize - typographic scale in pixels.
-- |
-- | A positive number representing font size in CSS pixels. Font sizes are
-- | resolution-independent - a 16px font renders at appropriate physical
-- | size on any device via DPR scaling.
-- |
-- | Common base sizes:
-- | - **16px**: Browser default, most readable for body text
-- | - **18px**: Enhanced readability, common for premium sites
-- | - **14px**: Compact interfaces, data-heavy applications
-- |
-- | Font sizes must be positive. Zero and negative values are invalid.

module Hydrogen.Schema.Typography.FontSize
  ( FontSize
  , fontSize
  , unsafeFontSize
  , unwrap
  , scale
  , toLegacyCss
  , bounds
  -- Common sizes
  , browserDefault
  , compact
  , readable
  -- Operations
  , blend
  , lerp
  , add
  , subtract
  , toNumber
  , toRem
  -- Predicates
  , isReadable
  , isCompact
  , isDisplay
  , isHero
  -- Type scale
  , minor
  , major
  , heading1
  , heading2
  , heading3
  , body
  , caption
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // font size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font size in CSS pixels (positive Number)
-- |
-- | Represents the em-square height of a font. Actual glyph heights vary
-- | within this bounding box based on the font's design.
newtype FontSize = FontSize Number

derive instance eqFontSize :: Eq FontSize
derive instance ordFontSize :: Ord FontSize

instance showFontSize :: Show FontSize where
  show (FontSize s) = show s <> "px"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a font size, clamping to positive values
-- |
-- | Minimum size is 1px to prevent invisible text.
-- | Maximum size is 1000px (practical limit for display).
fontSize :: Number -> FontSize
fontSize n = FontSize (Bounded.clampNumber 1.0 1000.0 n)

-- | Create a font size without clamping
-- |
-- | Use only when you know the value is valid.
unsafeFontSize :: Number -> FontSize
unsafeFontSize = FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // common sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Browser default size (16px)
-- |
-- | The standard base size for web content. Used as the reference for
-- | rem calculations.
browserDefault :: FontSize
browserDefault = FontSize 16.0

-- | Compact size (14px)
-- |
-- | For data-dense interfaces where space efficiency matters more than
-- | optimal readability.
compact :: FontSize
compact = FontSize 14.0

-- | Enhanced readable size (18px)
-- |
-- | For premium reading experiences and accessibility-focused designs.
readable :: FontSize
readable = FontSize 18.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale font size by a factor
-- |
-- | Used for type scale calculations. The factor must be positive.
scale :: Number -> FontSize -> FontSize
scale factor (FontSize s) = fontSize (s * factor)

-- | Blend two font sizes with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation for animated type sizes:
-- | ```purescript
-- | blend 0.5 compact readable  -- FontSize 16px (midpoint)
-- | ```
blend :: Number -> FontSize -> FontSize -> FontSize
blend weight (FontSize a) (FontSize b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in fontSize (a * (1.0 - w) + b * w)

-- | Linear interpolation (standard lerp signature)
lerp :: FontSize -> FontSize -> Number -> FontSize
lerp from to t = blend t from to

-- | Add to font size (clamped)
add :: Number -> FontSize -> FontSize
add amount (FontSize s) = fontSize (s + amount)

-- | Subtract from font size (clamped)
subtract :: Number -> FontSize -> FontSize
subtract amount (FontSize s) = fontSize (s - amount)

-- | Convert to Number for calculations
toNumber :: FontSize -> Number
toNumber (FontSize s) = s

-- | Convert to rem value (assuming 16px base)
-- |
-- | For responsive typography that respects user's browser settings:
-- | ```purescript
-- | toRem browserDefault  -- 1.0
-- | toRem (fontSize 24.0) -- 1.5
-- | ```
toRem :: FontSize -> Number
toRem (FontSize s) = s / 16.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // type // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minor second type scale step (1.067x)
-- |
-- | Very subtle size increase, used for fine distinctions.
minor :: FontSize -> FontSize
minor = scale 1.067

-- | Major second type scale step (1.125x)
-- |
-- | Standard step for type hierarchies.
major :: FontSize -> FontSize
major = scale 1.125

-- | Heading 1 size (32px)
heading1 :: FontSize
heading1 = FontSize 32.0

-- | Heading 2 size (24px)
heading2 :: FontSize
heading2 = FontSize 24.0

-- | Heading 3 size (20px)
heading3 :: FontSize
heading3 = FontSize 20.0

-- | Body text size (16px)
body :: FontSize
body = FontSize 16.0

-- | Caption/small text size (12px)
caption :: FontSize
caption = FontSize 12.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if font size is readable for body text (14-20px)
-- |
-- | This is the recommended range for extended reading:
-- | ```purescript
-- | isReadable browserDefault  -- true (16px)
-- | isReadable caption         -- false (12px)
-- | isReadable heading1        -- false (32px)
-- | ```
isReadable :: FontSize -> Boolean
isReadable (FontSize s) = s >= 14.0 && s <= 20.0

-- | Check if font size is compact (10-14px)
-- |
-- | Small text for data-dense interfaces:
-- | ```purescript
-- | isCompact caption      -- true (12px)
-- | isCompact browserDefault  -- false (16px)
-- | ```
isCompact :: FontSize -> Boolean
isCompact (FontSize s) = s >= 10.0 && s < 14.0

-- | Check if font size is display (24-48px)
-- |
-- | Large text for headings and emphasis:
-- | ```purescript
-- | isDisplay heading1  -- true (32px)
-- | isDisplay heading2  -- true (24px)
-- | isDisplay body      -- false (16px)
-- | ```
isDisplay :: FontSize -> Boolean
isDisplay (FontSize s) = s >= 24.0 && s <= 48.0

-- | Check if font size is hero (> 48px)
-- |
-- | Extra large text for hero sections and dramatic impact:
-- | ```purescript
-- | isHero (fontSize 72.0)  -- true
-- | isHero heading1         -- false (32px)
-- | ```
isHero :: FontSize -> Boolean
isHero (FontSize s) = s > 48.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FontSize -> Number
unwrap (FontSize s) = s

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS font-size value
toLegacyCss :: FontSize -> String
toLegacyCss (FontSize s) = show s <> "px"

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 1.0 1000.0 "fontSize" "Font size in CSS pixels"
