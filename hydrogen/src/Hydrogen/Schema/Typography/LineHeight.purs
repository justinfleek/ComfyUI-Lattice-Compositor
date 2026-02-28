-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // typography // line-height
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LineHeight - vertical rhythm and text leading.
-- |
-- | A unitless ratio relative to font size:
-- | - **1.0**: Lines touch (no leading) - display text only
-- | - **1.2-1.3**: Tight - headings, short bursts
-- | - **1.4-1.5**: Normal - balanced readability
-- | - **1.6-1.8**: Relaxed - body text, long-form reading
-- | - **2.0+**: Loose - special effects, dramatic spacing
-- |
-- | Line height = font-size × ratio. For 16px text at 1.5 ratio = 24px lines.
-- |
-- | Professional typographers call the space between lines "leading" (rhymes
-- | with "bedding"), from the lead strips inserted between lines of metal type.

module Hydrogen.Schema.Typography.LineHeight
  ( LineHeight
  , lineHeight
  , unsafeLineHeight
  , unwrap
  , toPixels
  , toLegacyCss
  , bounds
  -- Common ratios
  , solid
  , tight
  , normal
  , relaxed
  , loose
  -- Operations
  , blend
  , lerp
  , scale
  , add
  , subtract
  , toNumber
  -- Predicates
  , isSolid
  , isTight
  , isNormal
  , isRelaxed
  , isLoose
  , atLeast
  , lessThan
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  )

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Typography.FontSize (FontSize)
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // line height
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line height as unitless ratio (positive Number)
-- |
-- | This is a multiplier of the font size. Using unitless values ensures
-- | line height scales proportionally when font size changes.
newtype LineHeight = LineHeight Number

derive instance eqLineHeight :: Eq LineHeight
derive instance ordLineHeight :: Ord LineHeight

instance showLineHeight :: Show LineHeight where
  show (LineHeight h) = show h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a line height, clamping to valid range
-- |
-- | Minimum is 0.5 (prevents text overlap in most cases).
-- | Maximum is 5.0 (practical limit for display).
lineHeight :: Number -> LineHeight
lineHeight n = LineHeight (Bounded.clampNumber 0.5 5.0 n)

-- | Create a line height without clamping
-- |
-- | Use only when you know the value is valid.
unsafeLineHeight :: Number -> LineHeight
unsafeLineHeight = LineHeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common ratios
-- ═════════════════════════════════════════════════════════════════════════════

-- | Solid line height (1.0)
-- |
-- | No leading - lines touch. Use only for single-line display text where
-- | vertical space is at a premium.
solid :: LineHeight
solid = LineHeight 1.0

-- | Tight line height (1.25)
-- |
-- | Minimal leading for headings and short text bursts. Creates visual
-- | density and urgency.
tight :: LineHeight
tight = LineHeight 1.25

-- | Normal line height (1.5)
-- |
-- | Balanced readability for most content. Good default for body text
-- | in interfaces.
normal :: LineHeight
normal = LineHeight 1.5

-- | Relaxed line height (1.75)
-- |
-- | Enhanced readability for long-form content. Reduces eye strain during
-- | extended reading sessions.
relaxed :: LineHeight
relaxed = LineHeight 1.75

-- | Loose line height (2.0)
-- |
-- | Dramatic vertical spacing for special effects or when content needs
-- | room to breathe.
loose :: LineHeight
loose = LineHeight 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two line heights with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation for animated typography:
-- | ```purescript
-- | blend 0.5 tight relaxed  -- LineHeight 1.5 (midpoint)
-- | ```
blend :: Number -> LineHeight -> LineHeight -> LineHeight
blend weight (LineHeight a) (LineHeight b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in lineHeight (a * (1.0 - w) + b * w)

-- | Linear interpolation (standard lerp signature)
lerp :: LineHeight -> LineHeight -> Number -> LineHeight
lerp from to t = blend t from to

-- | Scale line height by a factor
-- |
-- | Useful for responsive adjustments:
-- | ```purescript
-- | scale 1.2 normal  -- LineHeight 1.8
-- | ```
scale :: Number -> LineHeight -> LineHeight
scale factor (LineHeight h) = lineHeight (h * factor)

-- | Add to line height (clamped)
add :: Number -> LineHeight -> LineHeight
add amount (LineHeight h) = lineHeight (h + amount)

-- | Subtract from line height (clamped)
subtract :: Number -> LineHeight -> LineHeight
subtract amount (LineHeight h) = lineHeight (h - amount)

-- | Convert to Number for calculations
toNumber :: LineHeight -> Number
toNumber (LineHeight h) = h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if line height is solid (no leading, ~1.0)
-- |
-- | Solid line heights should only be used for single-line display text:
-- | ```purescript
-- | isSolid solid  -- true
-- | isSolid tight  -- false
-- | ```
isSolid :: LineHeight -> Boolean
isSolid (LineHeight h) = h <= 1.1

-- | Check if line height is tight (1.1-1.35)
-- |
-- | Tight leading for headings and compact text:
-- | ```purescript
-- | isTight tight  -- true (1.25)
-- | isTight normal -- false (1.5)
-- | ```
isTight :: LineHeight -> Boolean
isTight (LineHeight h) = h > 1.1 && h <= 1.35

-- | Check if line height is normal (1.35-1.6)
-- |
-- | Standard leading for body text:
-- | ```purescript
-- | isNormal normal  -- true (1.5)
-- | isNormal tight   -- false (1.25)
-- | ```
isNormal :: LineHeight -> Boolean
isNormal (LineHeight h) = h > 1.35 && h <= 1.6

-- | Check if line height is relaxed (1.6-1.9)
-- |
-- | Generous leading for long-form reading:
-- | ```purescript
-- | isRelaxed relaxed  -- true (1.75)
-- | isRelaxed normal   -- false (1.5)
-- | ```
isRelaxed :: LineHeight -> Boolean
isRelaxed (LineHeight h) = h > 1.6 && h <= 1.9

-- | Check if line height is loose (> 1.9)
-- |
-- | Extra-generous leading for dramatic effect:
-- | ```purescript
-- | isLoose loose   -- true (2.0)
-- | isLoose relaxed -- false (1.75)
-- | ```
isLoose :: LineHeight -> Boolean
isLoose (LineHeight h) = h > 1.9

-- | Check if line height is at least a given ratio
-- |
-- | Useful for accessibility checks (WCAG recommends >= 1.5 for body text):
-- | ```purescript
-- | atLeast 1.5 normal   -- true (1.5 >= 1.5)
-- | atLeast 1.5 tight    -- false (1.25 < 1.5)
-- | ```
atLeast :: Number -> LineHeight -> Boolean
atLeast threshold (LineHeight h) = h >= threshold

-- | Check if line height is less than a given ratio
-- |
-- | Useful for detecting overly tight leading:
-- | ```purescript
-- | lessThan 1.2 solid   -- true (1.0 < 1.2)
-- | lessThan 1.2 tight   -- false (1.25 >= 1.2)
-- | ```
lessThan :: Number -> LineHeight -> Boolean
lessThan threshold (LineHeight h) = h < threshold

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: LineHeight -> Number
unwrap (LineHeight h) = h

-- | Calculate actual pixel height for a given font size
toPixels :: FontSize -> LineHeight -> Number
toPixels fs (LineHeight ratio) = FontSize.unwrap fs * ratio

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS line-height value (unitless)
toLegacyCss :: LineHeight -> String
toLegacyCss (LineHeight h) = show h

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.5 5.0 "lineHeight" "Line height as unitless ratio"
