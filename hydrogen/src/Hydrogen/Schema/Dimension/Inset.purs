-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // dimension // inset
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Inset — Top, Right, Bottom, Left edge values.
-- |
-- | **WHY INSET?**
-- | Inset represents values for all four edges of a rectangular region:
-- | - Top edge
-- | - Right edge  
-- | - Bottom edge
-- | - Left edge
-- |
-- | Follows CSS box model conventions (clockwise from top).
-- |
-- | **Use cases:**
-- | - Padding (inset from container edges)
-- | - Margin (outset from element edges)
-- | - Border width
-- | - Safe area insets (device notches, home indicators)
-- | - Scroll padding
-- |
-- | **Also includes:**
-- | - `InsetXY` — Simplified horizontal/vertical only

module Hydrogen.Schema.Dimension.Inset
  ( -- * Types
    Inset(Inset)
  , InsetXY(InsetXY)
  
  -- * Constructors (Inset)
  , inset
  , insetFromRecord
  , insetAll
  , insetNone
  , insetSymmetric
  , insetTop
  , insetRight
  , insetBottom
  , insetLeft
  
  -- * Constructors (InsetXY)
  , insetXY
  , insetXYFromRecord
  , insetXYAll
  , insetXYNone
  
  -- * Accessors (Inset)
  , top
  , right
  , bottom
  , left
  , toRecord
  , horizontal
  , vertical
  
  -- * Accessors (InsetXY)
  , insetX
  , insetY
  , toRecordXY
  
  -- * Operations (Inset)
  , add
  , scale
  , max
  , min
  , lerp
  , totalHorizontal
  , totalVertical
  
  -- * Conversions
  , toInsetXY
  , fromInsetXY
  , expandInset
  , contractInset
  
  -- * Predicates
  , isZero
  , isUniform
  , isSymmetric
  , isEqual
  
  -- * CSS Output
  , toCss
  , toCssXY
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , (==)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // inset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Inset with top, right, bottom, left values.
-- |
-- | Follows CSS convention: clockwise from top.
-- | Values are typically non-negative but can be negative for outsets.
data Inset = Inset Number Number Number Number

derive instance eqInset :: Eq Inset
derive instance ordInset :: Ord Inset

instance showInset :: Show Inset where
  show (Inset t r b l) = 
    "Inset(" <> show t <> ", " <> show r <> ", " <> show b <> ", " <> show l <> ")"

-- | Simplified inset with just horizontal and vertical values.
-- |
-- | Symmetric: same value for left/right (horizontal) and top/bottom (vertical).
data InsetXY = InsetXY Number Number

derive instance eqInsetXY :: Eq InsetXY
derive instance ordInsetXY :: Ord InsetXY

instance showInsetXY :: Show InsetXY where
  show (InsetXY h v) = "InsetXY(" <> show h <> ", " <> show v <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // constructors // inset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an Inset with all four values.
-- |
-- | Order: top, right, bottom, left (CSS convention).
-- |
-- | ```purescript
-- | inset 10.0 20.0 10.0 20.0  -- 10px vertical, 20px horizontal
-- | ```
inset :: Number -> Number -> Number -> Number -> Inset
inset = Inset

-- | Create from a record.
insetFromRecord :: { top :: Number, right :: Number, bottom :: Number, left :: Number } -> Inset
insetFromRecord { top: t, right: r, bottom: b, left: l } = Inset t r b l

-- | Create uniform inset (same value all sides).
-- |
-- | ```purescript
-- | insetAll 16.0  -- 16px padding on all sides
-- | ```
insetAll :: Number -> Inset
insetAll n = Inset n n n n

-- | Zero inset.
insetNone :: Inset
insetNone = Inset 0.0 0.0 0.0 0.0

-- | Create symmetric inset (horizontal and vertical).
-- |
-- | ```purescript
-- | insetSymmetric 20.0 10.0  -- 20px left/right, 10px top/bottom
-- | ```
insetSymmetric :: Number -> Number -> Inset
insetSymmetric h v = Inset v h v h

-- | Create inset with only top value.
insetTop :: Number -> Inset
insetTop t = Inset t 0.0 0.0 0.0

-- | Create inset with only right value.
insetRight :: Number -> Inset
insetRight r = Inset 0.0 r 0.0 0.0

-- | Create inset with only bottom value.
insetBottom :: Number -> Inset
insetBottom b = Inset 0.0 0.0 b 0.0

-- | Create inset with only left value.
insetLeft :: Number -> Inset
insetLeft l = Inset 0.0 0.0 0.0 l

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // constructors // insetxy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an InsetXY with horizontal and vertical values.
-- |
-- | ```purescript
-- | insetXY 20.0 10.0  -- 20px horizontal (left/right), 10px vertical (top/bottom)
-- | ```
insetXY :: Number -> Number -> InsetXY
insetXY = InsetXY

-- | Create from a record.
insetXYFromRecord :: { horizontal :: Number, vertical :: Number } -> InsetXY
insetXYFromRecord { horizontal: h, vertical: v } = InsetXY h v

-- | Create uniform InsetXY (same value both directions).
insetXYAll :: Number -> InsetXY
insetXYAll n = InsetXY n n

-- | Zero InsetXY.
insetXYNone :: InsetXY
insetXYNone = InsetXY 0.0 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // accessors // inset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get top value.
top :: Inset -> Number
top (Inset t _ _ _) = t

-- | Get right value.
right :: Inset -> Number
right (Inset _ r _ _) = r

-- | Get bottom value.
bottom :: Inset -> Number
bottom (Inset _ _ b _) = b

-- | Get left value.
left :: Inset -> Number
left (Inset _ _ _ l) = l

-- | Convert to record.
toRecord :: Inset -> { top :: Number, right :: Number, bottom :: Number, left :: Number }
toRecord (Inset t r b l) = { top: t, right: r, bottom: b, left: l }

-- | Get horizontal component (average of left and right).
horizontal :: Inset -> Number
horizontal (Inset _ r _ l) = (l + r) / 2.0

-- | Get vertical component (average of top and bottom).
vertical :: Inset -> Number
vertical (Inset t _ b _) = (t + b) / 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // accessors // insetxy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get horizontal value.
insetX :: InsetXY -> Number
insetX (InsetXY h _) = h

-- | Get vertical value.
insetY :: InsetXY -> Number
insetY (InsetXY _ v) = v

-- | Convert to record.
toRecordXY :: InsetXY -> { horizontal :: Number, vertical :: Number }
toRecordXY (InsetXY h v) = { horizontal: h, vertical: v }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // operations // inset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two insets (component-wise).
add :: Inset -> Inset -> Inset
add (Inset t1 r1 b1 l1) (Inset t2 r2 b2 l2) =
  Inset (t1 + t2) (r1 + r2) (b1 + b2) (l1 + l2)

-- | Scale all values by a factor.
scale :: Number -> Inset -> Inset
scale factor (Inset t r b l) =
  Inset (t * factor) (r * factor) (b * factor) (l * factor)

-- | Component-wise maximum.
max :: Inset -> Inset -> Inset
max (Inset t1 r1 b1 l1) (Inset t2 r2 b2 l2) =
  Inset (maxNum t1 t2) (maxNum r1 r2) (maxNum b1 b2) (maxNum l1 l2)

-- | Component-wise minimum.
min :: Inset -> Inset -> Inset
min (Inset t1 r1 b1 l1) (Inset t2 r2 b2 l2) =
  Inset (minNum t1 t2) (minNum r1 r2) (minNum b1 b2) (minNum l1 l2)

-- | Linear interpolation between two insets.
lerp :: Inset -> Inset -> Number -> Inset
lerp (Inset t1 r1 b1 l1) (Inset t2 r2 b2 l2) t =
  let t' = clamp01 t
  in Inset
    (t1 + (t2 - t1) * t')
    (r1 + (r2 - r1) * t')
    (b1 + (b2 - b1) * t')
    (l1 + (l2 - l1) * t')

-- | Total horizontal inset (left + right).
totalHorizontal :: Inset -> Number
totalHorizontal (Inset _ r _ l) = l + r

-- | Total vertical inset (top + bottom).
totalVertical :: Inset -> Number
totalVertical (Inset t _ b _) = t + b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Inset to InsetXY (uses left for horizontal, top for vertical).
-- |
-- | Warning: loses information if sides aren't symmetric.
toInsetXY :: Inset -> InsetXY
toInsetXY (Inset t _ _ l) = InsetXY l t

-- | Convert InsetXY to symmetric Inset.
fromInsetXY :: InsetXY -> Inset
fromInsetXY (InsetXY h v) = Inset v h v h

-- | Expand an inset by adding an amount to all sides.
expandInset :: Number -> Inset -> Inset
expandInset amount (Inset t r b l) =
  Inset (t + amount) (r + amount) (b + amount) (l + amount)

-- | Contract an inset by subtracting an amount from all sides.
-- |
-- | Values can become negative.
contractInset :: Number -> Inset -> Inset
contractInset amount (Inset t r b l) =
  Inset (t - amount) (r - amount) (b - amount) (l - amount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if all values are zero.
isZero :: Inset -> Boolean
isZero (Inset t r b l) = t == 0.0 && r == 0.0 && b == 0.0 && l == 0.0

-- | Check if all values are equal.
isUniform :: Inset -> Boolean
isUniform (Inset t r b l) = t == r && r == b && b == l

-- | Check if horizontally and vertically symmetric.
-- |
-- | Symmetric means: top == bottom AND left == right.
isSymmetric :: Inset -> Boolean
isSymmetric (Inset t r b l) = t == b && l == r

-- | Check if two insets are equal.
isEqual :: Inset -> Inset -> Boolean
isEqual (Inset t1 r1 b1 l1) (Inset t2 r2 b2 l2) =
  t1 == t2 && r1 == r2 && b1 == b2 && l1 == l2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS inset value.
-- |
-- | Uses shortest form possible:
-- | - 1 value if uniform
-- | - 2 values if vertical/horizontal symmetric
-- | - 4 values otherwise
toCss :: Inset -> String
toCss i@(Inset t r b l)
  | isUniform i = show t <> "px"
  | isSymmetric i = show t <> "px " <> show r <> "px"
  | otherwise = show t <> "px " <> show r <> "px " <> show b <> "px " <> show l <> "px"

-- | Convert InsetXY to CSS.
toCssXY :: InsetXY -> String
toCssXY (InsetXY h v) = show v <> "px " <> show h <> "px"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum of two numbers
maxNum :: Number -> Number -> Number
maxNum a b
  | a >= b = a
  | otherwise = b

-- | Minimum of two numbers
minNum :: Number -> Number -> Number
minNum a b
  | a <= b = a
  | otherwise = b

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n <= 1.0 = n
  | otherwise = 1.0
