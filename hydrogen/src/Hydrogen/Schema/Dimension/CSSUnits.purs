-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // dimension // cssunits
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Additional CSS dimension units.
-- |
-- | ## Cap Height Unit
-- | - cap: Height of capital letters in current font
-- |
-- | ## Ideograph Width
-- | - ic: Width of CJK water ideograph (水)
-- |
-- | ## Line Height Units
-- | - lh: Line height of the element
-- | - rlh: Line height of the root element

module Hydrogen.Schema.Dimension.CSSUnits
  ( -- * Cap Height
    Cap(..)
  , cap
  , unwrapCap
  , capAtLeast
  
  -- * Ideograph Width
  , Ic(..)
  , ic
  , unwrapIc
  , icAtLeast
  
  -- * Line Height
  , Lh(..)
  , lh
  , unwrapLh
  , lhAtLeast
  
  , Rlh(..)
  , rlh
  , unwrapRlh
  , rlhAtLeast
  
  -- * Gradians (angle)
  , Gradian(..)
  , gradian
  , unwrapGradian
  , gradianBounds
  , gradianToDegrees
  , degreesToGradian
  , gradianAtLeast
  
  -- * Turns (angle)
  , Turn(..)
  , turn
  , unwrapTurn
  , turnBounds
  , turnToDegrees
  , degreesToTurn
  , turnAtLeast
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (*)
  , (/)
  , (-)
  , (+)
  , (<)
  , (>=)
  , max
  )

import Data.Number (floor)
import Hydrogen.Schema.Bounded as Bounded

-- | Wrap a number to a range [minVal, maxVal).
wrapNumber :: Number -> Number -> Number -> Number
wrapNumber minVal maxVal n =
  let range = maxVal - minVal
      normalized = n - minVal
      wrapped = modFloat normalized range
      adjusted = if wrapped < 0.0 then wrapped + range else wrapped
  in adjusted + minVal

-- | Floating-point modulo.
modFloat :: Number -> Number -> Number
modFloat x y = x - y * floor (x / y)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // cap height
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cap - cap height unit.
-- | The height of capital letters in the current font.
newtype Cap = Cap Number

derive instance eqCap :: Eq Cap
derive instance ordCap :: Ord Cap

instance showCap :: Show Cap where
  show (Cap c) = show c <> "cap"

-- | Construct a cap value.
cap :: Number -> Cap
cap c = Cap (max 0.0 c)

-- | Unwrap cap.
unwrapCap :: Cap -> Number
unwrapCap (Cap c) = c

-- | Check if cap height meets minimum threshold.
capAtLeast :: Number -> Cap -> Boolean
capAtLeast threshold (Cap c) = c >= threshold

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // ideograph width
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ic - ideograph width unit.
-- | The width of the CJK water ideograph (水) in the current font.
-- | Used for CJK typographic layouts.
newtype Ic = Ic Number

derive instance eqIc :: Eq Ic
derive instance ordIc :: Ord Ic

instance showIc :: Show Ic where
  show (Ic i) = show i <> "ic"

-- | Construct an ic value.
ic :: Number -> Ic
ic i = Ic (max 0.0 i)

-- | Unwrap ic.
unwrapIc :: Ic -> Number
unwrapIc (Ic i) = i

-- | Check if ideograph width meets minimum threshold.
icAtLeast :: Number -> Ic -> Boolean
icAtLeast threshold (Ic i) = i >= threshold

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // line height
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lh - line height of the element.
newtype Lh = Lh Number

derive instance eqLh :: Eq Lh
derive instance ordLh :: Ord Lh

instance showLh :: Show Lh where
  show (Lh l) = show l <> "lh"

-- | Construct an lh value.
lh :: Number -> Lh
lh l = Lh (max 0.0 l)

-- | Unwrap lh.
unwrapLh :: Lh -> Number
unwrapLh (Lh l) = l

-- | Check if line height meets minimum threshold.
lhAtLeast :: Number -> Lh -> Boolean
lhAtLeast threshold (Lh l) = l >= threshold

-- | Rlh - line height of the root element.
newtype Rlh = Rlh Number

derive instance eqRlh :: Eq Rlh
derive instance ordRlh :: Ord Rlh

instance showRlh :: Show Rlh where
  show (Rlh r) = show r <> "rlh"

-- | Construct an rlh value.
rlh :: Number -> Rlh
rlh r = Rlh (max 0.0 r)

-- | Unwrap rlh.
unwrapRlh :: Rlh -> Number
unwrapRlh (Rlh r) = r

-- | Check if root line height meets minimum threshold.
rlhAtLeast :: Number -> Rlh -> Boolean
rlhAtLeast threshold (Rlh r) = r >= threshold

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // gradian
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gradian - angle unit where 400 gradians = full circle.
-- | Used in surveying and some European countries.
newtype Gradian = Gradian Number

derive instance eqGradian :: Eq Gradian
derive instance ordGradian :: Ord Gradian

instance showGradian :: Show Gradian where
  show (Gradian g) = show g <> "grad"

-- | Bounds for gradian (wraps at 400).
gradianBounds :: Bounded.NumberBounds
gradianBounds = Bounded.numberBounds 0.0 400.0 "Gradian" "Angle in gradians (wraps at 400)"

-- | Construct a gradian value (wraps).
gradian :: Number -> Gradian
gradian g = Gradian (wrapNumber 0.0 400.0 g)

-- | Unwrap gradian.
unwrapGradian :: Gradian -> Number
unwrapGradian (Gradian g) = g

-- | Convert gradian to degrees.
gradianToDegrees :: Gradian -> Number
gradianToDegrees (Gradian g) = g * 0.9  -- 360/400 = 0.9

-- | Convert degrees to gradian.
degreesToGradian :: Number -> Gradian
degreesToGradian d = gradian (d / 0.9)

-- | Check if gradian angle is at least threshold.
gradianAtLeast :: Number -> Gradian -> Boolean
gradianAtLeast threshold (Gradian g) = g >= threshold

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // turn
-- ═════════════════════════════════════════════════════════════════════════════

-- | Turn - angle unit where 1 turn = 360 degrees.
newtype Turn = Turn Number

derive instance eqTurn :: Eq Turn
derive instance ordTurn :: Ord Turn

instance showTurn :: Show Turn where
  show (Turn t) = show t <> "turn"

-- | Bounds for turn (wraps at 1.0).
turnBounds :: Bounded.NumberBounds
turnBounds = Bounded.numberBounds 0.0 1.0 "Turn" "Angle in turns (wraps at 1.0)"

-- | Construct a turn value (wraps).
turn :: Number -> Turn
turn t = Turn (wrapNumber 0.0 1.0 t)

-- | Unwrap turn.
unwrapTurn :: Turn -> Number
unwrapTurn (Turn t) = t

-- | Convert turn to degrees.
turnToDegrees :: Turn -> Number
turnToDegrees (Turn t) = t * 360.0

-- | Convert degrees to turn.
degreesToTurn :: Number -> Turn
degreesToTurn d = turn (d / 360.0)

-- | Check if turn angle is at least threshold.
turnAtLeast :: Number -> Turn -> Boolean
turnAtLeast threshold (Turn t) = t >= threshold
