-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // dimension // flex
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Flex unit - CSS Grid and Flexbox fraction unit.
-- |
-- | The fr unit represents a fraction of available space in a grid container.
-- | It's the only unit that can be used with other units in grid templates.
-- |
-- | ## Usage
-- |
-- | - 1fr = one fraction of available space
-- | - 2fr = twice as much space as 1fr
-- | - 1fr 2fr 1fr = 25% / 50% / 25% distribution
-- |
-- | ## Type Safety
-- |
-- | Fr is distinct from Number - it can only be used in grid/flex contexts.
-- |
-- | ## Dependencies
-- | - Prelude

module Hydrogen.Schema.Dimension.Flex
  ( -- * Flex Fraction
    Fr(Fr)
  , fr
  , frs
  , unwrapFr
  
  -- * Common Flex Values
  , flexEqual
  , flexDouble
  , flexHalf
  , flexThird
  , flexQuarter
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , show
  , (<>)
  , (<<<)
  )

import Data.Array ((..))
import Data.Int (toNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // fr // flex
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flex fraction unit - a portion of available space.
-- |
-- | Used in CSS Grid and Flexbox. 1fr represents one share of the
-- | available space. Combined with other fr values to create proportional layouts.
newtype Fr = Fr Number

derive instance eqFr :: Eq Fr
derive instance ordFr :: Ord Fr

instance showFr :: Show Fr where
  show (Fr v) = show v <> "fr"

-- | Create Fr from Number
fr :: Number -> Fr
fr = Fr

-- | Create Fr (plural alias)
frs :: Number -> Fr
frs = fr

-- | Unwrap Fr to raw Number
unwrapFr :: Fr -> Number
unwrapFr (Fr v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common // flex
-- ═════════════════════════════════════════════════════════════════════════════

-- | Equal distribution (1fr 1fr 1fr)
flexEqual :: Int -> Array Fr
flexEqual n = map (fr <<< toNumber) (1 .. n)

-- | Double the first item (2fr 1fr)
flexDouble :: Array Fr
flexDouble = [fr 2.0, fr 1.0]

-- | Half the first item (1fr 2fr)
flexHalf :: Array Fr
flexHalf = [fr 1.0, fr 2.0]

-- | Three equal columns (1fr 1fr 1fr)
flexThird :: Array Fr
flexThird = flexEqual 3

-- | Four equal columns (1fr 1fr 1fr 1fr)
flexQuarter :: Array Fr
flexQuarter = flexEqual 4
